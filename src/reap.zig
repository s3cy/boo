//! Full-tree teardown for a session's process tree.
//!
//! `boo kill` must end everything the session started, not just the
//! shell. The shell is the session's PTY child; it ran setsid(), so it
//! leads its own session and process group (child_pid == pgid). Signaling
//! only that pid, or even only its process group, leaves behind
//! grandchildren that ignore the signal, were placed in their own process
//! group by the shell's job control, or were backgrounded, so they keep
//! holding ports and files after the session is gone.
//!
//! terminateTree() snapshots the whole descendant tree while it is still
//! intact (before anything is signaled: once the leader dies its children
//! reparent to init and the parent links vanish), hangs up the leader's
//! process group, SIGTERMs every descendant by pid, waits a bounded grace
//! for them to exit, then SIGKILLs whatever remains. Every bare-pid signal
//! is guarded by the process start time recorded at snapshot, so a pid
//! reused between the snapshot and a later SIGKILL is never hit.
//!
//! A descendant that double-forked into its own session and reparented to
//! init before the kill cannot be discovered from the leader and is not
//! reached; that is the same caveat tmux and screen live with.

const std = @import("std");
const builtin = @import("builtin");
const posix = std.posix;

const log = std.log.scoped(.reap);

/// A descendant captured at snapshot time. `start` is the process start
/// time; comparing it before each signal distinguishes this process from a
/// later one that reuses the pid. `start_unknown` means the platform could
/// not report it, so the reuse guard is skipped (best effort).
const Proc = struct {
    pid: posix.pid_t,
    start: u64,
};

/// Sentinel for "start time unavailable". A real start time is normalized
/// away from this value (see normalizeStart).
const start_unknown: u64 = 0;

/// Upper bound on descendants enumerated, so a fork bomb cannot make
/// teardown allocate or scan without limit.
const max_procs: usize = 16 * 1024;

/// How long to wait after SIGTERM before escalating to SIGKILL, polled in
/// small slices so teardown returns as soon as the tree drains.
const grace_ms: i64 = 2000;
const poll_slice_ms: u64 = 20;

// Run the darwin layout asserts on every target (matching cwd.zig), so a
// struct drift fails the build loudly rather than only on macOS. This
// references a type, so it does not pull the libproc externs into a
// non-macOS link.
comptime {
    _ = darwin.proc_bsdinfo;
}

/// Tear down the entire process tree rooted at `leader` (the session's PTY
/// child, a process-group leader via setsid()). `leader` must be the
/// caller's direct child and still alive, so it can be reaped and its
/// descendants enumerated before anything is signaled. Best effort: any
/// step that cannot run is skipped rather than failing teardown.
pub fn terminateTree(alloc: std.mem.Allocator, leader: posix.pid_t) void {
    var procs: std.ArrayList(Proc) = .empty;
    defer procs.deinit(alloc);
    collect(alloc, leader, &procs);

    // Hang up the leader's process group first: the polite terminal-closed
    // signal a shell forwards to its own jobs. child_pid == pgid, so
    // -leader targets the shell and everything still in its group.
    posix.kill(-leader, posix.SIG.HUP) catch {};

    // SIGTERM every descendant by pid. This reaches foreground jobs the
    // shell placed in their own process groups, which the group signal
    // above cannot.
    for (procs.items) |p| signalProc(p, posix.SIG.TERM);

    // Wait for the tree to drain, reaping the leader as it exits, and
    // return as soon as nothing we started survives.
    const deadline = std.time.milliTimestamp() + grace_ms;
    while (std.time.milliTimestamp() < deadline) {
        reapChildren();
        if (!anyAlive(procs.items)) return;
        std.Thread.sleep(poll_slice_ms * std.time.ns_per_ms);
    }

    // Escalate: SIGKILL whatever is still the same process we snapshotted.
    for (procs.items) |p| signalProc(p, posix.SIG.KILL);
    reapChildren();
}

/// Reap any of our direct children that have exited (the leader). Orphaned
/// grandchildren reparent to init, which reaps them; this only clears our
/// own zombie so it stops counting as alive.
fn reapChildren() void {
    var status: c_int = undefined;
    while (std.c.waitpid(-1, &status, std.c.W.NOHANG) > 0) {}
}

/// Whether any snapshotted process is still alive and still itself (not a
/// zombie, and not a different process that reused the pid).
fn anyAlive(procs: []const Proc) bool {
    for (procs) |p| {
        const cur = startTimeIfAlive(p.pid) orelse continue;
        if (p.start == start_unknown or cur == p.start) return true;
    }
    return false;
}

/// Signal `p` only if it is still the process captured at snapshot time,
/// so a delayed SIGKILL never lands on an unrelated process that reused
/// the pid. A process that is already gone or a zombie is skipped.
fn signalProc(p: Proc, sig: u8) void {
    if (p.start != start_unknown) {
        const cur = startTimeIfAlive(p.pid) orelse return;
        if (cur != p.start) return;
    }
    posix.kill(p.pid, sig) catch {};
}

/// Snapshot the descendant tree of `leader` into `out`, including the
/// leader itself. The leader is always present so at least the shell is
/// torn down, even when enumeration fails or the platform is unsupported.
fn collect(alloc: std.mem.Allocator, leader: posix.pid_t, out: *std.ArrayList(Proc)) void {
    switch (builtin.os.tag) {
        .linux => collectLinux(alloc, leader, out) catch {},
        .macos, .ios, .tvos, .watchos, .visionos => collectDarwin(alloc, leader, out) catch {},
        else => {},
    }
    for (out.items) |p| if (p.pid == leader) return;
    out.append(alloc, .{
        .pid = leader,
        .start = startTimeIfAlive(leader) orelse start_unknown,
    }) catch {};
}

/// The process start time if `pid` names a live, non-zombie process, else
/// null. Used both to detect liveness and, compared against a recorded
/// value, to detect pid reuse.
fn startTimeIfAlive(pid: posix.pid_t) ?u64 {
    switch (builtin.os.tag) {
        .linux => {
            const st = readLinuxStat(pid) orelse return null;
            if (st.state == 'Z') return null; // zombie: effectively dead
            return st.start;
        },
        .macos, .ios, .tvos, .watchos, .visionos => return darwin.startTime(pid),
        else => return null,
    }
}

// -- Linux ----------------------------------------------------------------

const Stat = struct { ppid: posix.pid_t, state: u8, start: u64 };

/// Enumerate every process via /proc, then collect the transitive
/// descendants of `leader` by walking parent links to a fixpoint. The tree
/// must be built from a full snapshot because a child's /proc entry only
/// points up (to its parent), never down.
fn collectLinux(alloc: std.mem.Allocator, leader: posix.pid_t, out: *std.ArrayList(Proc)) !void {
    const Entry = struct { pid: posix.pid_t, ppid: posix.pid_t, start: u64 };
    var all: std.ArrayList(Entry) = .empty;
    defer all.deinit(alloc);

    var dir = try std.fs.openDirAbsolute("/proc", .{ .iterate = true });
    defer dir.close();
    var it = dir.iterate();
    while (try it.next()) |entry| {
        // Only numeric entries are processes; "self", "cpuinfo", etc. are
        // filtered out by the parse failing.
        const pid = std.fmt.parseInt(posix.pid_t, entry.name, 10) catch continue;
        const st = readLinuxStat(pid) orelse continue;
        try all.append(alloc, .{ .pid = pid, .ppid = st.ppid, .start = st.start });
        if (all.items.len >= max_procs) break;
    }

    // A process is in the tree when its parent is. Iterate until no new
    // members appear.
    var member: std.AutoHashMapUnmanaged(posix.pid_t, u64) = .empty;
    defer member.deinit(alloc);
    try member.put(alloc, leader, startTimeIfAlive(leader) orelse start_unknown);
    var changed = true;
    while (changed) {
        changed = false;
        for (all.items) |e| {
            if (member.contains(e.pid)) continue;
            if (member.contains(e.ppid)) {
                try member.put(alloc, e.pid, e.start);
                changed = true;
            }
        }
    }

    var mit = member.iterator();
    while (mit.next()) |e| {
        try out.append(alloc, .{ .pid = e.key_ptr.*, .start = e.value_ptr.* });
    }
}

fn readLinuxStat(pid: posix.pid_t) ?Stat {
    var path_buf: [64]u8 = undefined;
    const path = std.fmt.bufPrintZ(&path_buf, "/proc/{d}/stat", .{pid}) catch return null;
    var buf: [512]u8 = undefined;
    const content = readFileZ(path, &buf) orelse return null;
    return parseStat(content);
}

/// Parse ppid (field 4), state (field 3), and starttime (field 22) out of
/// a /proc/<pid>/stat line. The comm field (2) is parenthesized and may
/// itself contain spaces and ')', so scanning starts after the final ')'.
fn parseStat(content: []const u8) ?Stat {
    const rp = std.mem.lastIndexOfScalar(u8, content, ')') orelse return null;
    if (rp + 1 >= content.len) return null;
    var it = std.mem.tokenizeScalar(u8, content[rp + 1 ..], ' ');
    const state_tok = it.next() orelse return null; // field 3
    const ppid_tok = it.next() orelse return null; // field 4
    if (state_tok.len == 0) return null;
    const ppid = std.fmt.parseInt(posix.pid_t, ppid_tok, 10) catch return null;
    // We have consumed through field 4; count on to field 22 (starttime).
    var field: usize = 4;
    const start: u64 = while (it.next()) |tok| {
        field += 1;
        if (field == 22) break std.fmt.parseInt(u64, tok, 10) catch return null;
    } else return null;
    return .{ .ppid = ppid, .state = state_tok[0], .start = normalizeStart(start) };
}

fn readFileZ(path: [*:0]const u8, buf: []u8) ?[]u8 {
    const fd = posix.openZ(path, .{ .ACCMODE = .RDONLY }, 0) catch return null;
    defer posix.close(fd);
    var total: usize = 0;
    while (total < buf.len) {
        const n = posix.read(fd, buf[total..]) catch return null;
        if (n == 0) break;
        total += n;
    }
    return buf[0..total];
}

/// Map a real start time of 0 to 1 so it never collides with the
/// start_unknown sentinel. A start time of 0 is not observed for the
/// processes a session spawns.
fn normalizeStart(s: u64) u64 {
    return if (s == start_unknown) 1 else s;
}

// -- macOS ----------------------------------------------------------------

/// BFS the descendant tree via proc_listchildpids, which (unlike /proc)
/// enumerates a process's children directly.
fn collectDarwin(alloc: std.mem.Allocator, leader: posix.pid_t, out: *std.ArrayList(Proc)) !void {
    var seen: std.AutoHashMapUnmanaged(posix.pid_t, void) = .empty;
    defer seen.deinit(alloc);
    var queue: std.ArrayList(posix.pid_t) = .empty;
    defer queue.deinit(alloc);

    try seen.put(alloc, leader, {});
    try out.append(alloc, .{ .pid = leader, .start = startTimeIfAlive(leader) orelse start_unknown });
    try queue.append(alloc, leader);

    var kids: [1024]c_int = undefined;
    var head: usize = 0;
    while (head < queue.items.len) : (head += 1) {
        const parent = queue.items[head];
        const bytes = darwin.proc_listchildpids(parent, &kids, @sizeOf(@TypeOf(kids)));
        if (bytes <= 0) continue;
        const count = @min(@as(usize, @intCast(bytes)) / @sizeOf(c_int), kids.len);
        for (kids[0..count]) |child_c| {
            if (child_c <= 0) continue;
            const child: posix.pid_t = @intCast(child_c);
            if (seen.contains(child)) continue;
            try seen.put(alloc, child, {});
            const start = startTimeIfAlive(child) orelse continue; // already gone
            try out.append(alloc, .{ .pid = child, .start = start });
            if (out.items.len >= max_procs) return;
            try queue.append(alloc, child);
        }
    }
}

/// Minimal mirror of `<sys/proc_info.h>` for PROC_PIDTBSDINFO. proc_pidinfo
/// rejects any buffer whose size differs from `struct proc_bsdinfo`, so the
/// whole layout is reproduced and its size locked at comptime.
const darwin = struct {
    const PROC_PIDTBSDINFO: c_int = 3;
    const SZOMB: u32 = 5; // <sys/proc.h>: process is a zombie
    const MAXCOMLEN = 16;

    const proc_bsdinfo = extern struct {
        pbi_flags: u32,
        pbi_status: u32,
        pbi_xstatus: u32,
        pbi_pid: u32,
        pbi_ppid: u32,
        pbi_uid: u32,
        pbi_gid: u32,
        pbi_ruid: u32,
        pbi_rgid: u32,
        pbi_svuid: u32,
        pbi_svgid: u32,
        rfu_1: u32,
        pbi_comm: [MAXCOMLEN]u8,
        pbi_name: [2 * MAXCOMLEN]u8,
        pbi_nfiles: u32,
        pbi_pgid: u32,
        pbi_pjobc: u32,
        e_tdev: u32,
        e_tpgid: u32,
        pbi_nice: i32,
        pbi_start_tvsec: u64,
        pbi_start_tvusec: u64,
    };

    comptime {
        // Verified against macOS <sys/proc_info.h>; the syscall rejects any
        // other size, so a layout drift must fail the build loudly.
        std.debug.assert(@sizeOf(proc_bsdinfo) == 136);
        std.debug.assert(@offsetOf(proc_bsdinfo, "pbi_status") == 4);
        std.debug.assert(@offsetOf(proc_bsdinfo, "pbi_start_tvsec") == 120);
    }

    extern "c" fn proc_pidinfo(
        pid: c_int,
        flavor: c_int,
        arg: u64,
        buffer: ?*anyopaque,
        buffersize: c_int,
    ) c_int;

    extern "c" fn proc_listchildpids(ppid: c_int, buffer: ?*anyopaque, buffersize: c_int) c_int;

    fn startTime(pid: posix.pid_t) ?u64 {
        var bi: proc_bsdinfo = undefined;
        const size: c_int = @sizeOf(proc_bsdinfo);
        if (proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &bi, size) != size) return null;
        if (bi.pbi_status == SZOMB) return null; // zombie: effectively dead
        return normalizeStart(bi.pbi_start_tvsec *% 1_000_000 +% bi.pbi_start_tvusec);
    }
};

test "parseStat reads ppid, state, and starttime past a tricky comm" {
    // The comm contains spaces and a ')': the parser must scan from the
    // last ')' so those cannot shift the field offsets.
    const line = "1234 (weird )name) S 1000 1234 1000 0 -1 0 0 0 0 0 0 0 0 0 20 0 1 0 987654 0 0\n";
    const st = parseStat(line) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(posix.pid_t, 1000), st.ppid);
    try std.testing.expectEqual(@as(u8, 'S'), st.state);
    try std.testing.expectEqual(@as(u64, 987654), st.start);
}

test "parseStat rejects malformed input" {
    try std.testing.expect(parseStat("") == null);
    try std.testing.expect(parseStat("no parens here") == null);
    // Truncated before starttime (field 22).
    try std.testing.expect(parseStat("1 (x) S 0 1 1") == null);
}

test "normalizeStart never yields the unknown sentinel" {
    try std.testing.expectEqual(@as(u64, 1), normalizeStart(0));
    try std.testing.expectEqual(@as(u64, 42), normalizeStart(42));
}
