//! Client side: interactive attach (raw TTY <-> daemon socket) and
//! one-shot control commands (-X).

const std = @import("std");
const posix = std.posix;

const osc52 = @import("osc52.zig");
const protocol = @import("protocol.zig");
const ptypkg = @import("pty.zig");
const viewterm = @import("viewterm.zig");
const window = @import("window.zig");
const keys = @import("keys.zig");
const vt = @import("ghostty-vt");

const log = std.log.scoped(.client);

/// The attached client renders inside the terminal's own alternate
/// screen (like screen and tmux), so detaching restores the user's
/// pre-attach shell view. `1049h` also saves the cursor, which the
/// final `1049l` restores after undoing any state the session set.
/// SGR mouse (1006) and button events (1002) are enabled so wheel
/// events can be intercepted for local scrollback, mirroring boo ui.
const enter_sequence = "\x1b[?1049h" ++ viewterm.mouse_capture;
const restore_sequence = window.reset_state_sequence ++ "\x1b[?1049l";

/// Mouse reporting modes boo keeps on the real terminal so wheel events
/// arrive as SGR mouse sequences for local scrollback. A repaint's
/// `sanitize_sequence` disables mouse reporting; without re-establishing
/// this, the real terminal falls back to alternate-scroll (wheel becomes
/// arrow keys) instead of reporting wheel events for boo to intercept.
const mouse_capture = viewterm.mouse_capture;

/// Rows per mouse wheel tick, matching boo ui.
const wheel_lines = viewterm.wheel_lines;

/// How long to wait for a follow-up byte before treating a bare Esc at
/// the end of a read as a lone Esc keypress (which snaps scrollback to
/// the bottom). Mirrors boo ui.
const esc_flush_ms = viewterm.esc_flush_ms;

/// How long a transient status message (the copy confirmation) stays on
/// the bottom row. Shared with boo ui.
const message_ttl_ms = viewterm.message_ttl_ms;

/// Dim style for the transient status row, matching boo ui.
const style_dim = viewterm.style_dim;

/// A cell position in viewport coordinates (0-based), used for mouse
/// selection. Shared with boo ui.
const CellPos = viewterm.CellPos;

/// A parsed SGR mouse event, shared with boo ui.
const Mouse = viewterm.Mouse;

const Handler = vt.TerminalStream.Handler;

/// Stream callback state. The local terminal answers terminal queries
/// (DSR, DA, XTWINOPS, ...) itself only while it owns the view: while
/// scrolled back, while a selection or transient message is active, or
/// while still seeding from the attach replay. While live, the real
/// terminal answers queries through passthrough, so the local terminal
/// stays mute to avoid duplicate replies. The device-attributes and size
/// callbacks are shared with boo ui (`viewterm`); the write-pty and
/// xtversion callbacks differ.
// ponytail: module-level, safe because attachLoop is single-threaded.
// An accidental nested call would silently corrupt state; wrap in a
// struct if attach ever becomes re-entrant.
var reply_sock: posix.fd_t = -1;
var replies_on: bool = false;

/// Whether the local terminal should answer terminal queries itself
/// instead of passing them through to the real terminal. The local
/// terminal owns the view when still seeding from the attach replay,
/// scrolled back into history, or while a selection or transient message
/// is active.
fn repliesNeeded(awaiting_repaint: bool, scrolled: bool, select_active: bool, message_active: bool) bool {
    return awaiting_repaint or scrolled or select_active or message_active;
}

fn effectWritePty(handler: *Handler, data: [:0]const u8) void {
    _ = handler;
    if (!replies_on or reply_sock < 0) return;
    protocol.writeMsg(reply_sock, .input, data) catch {};
}

fn effectXtversion(handler: *Handler) []const u8 {
    _ = handler;
    return "boo " ++ @import("main.zig").version;
}

pub const Outcome = union(enum) {
    detached: void,
    stolen: void,
    ended: void,
    lost: void,
    /// The daemon told us to re-attach to this session. Owned, caller
    /// frees.
    switched: []const u8,
    /// The daemon told us to launch the UI (boo ui ran inside the
    /// session).
    launch_ui: void,
};

/// How long to wait for the terminal to answer the startup OSC 11
/// background probe. Terminals that support it answer within a few
/// milliseconds; the probe returns as soon as the reply arrives, so this
/// bound only delays attach on a terminal that never answers.
const probe_timeout_ms = 150;

var signal_pipe: posix.fd_t = -1;

fn handleSignal(sig: c_int) callconv(.c) void {
    if (signal_pipe >= 0) {
        const byte: [1]u8 = .{@intCast(sig & 0xff)};
        _ = posix.write(signal_pipe, &byte) catch {};
    }
}

pub fn connect(alloc: std.mem.Allocator, socket_path: []const u8) !posix.fd_t {
    _ = alloc;
    const fd = try posix.socket(posix.AF.UNIX, posix.SOCK.STREAM | posix.SOCK.CLOEXEC, 0);
    errdefer posix.close(fd);
    var addr: posix.sockaddr.un = .{ .family = posix.AF.UNIX, .path = undefined };
    if (socket_path.len >= addr.path.len) return error.NameTooLong;
    @memset(&addr.path, 0);
    @memcpy(addr.path[0..socket_path.len], socket_path);
    try posix.connect(fd, @ptrCast(&addr), @sizeOf(posix.sockaddr.un));
    return fd;
}

/// Attach the calling terminal to a session. Blocks until detach or
/// session end. Stdin/stdout must be the controlling TTY.
pub fn attach(alloc: std.mem.Allocator, socket_path: []const u8) !Outcome {
    const tty: posix.fd_t = 0;
    if (!posix.isatty(tty)) return error.NotATty;

    const sock = try connect(alloc, socket_path);
    defer posix.close(sock);

    // Signal plumbing: SIGWINCH resizes, SIGTERM/SIGHUP detach.
    const pipe_fds = try posix.pipe2(.{ .CLOEXEC = true, .NONBLOCK = true });
    defer posix.close(pipe_fds[0]);
    defer posix.close(pipe_fds[1]);
    signal_pipe = pipe_fds[1];
    defer signal_pipe = -1;
    const sigact: posix.Sigaction = .{
        .handler = .{ .handler = handleSignal },
        .mask = posix.sigemptyset(),
        .flags = posix.SA.RESTART,
    };
    posix.sigaction(posix.SIG.WINCH, &sigact, null);
    posix.sigaction(posix.SIG.TERM, &sigact, null);
    posix.sigaction(posix.SIG.HUP, &sigact, null);
    posix.sigaction(posix.SIG.PIPE, &.{
        .handler = .{ .handler = posix.SIG.IGN },
        .mask = posix.sigemptyset(),
        .flags = 0,
    }, null);

    // Raw mode, then move the terminal onto its alternate screen so
    // the session view never disturbs the user's shell scrollback.
    // Mouse reporting is enabled so wheel events can be intercepted
    // for local scrollback.
    const saved = try posix.tcgetattr(tty);
    var raw = saved;
    rawMode(&raw);
    try posix.tcsetattr(tty, .FLUSH, raw);
    // Set by the outcome paths below when a held C-d may still be
    // repeating; read by the deferred restore.
    var eof_guard = false;
    defer restoreTty(tty, saved, restore_sequence, eof_guard, 'd');

    try protocol.writeAll(1, enter_sequence);

    // Handshake with our current size first so the daemon sees the
    // attach promptly. The background probe below blocks briefly; a kill
    // or resize racing a slow attach would otherwise break the
    // connection or miss the initial size.
    const ws = ptypkg.getSize(tty) catch ptypkg.makeWinsize(24, 80);
    // Mark this as a ui-style view before attaching so the daemon
    // replays scrollback history on attach; the local terminal pages
    // it on a wheel-up, just like boo ui. An older daemon ignores the
    // unknown `.ui` message and attaches with no history.
    try protocol.writeMsg(sock, .ui, "");
    try protocol.writeMsg(sock, .attach, &(protocol.SizePayload{
        .rows = ws.row,
        .cols = ws.col,
    }).encode());

    // Probe the real terminal's background color so the daemon can
    // answer OSC 11 theme queries from inside the session, where the
    // application can no longer reach this terminal. The probe yields to
    // a pending signal, and any keystrokes typed during it are forwarded
    // as input afterward.
    var probe_scratch: [256]u8 = undefined;
    var leftover_len: usize = 0;
    if (probeBackground(tty, pipe_fds[0], &probe_scratch, &leftover_len)) |color| {
        protocol.writeMsg(sock, .bg_color, &color.encode()) catch {};
    }
    if (leftover_len > 0) protocol.writeMsg(sock, .input, probe_scratch[0..leftover_len]) catch {};

    // Local terminal emulator: all daemon output is fed through this so
    // the viewport can page back through history. While live at the
    // bottom, bytes also pass through to the real terminal raw (it is
    // the renderer); while scrolled back, the local terminal's viewport
    // is rendered instead.
    var term = try vt.Terminal.init(alloc, .{
        .cols = ws.col,
        .rows = ws.row,
        .max_scrollback = 512 * 1024,
    });
    defer term.deinit(alloc);
    var stream = term.vtStream();
    defer stream.deinit();
    // The local terminal answers terminal queries itself; the callbacks
    // are gated by `replies_on` so they only fire while the local
    // terminal owns the view (scrolled or still seeding).
    stream.handler.effects = .{
        .write_pty = &effectWritePty,
        .bell = null,
        .color_scheme = null,
        .device_attributes = &viewterm.effectDeviceAttributes,
        .enquiry = null,
        .size = &viewterm.effectSize,
        .title_changed = null,
        .pwd_changed = null,
        .xtversion = &effectXtversion,
    };
    reply_sock = sock;
    defer reply_sock = -1;

    var decoder: protocol.Decoder = .init(alloc);
    defer decoder.deinit();

    // Scrollback state.
    var scrolled: bool = false;
    // True until the daemon's first `.screen` after attach lands, so the
    // history replay and repaint seed the local terminal without
    // flashing through the real terminal; the `.screen` releases it.
    var awaiting_repaint = true;
    // Which screen the application is on, tracked from `.screen`
    // messages: the passthrough strips screen toggles, so the local
    // terminal cannot see them itself.
    var alt_screen_active = false;
    // Mouse selection state (viewport coordinates), mirroring boo ui:
    // a left-press sets the anchor, drag extends the head, release
    // copies the span to the clipboard via OSC 52 and clears it. A null
    // anchor means no selection in progress. While a selection is
    // active, output is fed to the local terminal but not passed through
    // (the viewport is frozen for the selection).
    var select_anchor: ?CellPos = null;
    var select_head: CellPos = .{ .x = 0, .y = 0 };
    replies_on = true;
    defer replies_on = false;
    // ESC/CSI hold buffer for input parsing: a sequence can split across
    // reads, and wheel events must be intercepted whole.
    var hold: [64]u8 = undefined;
    var hold_len: usize = 0;
    // A bare Esc held at the end of a read is ambiguous with the start
    // of an escape sequence; `esc_deadline` is when to flush it.
    var esc_deadline: i64 = 0;
    // Transient status message (the copy confirmation) shown on the bottom
    // row for `message_ttl_ms`, matching boo ui. While one is active the
    // viewport renders from the local terminal so the message stays put
    // over new output, like boo ui's borrowed bottom row.
    var message: std.ArrayList(u8) = .empty;
    defer message.deinit(std.heap.c_allocator);
    var message_deadline: i64 = 0;

    var buf: [32 * 1024]u8 = undefined;
    var fds = [_]posix.pollfd{
        .{ .fd = tty, .events = posix.POLL.IN, .revents = 0 },
        .{ .fd = sock, .events = posix.POLL.IN, .revents = 0 },
        .{ .fd = pipe_fds[0], .events = posix.POLL.IN, .revents = 0 },
    };

    var stdin_open = true;
    while (true) {
        for (&fds) |*pfd| pfd.revents = 0;
        // poll() ignores negative fds; once stdin is gone we only wait
        // for the daemon's detach acknowledgement.
        fds[0].fd = if (stdin_open) tty else -1;
        // A held bare Esc gets a short timeout to disambiguate from the
        // start of an escape sequence; a live transient message gets a
        // timeout to expire; otherwise block indefinitely.
        const now_poll = std.time.milliTimestamp();
        const next_deadline: i64 = blk: {
            var d: i64 = -1;
            if (esc_deadline != 0) d = esc_deadline;
            if (message_deadline != 0) d = if (d < 0) message_deadline else @min(d, message_deadline);
            break :blk d;
        };
        const timeout: i32 = if (next_deadline < 0)
            -1
        else
            @intCast(@min(@as(i64, std.math.maxInt(i32)), @max(@as(i64, 0), next_deadline - now_poll)));
        _ = try posix.poll(&fds, timeout);

        // A held bare Esc whose deadline passed is a lone Esc keypress.
        if (esc_deadline != 0 and std.time.milliTimestamp() >= esc_deadline) {
            esc_deadline = 0;
            if (hold_len == 1 and hold[0] == 0x1b) {
                hold_len = 0;
                if (scrolled or select_anchor != null) {
                    resumeLive(&term, &scrolled, &select_anchor, &message, &message_deadline);
                } else {
                    protocol.writeMsg(sock, .input, "\x1b") catch {};
                }
                replies_on = repliesNeeded(awaiting_repaint, scrolled, select_anchor != null, message_deadline != 0);
            }
        }

        // A transient status message has expired: drop it and repaint the
        // viewport without the overlay.
        if (message_deadline != 0 and std.time.milliTimestamp() >= message_deadline) {
            message_deadline = 0;
            message.clearRetainingCapacity();
            if (!awaiting_repaint and select_anchor == null) {
                renderState(&term, scrolled, null);
            }
            replies_on = repliesNeeded(awaiting_repaint, scrolled, select_anchor != null, false);
        }

        // Signals.
        if (fds[2].revents != 0) {
            while (true) {
                const n = posix.read(pipe_fds[0], &buf) catch 0;
                if (n == 0) break;
                for (buf[0..n]) |sig| switch (sig) {
                    posix.SIG.WINCH => {
                        const new_ws = ptypkg.getSize(tty) catch continue;
                        protocol.writeMsg(sock, .resize, &(protocol.SizePayload{
                            .rows = new_ws.row,
                            .cols = new_ws.col,
                        }).encode()) catch {};
                        term.resize(alloc, new_ws.col, new_ws.row) catch {};
                        // Re-render at the new size. While still seeding,
                        // the viewport is blank; the repaint's `.screen`
                        // will release it.
                        if (!awaiting_repaint) {
                            if (select_anchor) |a| {
                                renderSelect(&term, a, select_head);
                            } else {
                                const msg: ?[]const u8 = if (message_deadline != 0) message.items else null;
                                renderState(&term, scrolled, msg);
                            }
                        }
                    },
                    else => protocol.writeMsg(sock, .detach_req, "") catch {},
                };
                if (n < buf.len) break;
            }
        }

        // Terminal input -> daemon or scroll event.
        if (stdin_open and fds[0].revents != 0) {
            const n = posix.read(tty, &buf) catch 0;
            if (n == 0) {
                // TTY is gone; ask for an orderly detach.
                stdin_open = false;
                protocol.writeMsg(sock, .detach_req, "") catch {};
            } else {
                esc_deadline = processInput(
                    buf[0..n],
                    &hold,
                    &hold_len,
                    &term,
                    &scrolled,
                    alt_screen_active,
                    sock,
                    &select_anchor,
                    &select_head,
                    &message,
                    &message_deadline,
                );
                replies_on = repliesNeeded(awaiting_repaint, scrolled, select_anchor != null, message_deadline != 0);
            }
        }

        // Daemon -> terminal output and lifecycle messages.
        if (fds[1].revents != 0) {
            const n = posix.read(sock, &buf) catch 0;
            if (n == 0) return .{ .lost = {} };
            try decoder.feed(buf[0..n]);
            while (try decoder.next()) |msg| {
                switch (msg.type) {
                    .output => {
                        // Always feed the local terminal so its state
                        // (and scrollback) stays current.
                        stream.nextSlice(msg.payload);
                        if (awaiting_repaint or scrolled or select_anchor != null) {
                            // The viewport is pinned (seeding, scrolled, or
                            // selecting): new output lands below it, so no
                            // re-render is needed.
                        } else if (message_deadline != 0) {
                            // A transient message is borrowing the bottom
                            // row: render from the local terminal so new
                            // output shows on every row but that one, like
                            // boo ui's composited status row.
                            renderViewportStatus(&term, message.items, style_dim);
                        } else {
                            // Live at the bottom with no overlay: pass
                            // through raw so the real terminal renders.
                            protocol.writeAll(1, msg.payload) catch {};
                        }
                    },
                    .screen => {
                        alt_screen_active = std.mem.eql(u8, msg.payload, "alt");
                        if (awaiting_repaint) {
                            // The history replay and repaint have seeded
                            // the local terminal; paint the live screen
                            // (with modes) onto the real terminal and go
                            // live.
                            awaiting_repaint = false;
                            replies_on = repliesNeeded(false, scrolled, select_anchor != null, message_deadline != 0);
                            renderLive(&term);
                        } else if (!scrolled and select_anchor == null) {
                            // A screen change arrives with a repaint whose
                            // sanitize disables mouse reporting on the real
                            // terminal; re-establish boo's wheel capture
                            // when the application isn't using the mouse,
                            // so the wheel keeps paging scrollback instead
                            // of becoming alternate-scroll arrow keys.
                            ensureMouseCapture(&term);
                        }
                    },
                    .detached => {
                        if (std.mem.eql(u8, msg.payload, "launch-ui")) return .{ .launch_ui = {} };
                        if (std.mem.startsWith(u8, msg.payload, protocol.switch_to_prefix)) {
                            return .{ .switched = try alloc.dupe(u8, msg.payload[protocol.switch_to_prefix.len..]) };
                        }
                        if (std.mem.eql(u8, msg.payload, "stolen")) return .{ .stolen = {} };
                        if (std.mem.eql(u8, msg.payload, "detached-eof")) {
                            eof_guard = true;
                        }
                        return .{ .detached = {} };
                    },
                    .exit => {
                        // Sessions often end because the user typed
                        // C-d at the session's shell; treat the tail
                        // as EOF-dangerous.
                        eof_guard = true;
                        return .{ .ended = {} };
                    },
                    else => {},
                }
            }
        }
    }
}

/// Process terminal input: intercept wheel events for local scrollback
/// and mouse selection, and forward everything else to the daemon. A
/// sequence can split across reads, so `hold`/`hold_len` carry an
/// in-progress ESC or CSI sequence between calls. Returns a deadline
/// (millis) at which a held bare Esc should be flushed as a lone Esc, or
/// 0 if none.
fn processInput(
    bytes: []const u8,
    hold: *[64]u8,
    hold_len: *usize,
    term: *vt.Terminal,
    scrolled: *bool,
    alt_screen_active: bool,
    sock: posix.fd_t,
    select_anchor: *?CellPos,
    select_head: *CellPos,
    message: *std.ArrayList(u8),
    message_deadline: *i64,
) i64 {
    var fwd_buf: [4096]u8 = undefined;
    var fwd_len: usize = 0;

    const flush = struct {
        fn run(fwd: []const u8, s: posix.fd_t) void {
            if (fwd.len > 0) protocol.writeMsg(s, .input, fwd) catch {};
        }
    };

    // Defer the snap-back render until the end so a single input chunk
    // renders once even if it mixes forwarded bytes with other events.
    var snap_pending = false;

    var i: usize = 0;
    while (i < bytes.len) {
        const byte = bytes[i];

        if (hold_len.* > 0) {
            // Inside a held sequence.
            if (hold_len.* == 1 and hold[0] == 0x1b) {
                // Held bare Esc; this byte decides its fate.
                if (byte == '[') {
                    hold[1] = '[';
                    hold_len.* = 2;
                    i += 1;
                    continue;
                }
                // Not a CSI: the Esc is a lone Esc (or starts a non-CSI
                // escape). Forward it, then re-examine this byte.
                if (scrolled.*) snap_pending = true;
                flush.run(fwd_buf[0..fwd_len], sock);
                fwd_len = 0;
                flush.run("\x1b", sock);
                hold_len.* = 0;
                continue;
            }

            // CSI hold (hold[0..2] == ESC [).
            if (hold_len.* >= hold.len) {
                // Overflow: forward the hold as-is and re-examine byte.
                if (scrolled.*) snap_pending = true;
                flush.run(fwd_buf[0..fwd_len], sock);
                fwd_len = 0;
                flush.run(hold[0..hold_len.*], sock);
                hold_len.* = 0;
                continue;
            }
            hold[hold_len.*] = byte;
            hold_len.* += 1;
            i += 1;
            if (isCsiFinal(byte)) {
                const seq = hold[0..hold_len.*];
                hold_len.* = 0;
                if (parseMouseEvent(seq)) |ev| {
                    if (ev.isWheel()) {
                        // Wheel events are press-only; ignore any release.
                        if (!ev.release) {
                            flush.run(fwd_buf[0..fwd_len], sock);
                            fwd_len = 0;
                            handleWheel(term, scrolled, alt_screen_active, ev.code & 1 == 1, seq, sock, message, message_deadline);
                        }
                    } else {
                        // Non-wheel mouse: drive a selection when the
                        // application isn't using the mouse, else forward.
                        flush.run(fwd_buf[0..fwd_len], sock);
                        fwd_len = 0;
                        handleMouse(term, scrolled, ev, seq, sock, select_anchor, select_head, message, message_deadline);
                    }
                    continue;
                }
                if (scrolled.*) snap_pending = true;
                if (fwd_len + seq.len <= fwd_buf.len) {
                    @memcpy(fwd_buf[fwd_len..][0..seq.len], seq);
                    fwd_len += seq.len;
                } else {
                    flush.run(fwd_buf[0..fwd_len], sock);
                    fwd_len = 0;
                    flush.run(seq, sock);
                }
            } else if (byte == 0x1b) {
                // A new Esc aborts the CSI: forward the hold (minus the
                // new Esc) and hold the new Esc.
                if (scrolled.*) snap_pending = true;
                flush.run(fwd_buf[0..fwd_len], sock);
                fwd_len = 0;
                flush.run(hold[0 .. hold_len.* - 1], sock);
                hold[0] = 0x1b;
                hold_len.* = 1;
            }
            // else: keep accumulating.
            continue;
        }

        if (byte == 0x1b) {
            hold[0] = 0x1b;
            hold_len.* = 1;
            i += 1;
            continue;
        }

        // Plain byte: forward.
        if (scrolled.*) snap_pending = true;
        if (fwd_len < fwd_buf.len) {
            fwd_buf[fwd_len] = byte;
            fwd_len += 1;
        } else {
            flush.run(fwd_buf[0..fwd_len], sock);
            fwd_buf[0] = byte;
            fwd_len = 1;
        }
        i += 1;
    }

    if (snap_pending and scrolled.*) resumeLive(term, scrolled, select_anchor, message, message_deadline);
    flush.run(fwd_buf[0..fwd_len], sock);

    // A held bare Esc at the end of a read is ambiguous: the Esc key, or
    // the start of a sequence split across reads. Wait briefly for more.
    if (hold_len.* == 1 and hold[0] == 0x1b) {
        return std.time.milliTimestamp() + esc_flush_ms;
    }
    return 0;
}

/// Whether `b` is a CSI final byte (0x40-0x7E). The introducer `[`
/// (0x5B) is itself in this range, which is why the hold state machine
/// only looks for a final byte once past `ESC [`.
fn isCsiFinal(b: u8) bool {
    return b >= 0x40 and b <= 0x7e;
}

/// If `seq` is an SGR mouse event, parse it. Returns null otherwise.
fn parseMouseEvent(seq: []const u8) ?Mouse {
    if (seq.len < 5 or seq[0] != 0x1b or seq[1] != '[' or seq[2] != '<') return null;
    const final_b = seq[seq.len - 1];
    if (final_b != 'M' and final_b != 'm') return null;
    const body = seq[3 .. seq.len - 1];
    var it = std.mem.splitScalar(u8, body, ';');
    const code = parseField(it.next()) orelse return null;
    const x = parseField(it.next()) orelse return null;
    const y = parseField(it.next()) orelse return null;
    return .{ .code = code, .x = x, .y = y, .release = final_b == 'm' };
}

fn parseField(s: ?[]const u8) ?u16 {
    const slice = s orelse return null;
    if (slice.len == 0) return null;
    return std.fmt.parseInt(u16, slice, 10) catch return null;
}

/// Handle a wheel event, mirroring boo ui's wheelViewport: applications
/// that asked for mouse reporting get the event; alternate-screen
/// applications get arrow keys (alternate-scroll); otherwise the local
/// scrollback is paged. `seq` is the raw SGR mouse sequence, forwarded
/// verbatim in the first case.
///
/// Like boo ui, "scrolled" is derived from `viewportIsBottom()` after
/// the scroll, so wheeling up when there is no history never enters
/// scrollback mode (and never shows the scrollback hint).
fn handleWheel(
    term: *vt.Terminal,
    scrolled: *bool,
    alt_screen_active: bool,
    down: bool,
    seq: []const u8,
    sock: posix.fd_t,
    message: *std.ArrayList(u8),
    message_deadline: *i64,
) void {
    if (term.flags.mouse_event != .none) {
        protocol.writeMsg(sock, .input, seq) catch {};
        return;
    }
    if (alt_screen_active) {
        const arrow = viewterm.cursorArrowSeq(term, down);
        var n: u16 = 0;
        while (n < wheel_lines) : (n += 1) {
            protocol.writeMsg(sock, .input, arrow) catch {};
        }
        return;
    }
    const was_at_bottom = term.screens.active.viewportIsBottom();
    const delta: isize = if (down) @as(isize, wheel_lines) else -@as(isize, wheel_lines);
    term.scrollViewport(.{ .delta = delta });
    if (term.screens.active.viewportIsBottom()) {
        // At the bottom there is nothing (left) to scroll. Only a
        // previously scrolled viewport needs to snap back to live; an
        // already-live screen is unchanged, so it is not repainted.
        if (scrolled.*) {
            scrolled.* = false;
            const msg: ?[]const u8 = if (message_deadline.* != 0) message.items else null;
            renderState(term, false, msg);
        }
        return;
    }
    scrolled.* = true;
    if (was_at_bottom) {
        // Entering scrollback from the live bottom: the scrollback hint
        // takes the bottom row, so a stale transient message is cleared,
        // matching boo ui's scrollView.
        message.clearRetainingCapacity();
        message_deadline.* = 0;
    }
    const msg: ?[]const u8 = if (message_deadline.* != 0) message.items else null;
    renderState(term, true, msg);
}

/// Return the viewport to the live bottom, clear any selection, and
/// repaint. Used after scroll-back, an in-progress selection, or a
/// snapped-back Esc. A still-active transient message stays on the
/// bottom row, like boo ui (Esc snaps scrollback but not the message).
fn resumeLive(
    term: *vt.Terminal,
    scrolled: *bool,
    select_anchor: *?CellPos,
    message: *std.ArrayList(u8),
    message_deadline: *i64,
) void {
    if (scrolled.*) {
        scrolled.* = false;
        term.scrollViewport(.{ .bottom = {} });
    }
    if (select_anchor.*) |_| select_anchor.* = null;
    const msg: ?[]const u8 = if (message_deadline.* != 0) message.items else null;
    renderState(term, false, msg);
}

/// Handle a non-wheel mouse event, mirroring boo ui's viewport selection:
/// applications that asked for mouse reporting get the raw event;
/// otherwise a left-press starts a selection, drag extends it, and
/// release copies the span to the clipboard via OSC 52.
fn handleMouse(
    term: *vt.Terminal,
    scrolled: *bool,
    ev: Mouse,
    seq: []const u8,
    sock: posix.fd_t,
    select_anchor: *?CellPos,
    select_head: *CellPos,
    message: *std.ArrayList(u8),
    message_deadline: *i64,
) void {
    if (term.flags.mouse_event != .none) {
        protocol.writeMsg(sock, .input, seq) catch {};
        return;
    }
    const cols = term.cols;
    const rows = term.rows;
    if (cols == 0 or rows == 0) return;
    const x: u16 = @min(ev.x -| 1, cols - 1);
    const y: u16 = @min(ev.y -| 1, rows - 1);

    if (select_anchor.*) |anchor| {
        // An in-progress selection: motion extends it, release copies.
        if (!ev.release and !ev.isMotion()) return;
        const moved = x != select_head.*.x or y != select_head.*.y;
        select_head.* = .{ .x = x, .y = y };
        if (!ev.release) {
            if (moved) renderSelect(term, anchor, select_head.*);
            return;
        }
        if (anchor.x != select_head.*.x or anchor.y != select_head.*.y) {
            copySelection(term, anchor, select_head.*, message, message_deadline);
        }
        select_anchor.* = null;
        const msg: ?[]const u8 = if (message_deadline.* != 0) message.items else null;
        renderState(term, scrolled.*, msg);
        return;
    }

    // No selection in progress: a left-press (no motion) starts one.
    if (ev.release or ev.isMotion()) return;
    if (ev.code & 3 != 0) return;
    const start: CellPos = .{ .x = x, .y = y };
    select_anchor.* = start;
    select_head.* = start;
    renderSelect(term, start, start);
}

/// Render the viewport with an in-progress selection highlighted in
/// reverse video, like boo ui. The cursor is hidden; wheel capture is
/// kept on. Used while a selection is active (live or scrolled).
fn renderSelect(term: *vt.Terminal, anchor: CellPos, head: CellPos) void {
    if (term.rows == 0 or term.cols == 0) return;
    const alloc = std.heap.c_allocator;
    var out: std.ArrayList(u8) = .empty;
    defer out.deinit(alloc);
    out.appendSlice(alloc, window.sanitize_sequence) catch return;
    out.appendSlice(alloc, "\x1b[?2026h\x1b[?25l") catch return;
    var y: u16 = 0;
    while (y < term.rows) : (y += 1) {
        out.print(alloc, "\x1b[{d};1H\x1b[K", .{y + 1}) catch return;
        viewterm.appendTermRow(alloc, term, y, &out) catch return;
        // Overpaint the selected span in reverse video, like boo ui.
        if (viewterm.selectionSpan(anchor, head, y, term.cols)) |span| {
            out.print(alloc, "\x1b[{d};{d}H", .{ y + 1, span.x0 + 1 }) catch return;
            out.appendSlice(alloc, viewterm.style_selected) catch return;
            viewterm.appendPlainSpan(alloc, term, y, span.x0, span.x1, &out) catch return;
            out.appendSlice(alloc, viewterm.sgr_reset) catch return;
        }
    }
    out.appendSlice(alloc, "\x1b[?2026l") catch return;
    if (term.flags.mouse_event == .none) {
        out.appendSlice(alloc, mouse_capture) catch return;
    }
    _ = protocol.writeAll(posix.STDOUT_FILENO, out.items) catch {};
}

/// Copy the selected viewport text to the clipboard via OSC 52, which
/// works over SSH and through nested multiplexers, and set a transient
/// "copied N characters" confirmation on the bottom row. Mirrors boo ui.
fn copySelection(
    term: *vt.Terminal,
    anchor: CellPos,
    head: CellPos,
    message: *std.ArrayList(u8),
    message_deadline: *i64,
) void {
    const alloc = std.heap.c_allocator;
    const text = viewterm.selectionPlainText(alloc, term, anchor, head) orelse return;
    defer alloc.free(text);
    if (text.len == 0) return;
    const seq = osc52.copySequence(alloc, text) catch return;
    defer alloc.free(seq);
    _ = protocol.writeAll(posix.STDOUT_FILENO, seq) catch {};
    message.clearRetainingCapacity();
    message.print(alloc, "copied {d} characters", .{text.len}) catch {};
    message_deadline.* = std.time.milliTimestamp() + message_ttl_ms;
}

/// Repaint the live screen onto the real terminal, re-establishing
/// modes (cursor keys, bracketed paste, mouse, ...) so the real
/// terminal mirrors the local terminal after a repaint or snap-back.
fn renderLive(term: *vt.Terminal) void {
    const alloc = std.heap.c_allocator;
    var out: std.Io.Writer.Allocating = .init(alloc);
    defer out.deinit();
    out.writer.writeAll(window.sanitize_sequence) catch return;
    {
        var f: vt.formatter.TerminalFormatter = .init(term, .{ .emit = .vt });
        f.content = .{ .selection = window.screenSelectionOf(term) };
        // Keep the user's palette (emit palette references, not
        // redefinitions); re-establish modes, scrolling region, tabstops,
        // and keyboard protocol so the real terminal matches the local.
        f.extra = .{
            .palette = false,
            .modes = true,
            .scrolling_region = true,
            .tabstops = true,
            .pwd = false,
            .keyboard = true,
            .screen = .all,
        };
        out.writer.print("{f}", .{f}) catch return;
    }
    // sanitize above disabled mouse reporting; restore boo's wheel
    // capture unless the application is using the mouse itself (its
    // modes were re-emitted by the formatter), so the wheel reaches this
    // client instead of turning into alternate-scroll arrow keys.
    if (term.flags.mouse_event == .none) {
        out.writer.writeAll(mouse_capture) catch return;
    }
    // The formatter's tabstop and scrolling-region extras move the
    // cursor, so position it last, like the daemon's repaint.
    window.writeCursorPosOf(term, &out.writer) catch return;
    _ = protocol.writeAll(posix.STDOUT_FILENO, out.writer.buffered()) catch {};
}

/// Render the full viewport from the local terminal state with a status
/// string overlaid on the bottom row. Used while scrolled (the scrollback
/// hint) or while a transient message borrows the bottom row (the copy
/// confirmation), mirroring boo ui's status row. `style` is the SGR prefix
/// applied to the status text.
fn renderViewportStatus(term: *vt.Terminal, status: []const u8, style: []const u8) void {
    if (term.rows == 0 or term.cols == 0) return;
    const alloc = std.heap.c_allocator;
    var out: std.ArrayList(u8) = .empty;
    defer out.deinit(alloc);
    out.appendSlice(alloc, window.sanitize_sequence) catch return;
    out.appendSlice(alloc, "\x1b[?2026h\x1b[?25l") catch return;
    var y: u16 = 0;
    while (y < term.rows) : (y += 1) {
        out.print(alloc, "\x1b[{d};1H\x1b[K", .{y + 1}) catch return;
        viewterm.appendTermRow(alloc, term, y, &out) catch return;
    }
    out.print(alloc, "\x1b[{d};1H{s} {s}{s}\x1b[K", .{term.rows, style, status, viewterm.sgr_reset}) catch return;
    out.appendSlice(alloc, "\x1b[?2026l") catch return;
    if (term.flags.mouse_event == .none) {
        out.appendSlice(alloc, mouse_capture) catch return;
    }
    _ = protocol.writeAll(posix.STDOUT_FILENO, out.items) catch {};
}

/// Render the viewport for the current overlay state: the transient
/// message on the bottom row when one is active (overriding the scrollback
/// hint, as in boo ui), else the scrolled history, else the live screen.
/// An in-progress selection has its own render path (`renderSelect`) and
/// is handled by the caller.
fn renderState(term: *vt.Terminal, scrolled: bool, message_text: ?[]const u8) void {
    if (message_text) |m| {
        renderViewportStatus(term, m, style_dim);
    } else if (scrolled) {
        renderViewportStatus(term, "scrollback  wheel down or esc to return ", style_dim);
    } else {
        renderLive(term);
    }
}

/// Re-establish wheel capture on the real terminal after a passthrough
/// repaint disables mouse reporting, when the application isn't using the
/// mouse. Used on screen-change repaints that arrive after the initial
/// attach (where `renderLive` already handles it).
fn ensureMouseCapture(term: *vt.Terminal) void {
    if (term.flags.mouse_event != .none) return;
    _ = protocol.writeAll(posix.STDOUT_FILENO, mouse_capture) catch {};
}

/// Probe the real terminal for its background color via an OSC 11 query
/// and parse the reply. Returns null if the terminal does not answer
/// within `probe_timeout_ms` or a pending signal (resize/quit) on
/// `signal_fd` cuts the probe short so the caller can service it. Bytes
/// read while waiting that are not the reply (e.g. a keystroke typed
/// during attach) are left in `scratch[0..leftover_len.*]` for the
/// caller to forward as input. Pass -1 for `signal_fd` to skip the
/// signal check.
pub fn probeBackground(
    tty: posix.fd_t,
    signal_fd: posix.fd_t,
    scratch: []u8,
    leftover_len: *usize,
) ?protocol.RgbPayload {
    leftover_len.* = 0;
    // The query goes to the terminal on stdout; the reply arrives on the
    // input fd. For an attached client and the ui both are the same tty.
    protocol.writeAll(posix.STDOUT_FILENO, "\x1b]11;?\x07") catch return null;

    const deadline = std.time.milliTimestamp() + probe_timeout_ms;
    var len: usize = 0;
    while (len < scratch.len) {
        const now = std.time.milliTimestamp();
        if (now >= deadline) break;
        var fds = [_]posix.pollfd{
            .{ .fd = tty, .events = posix.POLL.IN, .revents = 0 },
            .{ .fd = signal_fd, .events = posix.POLL.IN, .revents = 0 },
        };
        const ready = posix.poll(&fds, @intCast(deadline - now)) catch break;
        if (ready == 0) break;
        // A pending signal (resize or quit) must reach the caller's loop
        // without delay; stop probing and leave it queued.
        if (fds[1].revents != 0) break;
        if (fds[0].revents == 0) continue;
        const n = posix.read(tty, scratch[len..]) catch break;
        if (n == 0) break;
        len += n;
        if (findOsc11Reply(scratch[0..len])) |span| {
            const color = parseOsc11Reply(scratch[span.start..span.end]);
            // Drop the reply from the buffer; keep anything else (typed
            // input) as leftover for the caller to forward.
            const removed = span.end - span.start;
            std.mem.copyForwards(u8, scratch[span.start..], scratch[span.end..len]);
            leftover_len.* = len - removed;
            return color;
        }
    }
    leftover_len.* = len;
    return null;
}

const Osc11Span = struct { start: usize, end: usize };

/// Locate a complete OSC 11 reply (`ESC ] 11 ; ... BEL|ST`) in `data`,
/// returning the byte span it occupies, terminator included.
fn findOsc11Reply(data: []const u8) ?Osc11Span {
    const marker = "\x1b]11;";
    const start = std.mem.indexOf(u8, data, marker) orelse return null;
    const body = data[start + marker.len ..];
    if (std.mem.indexOfScalar(u8, body, 0x07)) |bel| {
        return .{ .start = start, .end = start + marker.len + bel + 1 };
    }
    if (std.mem.indexOf(u8, body, "\x1b\\")) |st| {
        return .{ .start = start, .end = start + marker.len + st + 2 };
    }
    return null;
}

/// Parse an OSC 11 reply (`ESC ] 11 ; rgb:R/G/B` with a BEL or ST
/// terminator) into a 16-bit RGB. Each channel may be 1-4 hex digits and
/// is scaled to 16-bit. Returns null for anything it does not recognize.
pub fn parseOsc11Reply(data: []const u8) ?protocol.RgbPayload {
    const marker = "\x1b]11;";
    const start = std.mem.indexOf(u8, data, marker) orelse return null;
    var body = data[start + marker.len ..];
    if (std.mem.indexOfScalar(u8, body, 0x07)) |bel| {
        body = body[0..bel];
    } else if (std.mem.indexOf(u8, body, "\x1b\\")) |st| {
        body = body[0..st];
    }
    const rgb_prefix = "rgb:";
    if (!std.mem.startsWith(u8, body, rgb_prefix)) return null;
    var it = std.mem.splitScalar(u8, body[rgb_prefix.len..], '/');
    const r = parseChannel(it.next() orelse return null) orelse return null;
    const g = parseChannel(it.next() orelse return null) orelse return null;
    const b = parseChannel(it.next() orelse return null) orelse return null;
    if (it.next() != null) return null;
    return .{ .r = r, .g = g, .b = b };
}

fn parseChannel(s: []const u8) ?u16 {
    if (s.len == 0 or s.len > 4) return null;
    const v = std.fmt.parseInt(u16, s, 16) catch return null;
    const wide: u32 = v;
    return switch (s.len) {
        1 => @intCast(wide * 0x1111), // 0xF  -> 0xFFFF
        2 => @intCast(wide * 0x101), // 0xFF -> 0xFFFF
        3 => @intCast((wide * 0xffff) / 0xfff), // 0xFFF -> 0xFFFF
        else => @intCast(wide), // already 16-bit
    };
}

/// Configure a termios for raw byte-at-a-time input. Shared with the
/// boo ui client, which manages its own terminal lifecycle.
pub fn rawMode(t: *posix.termios) void {
    t.iflag.IGNBRK = false;
    t.iflag.BRKINT = false;
    t.iflag.PARMRK = false;
    t.iflag.ISTRIP = false;
    t.iflag.INLCR = false;
    t.iflag.IGNCR = false;
    t.iflag.ICRNL = false;
    t.iflag.IXON = false;
    t.oflag.OPOST = false;
    t.lflag.ECHO = false;
    t.lflag.ECHONL = false;
    t.lflag.ICANON = false;
    t.lflag.ISIG = false;
    t.lflag.IEXTEN = false;
    t.cflag.CSIZE = .CS8;
    t.cflag.PARENB = false;
    t.cc[@intFromEnum(posix.V.MIN)] = 1;
    t.cc[@intFromEnum(posix.V.TIME)] = 0;
}

/// Read and discard terminal input until it goes quiet.
///
/// When a detach is triggered by a key the user is still holding, the
/// terminal keeps producing input after the daemon has already decided
/// to detach: auto-repeats of the command key, kitty release reports,
/// impatient re-presses, and (on a remote connection) anything in
/// flight during the round trip. The final TCSAFLUSH only discards
/// what has reached the tty queue at that instant, so without this
/// wait the tail is delivered to the shell that regains the terminal:
/// a stray `d` typed at the prompt, or worse, a leaked C-d that EOFs
/// the login shell and ends the SSH session.
///
/// Runs while the terminal is still in raw mode, so the discarded
/// bytes are never echoed. Two timers bound the wait: `guard_ms`
/// covers the silence between the triggering press and the first
/// auto-repeat (keyboard repeat delays reach ~660ms on common
/// configurations, so EOF-dangerous detaches use the long guard),
/// then each absorbed chunk extends the wait by a short tail until
/// the input stays quiet, all capped at drain_cap_ms. On terminals
/// that report key releases (the kitty protocol, which restoreTty
/// enables for the drain), the triggering key's release ends the wait
/// at once, so the timers are only a fallback.
fn drainInput(tty: posix.fd_t, guard_ms: i64, trigger_cp: u32) void {
    const start = std.time.milliTimestamp();
    const cap = start + drain_cap_ms;
    var deadline = start + guard_ms;
    var buf: [256]u8 = undefined;
    var scan: ReleaseScan = .{ .want_cp = trigger_cp };
    while (true) {
        const now = std.time.milliTimestamp();
        const until = @min(deadline, cap);
        if (now >= until) return;
        var fds = [_]posix.pollfd{
            .{ .fd = tty, .events = posix.POLL.IN, .revents = 0 },
        };
        const ready = posix.poll(&fds, @intCast(until - now)) catch return;
        if (ready == 0) return;
        const n = posix.read(tty, &buf) catch return;
        if (n == 0) return;
        // The triggering key's kitty release means the user let go: no
        // more auto-repeats can follow, so stop draining immediately.
        if (scan.feed(buf[0..n])) return;
        deadline = @max(deadline, std.time.milliTimestamp() + drain_tail_ms);
    }
}

/// Scans drained input for a kitty key-release event of the key that
/// triggered the detach. Carries CSI-parse state between calls so a
/// sequence split across reads is still recognized.
const ReleaseScan = struct {
    /// CSI parse state: 0 idle, 1 after ESC, 2 inside the CSI body.
    state: u8 = 0,
    body: [40]u8 = undefined,
    body_len: usize = 0,
    /// Effective codepoint whose release ends the drain; 0 matches any
    /// key release.
    want_cp: u32,

    fn feed(self: *ReleaseScan, bytes: []const u8) bool {
        for (bytes) |b| {
            switch (self.state) {
                1 => {
                    if (b == '[') {
                        self.state = 2;
                        self.body_len = 0;
                    } else self.state = if (b == 0x1b) 1 else 0;
                },
                2 => {
                    if (b == 'u') {
                        if (self.isRelease()) return true;
                        self.state = 0;
                    } else if ((b >= '0' and b <= '9') or b == ';' or b == ':') {
                        if (self.body_len < self.body.len) {
                            self.body[self.body_len] = b;
                            self.body_len += 1;
                        } else self.state = 0;
                    } else self.state = if (b == 0x1b) 1 else 0;
                },
                else => if (b == 0x1b) {
                    self.state = 1;
                },
            }
        }
        return false;
    }

    fn isRelease(self: *const ReleaseScan) bool {
        const key = keys.parseKitty(self.body[0..self.body_len]) orelse return false;
        if (key.event != 3) return false;
        return self.want_cp == 0 or keys.effectiveCp(key) == self.want_cp;
    }
};

/// Guard for detaches with no reason to expect a held key.
const drain_guard_short_ms = 300;
/// Guard for flows where the user plausibly holds C-d, the byte that
/// EOFs a cooked-mode shell: a C-a C-d detach and a session that ends
/// while attached (often a C-d typed at the session's own shell).
const drain_guard_eof_ms = 800;
const drain_tail_ms = 100;
const drain_cap_ms = 1500;
/// Kitty keyboard flags forced during the drain so a still-held key
/// reports its release: disambiguate (1) + event types (2) + report
/// all keys (8). Cleared again before the shell regains the terminal.
const drain_kbd_enable = "\x1b[=11;1u";
const drain_kbd_disable = "\x1b[=0;1u";

/// Restore a raw client terminal: screen restore, input drain, then
/// the mode switch. Shared with boo ui, whose quit has the same held
/// command key and kitty release tail to absorb.
pub fn restoreTty(
    tty: posix.fd_t,
    saved: posix.termios,
    restore: []const u8,
    eof_guard: bool,
    trigger_cp: u32,
) void {
    // Screen restore first: the user sees the detach immediately, and
    // a kitty-mode terminal stops CSI-u key reporting as soon as the
    // reset reaches it, so a still-held key repeats in legacy bytes
    // that the drain below absorbs. Only then hand the tty back, after
    // a final non-blocking input discard catches anything that slipped
    // in between the last drained read and the mode switch.
    protocol.writeAll(1, restore) catch {};
    // Re-enable kitty report-events so a still-held command key reports
    // its release, ending the drain the instant the user lets go rather
    // than waiting out the timed guard. Terminals without the kitty
    // protocol ignore this and the guard still applies.
    protocol.writeAll(1, drain_kbd_enable) catch {};
    drainInput(tty, if (eof_guard) drain_guard_eof_ms else drain_guard_short_ms, trigger_cp);
    // Clear keyboard reporting again before the shell regains the tty.
    protocol.writeAll(1, drain_kbd_disable) catch {};
    // Switch the mode back without TCSAFLUSH: on Darwin its output-drain
    // half blocks until the PTY master has consumed the writes above, so
    // a peer that briefly stopped reading (a detach test between reads, a
    // stalled remote link) wedges the restore, and the input-flush half
    // then discards whatever was typed in the meantime. Drain straggler
    // input non-blockingly instead, then apply the saved mode at once.
    flushPendingInput(tty);
    posix.tcsetattr(tty, .NOW, saved) catch {};
}

/// The input-flush half of TCSAFLUSH on its own: poll with a zero
/// timeout and read until the queue is empty, while the tty is still
/// raw so canonical buffering cannot hide a partial line. Skipping the
/// output-drain half is deliberate (see restoreTty): it would block on
/// Darwin until the PTY master consumes our output.
fn flushPendingInput(tty: posix.fd_t) void {
    var buf: [256]u8 = undefined;
    while (true) {
        var fds = [_]posix.pollfd{
            .{ .fd = tty, .events = posix.POLL.IN, .revents = 0 },
        };
        const ready = posix.poll(&fds, 0) catch return;
        if (ready == 0) return;
        const n = posix.read(tty, &buf) catch return;
        if (n == 0) return;
    }
}

pub const ControlResult = struct {
    ok: bool,
    /// Allocated; caller frees.
    text: []u8,
};

/// Send a single control command (-X) and wait for the reply. When
/// `timeout_ms` is non-null, give up with `error.Timeout` if no reply
/// arrives in that window, so a caller (notably `boo ui`) cannot hang
/// forever on a daemon that has stopped answering.
pub fn control(
    alloc: std.mem.Allocator,
    socket_path: []const u8,
    argv: []const []const u8,
    timeout_ms: ?u32,
) !ControlResult {
    const sock = try connect(alloc, socket_path);
    defer posix.close(sock);

    const payload = try protocol.encodeArgv(alloc, argv);
    defer alloc.free(payload);
    try protocol.writeMsg(sock, .command, payload);

    var decoder: protocol.Decoder = .init(alloc);
    defer decoder.deinit();
    var buf: [4096]u8 = undefined;
    const deadline: ?i64 = if (timeout_ms) |ms|
        std.time.milliTimestamp() + ms
    else
        null;
    while (true) {
        if (deadline) |dl| {
            const now = std.time.milliTimestamp();
            if (now >= dl) return error.Timeout;
            var fds = [_]posix.pollfd{
                .{ .fd = sock, .events = posix.POLL.IN, .revents = 0 },
            };
            const ready = posix.poll(&fds, @intCast(dl - now)) catch return error.Timeout;
            if (ready == 0) return error.Timeout;
        }
        const n = posix.read(sock, &buf) catch 0;
        if (n == 0) return error.ConnectionLost;
        try decoder.feed(buf[0..n]);
        while (try decoder.next()) |msg| {
            switch (msg.type) {
                .ok => return .{ .ok = true, .text = try alloc.dupe(u8, msg.payload) },
                .err => return .{ .ok = false, .text = try alloc.dupe(u8, msg.payload) },
                // Skip async frames (e.g. exit broadcast racing a quit).
                else => {},
            }
        }
    }
}

test "ReleaseScan: the triggering key's release ends the drain" {
    var scan: ReleaseScan = .{ .want_cp = 'd' };
    // Press and auto-repeat are not a release.
    try std.testing.expect(!scan.feed("\x1b[100;1:1u"));
    try std.testing.expect(!scan.feed("\x1b[100;1:2u"));
    // The release of the 'd' key ends the drain.
    try std.testing.expect(scan.feed("\x1b[100;1:3u"));
}

test "ReleaseScan: other keys' releases are ignored" {
    var scan: ReleaseScan = .{ .want_cp = 'd' };
    // A left-ctrl release from the C-a C-d chord is not the trigger.
    try std.testing.expect(!scan.feed("\x1b[57442;5:3u"));
    // C-d is the same physical 'd' key with ctrl held: its release ends
    // the drain, matched through the effective codepoint.
    try std.testing.expect(scan.feed("\x1b[100;5:3u"));
}

test "ReleaseScan: a sequence split across reads is still recognized" {
    var scan: ReleaseScan = .{ .want_cp = 'd' };
    try std.testing.expect(!scan.feed("\x1b[100;1"));
    try std.testing.expect(scan.feed(":3u"));
}

test "ReleaseScan: want_cp 0 matches any key release" {
    var scan: ReleaseScan = .{ .want_cp = 0 };
    try std.testing.expect(scan.feed("\x1b[97;1:3u"));
}

test "ReleaseScan: non-release CSI and plain bytes never trigger" {
    var scan: ReleaseScan = .{ .want_cp = 'd' };
    // Auto-repeats, an arrow key, and plain held bytes are not a
    // release of the trigger key.
    try std.testing.expect(!scan.feed("dddd"));
    try std.testing.expect(!scan.feed("\x1b[A\x1b[100;1:2u"));
}

test "parseOsc11Reply: BEL and ST terminators, various channel widths" {
    // 16-bit channels, BEL-terminated (ghostty's format).
    try std.testing.expectEqual(
        protocol.RgbPayload{ .r = 0x1234, .g = 0x5678, .b = 0x9abc },
        parseOsc11Reply("\x1b]11;rgb:1234/5678/9abc\x07").?,
    );
    // ST-terminated, 2-digit channels scaled to 16-bit.
    try std.testing.expectEqual(
        protocol.RgbPayload{ .r = 0xffff, .g = 0x0000, .b = 0x8080 },
        parseOsc11Reply("\x1b]11;rgb:ff/00/80\x1b\\").?,
    );
    // A reply embedded among other bytes still parses.
    try std.testing.expect(parseOsc11Reply("x\x1b]11;rgb:0000/0000/0000\x07y") != null);
    // A query is not a reply, and junk is rejected.
    try std.testing.expect(parseOsc11Reply("\x1b]11;?\x07") == null);
    try std.testing.expect(parseOsc11Reply("garbage") == null);
    try std.testing.expect(parseOsc11Reply("\x1b]11;rgb:00/00\x07") == null); // too few channels
}

test "findOsc11Reply: only a fully terminated reply is located" {
    // Incomplete (no terminator yet): not found.
    try std.testing.expect(findOsc11Reply("\x1b]11;rgb:1111/2222/3333") == null);
    // BEL-terminated reply: span covers the terminator (exclusive end).
    const span = findOsc11Reply("ab\x1b]11;rgb:1111/2222/3333\x07cd").?;
    try std.testing.expectEqual(@as(usize, 2), span.start);
    try std.testing.expectEqual(@as(usize, 26), span.end);
}

test "control times out when the daemon never answers" {
    const alloc = std.testing.allocator;

    var name_buf: [64]u8 = undefined;
    const path = try std.fmt.bufPrint(
        &name_buf,
        "/tmp/boo-control-timeout-{x}.sock",
        .{std.crypto.random.int(u32)},
    );
    std.fs.cwd().deleteFile(path) catch {};

    // A listener that never accepts: connect() still succeeds via the
    // backlog and the command write is buffered, so the reply read is
    // what blocks. Without the timeout this call would hang forever
    // (the boo ls / boo ui freeze); with it, it must give up.
    const lfd = try posix.socket(posix.AF.UNIX, posix.SOCK.STREAM | posix.SOCK.CLOEXEC, 0);
    defer {
        posix.close(lfd);
        std.fs.cwd().deleteFile(path) catch {};
    }
    var addr: posix.sockaddr.un = .{ .family = posix.AF.UNIX, .path = undefined };
    @memset(&addr.path, 0);
    @memcpy(addr.path[0..path.len], path);
    try posix.bind(lfd, @ptrCast(&addr), @sizeOf(posix.sockaddr.un));
    try posix.listen(lfd, 1);

    const start = std.time.milliTimestamp();
    try std.testing.expectError(error.Timeout, control(alloc, path, &.{"info"}, 150));
    try std.testing.expect(std.time.milliTimestamp() - start >= 100);
}
