//! Shared client-side viewport rendering and mouse-selection helpers
//! used by both `boo ui` (the multi-session TUI) and `boo attach` (the
//! single-session passthrough client). Each client renders a local
//! libghostty terminal to the user's real terminal; the pieces here -
//! row serialization, selection span math, clipboard text extraction,
//! and the query-reply effect callbacks - are identical between them
//! and kept here so the two stay in sync.
//!
//! The daemon-side `Window` owns its own terminal and repaints clients
//! via `window.zig`; these helpers are for a *client's* local view.

const std = @import("std");
const vt = @import("ghostty-vt");

/// A cell position in viewport coordinates (0-based), used for mouse
/// selection.
pub const CellPos = struct { x: u16, y: u16 };

/// An inclusive column span on a single viewport row.
pub const Span = struct { x0: u16, x1: u16 };

/// A parsed SGR mouse event (`ESC [ < code ; x ; y M|m`). `code` low
/// bits select the button, bit 5 marks motion, bit 6 marks wheel; `M`
/// is press/motion, `m` is release. Coordinates are 1-based.
pub const Mouse = struct {
    code: u16,
    x: u16,
    y: u16,
    release: bool,

    pub fn isWheel(self: Mouse) bool {
        return self.code & 64 != 0;
    }

    pub fn isMotion(self: Mouse) bool {
        return self.code & 32 != 0;
    }
};

/// Rows per mouse wheel tick.
pub const wheel_lines: u16 = 3;

/// How long to wait for a follow-up byte before treating a bare Esc at
/// the end of a read as a lone Esc keypress (which snaps scrollback to
/// the bottom).
pub const esc_flush_ms: i64 = 50;

/// How long a transient status message (the copy confirmation) stays on
/// the bottom row. Shared by boo ui and boo attach.
pub const message_ttl_ms: i64 = 1000;

/// Nominal cell metrics reported to applications that ask for pixel
/// sizes (XTWINOPS, kitty); the same values the daemon reports.
pub const cell_px_w: u32 = 8;
pub const cell_px_h: u32 = 16;

/// Mouse reporting modes a boo client keeps on the real terminal so
/// wheel events arrive as SGR mouse sequences for local scrollback. A
/// repaint's sanitize sequence disables mouse reporting; without
/// re-establishing this, the real terminal falls back to
/// alternate-scroll (wheel becomes arrow keys) instead of reporting
/// wheel events for the client to intercept.
pub const mouse_capture = "\x1b[?1002h\x1b[?1006h";

pub const style_selected = "\x1b[7m";
pub const sgr_reset = "\x1b[0m";
/// Dim style for status chrome (the status row, the scrollback hint),
/// shared by boo ui and boo attach.
pub const style_dim = "\x1b[2m";

/// Return `a` and `b` in a canonical order (start, end) so the smaller
/// coordinate comes first. Used by selection functions where the user
/// may drag in any direction.
pub fn normalize(a: CellPos, b: CellPos) struct { s: CellPos, e: CellPos } {
    var s = a;
    var e = b;
    if (e.y < s.y or (e.y == s.y and e.x < s.x)) std.mem.swap(CellPos, &s, &e);
    return .{ .s = s, .e = e };
}

/// The selection's inclusive column span on viewport row `y`, or null
/// when the row is outside the selection. `anchor`/`head` may be in any
/// order.
pub fn selectionSpan(
    anchor: CellPos,
    head: CellPos,
    y: u16,
    cols: u16,
) ?Span {
    if (cols == 0) return null;
    const n = normalize(anchor, head);
    if (y < n.s.y or y > n.e.y) return null;
    const x0: u16 = if (y == n.s.y) @min(n.s.x, cols - 1) else 0;
    const x1: u16 = if (y == n.e.y) @min(n.e.x, cols - 1) else cols - 1;
    if (x0 > x1) return null;
    return .{ .x0 = x0, .x1 = x1 };
}

/// Append one row of the terminal's active screen as styled VT bytes,
/// rendered through libghostty's own formatter so styles, wide
/// characters, and blank runs come out exactly as the daemon would
/// replay them, just one row at a time. Viewport pins follow scrollback
/// paging; at the bottom the viewport and the active screen are the
/// same rows. A row that opened a hyperlink is closed so it cannot leak
/// into the next row or the sidebar.
pub fn appendTermRow(
    alloc: std.mem.Allocator,
    term: *vt.Terminal,
    y: u16,
    out: *std.ArrayList(u8),
) !void {
    const screen = term.screens.active;
    if (term.cols == 0) return;
    // Viewport pins follow scrollback paging; at the bottom the
    // viewport and the active screen are the same rows.
    const start = screen.pages.pin(.{ .viewport = .{ .x = 0, .y = y } }) orelse return;
    const end = screen.pages.pin(.{ .viewport = .{ .x = term.cols - 1, .y = y } }) orelse return;

    var formatter: vt.formatter.ScreenFormatter = .init(screen, .vt);
    formatter.content = .{ .selection = vt.Selection.init(start, end, true) };

    // Format straight into `out`, reusing its capacity, so a repaint
    // does not allocate a fresh writer for every row.
    const begin = out.items.len;
    {
        var aw: std.Io.Writer.Allocating = .fromArrayList(alloc, out);
        defer out.* = aw.toArrayList();
        aw.writer.print("{f}", .{formatter}) catch return error.OutOfMemory;
    }
    // A row that opened a hyperlink must not leak it into the next
    // row or the sidebar.
    if (std.mem.indexOf(u8, out.items[begin..], "\x1b]8;") != null) {
        try out.appendSlice(alloc, "\x1b]8;;\x1b\\");
    }
}

/// Append one row's cells in [x0, x1] inclusive as plain text, with
/// trailing blanks trimmed. Used to repaint the selection highlight
/// over already-rendered row content.
pub fn appendPlainSpan(
    alloc: std.mem.Allocator,
    term: *vt.Terminal,
    y: u16,
    x0: u16,
    x1: u16,
    out: *std.ArrayList(u8),
) !void {
    const screen = term.screens.active;
    const start = screen.pages.pin(.{ .viewport = .{ .x = x0, .y = y } }) orelse return;
    const end = screen.pages.pin(.{ .viewport = .{ .x = x1, .y = y } }) orelse return;

    var formatter: vt.formatter.ScreenFormatter = .init(screen, .plain);
    formatter.content = .{ .selection = vt.Selection.init(start, end, false) };

    var aw: std.Io.Writer.Allocating = .init(alloc);
    defer aw.deinit();
    aw.writer.print("{f}", .{formatter}) catch return error.OutOfMemory;
    try out.appendSlice(alloc, aw.writer.buffered());
}

/// The selected viewport text (rows `a`..`b`, any order) as plain text,
/// caller-owned. Returns null if the pins cannot resolve or formatting
/// fails; empty if the selection covers no text.
pub fn selectionPlainText(
    alloc: std.mem.Allocator,
    term: *vt.Terminal,
    a: CellPos,
    b: CellPos,
) ?[]u8 {
    const n = normalize(a, b);
    const s = n.s;
    const e = n.e;
    const screen = term.screens.active;
    const start = screen.pages.pin(.{ .viewport = .{ .x = s.x, .y = s.y } }) orelse return null;
    const end = screen.pages.pin(.{ .viewport = .{ .x = e.x, .y = e.y } }) orelse return null;

    var formatter: vt.formatter.ScreenFormatter = .init(screen, .plain);
    formatter.content = .{ .selection = vt.Selection.init(start, end, false) };

    var aw: std.Io.Writer.Allocating = .init(alloc);
    defer aw.deinit();
    aw.writer.print("{f}", .{formatter}) catch return null;
    return alloc.dupe(u8, aw.writer.buffered()) catch null;
}

/// The arrow-key bytes a wheel tick should send to an alternate-screen
/// application, honoring the cursor-keys mode. `down` selects the
/// direction.
pub fn cursorArrowSeq(term: *vt.Terminal, down: bool) []const u8 {
    return if (term.modes.get(.cursor_keys))
        (if (down) "\x1bOB" else "\x1bOA")
    else
        (if (down) "\x1b[B" else "\x1b[A");
}

// -- Stream query-reply effect callbacks -------------------------------------
//
// A client's local terminal answers terminal queries (DSR, DA, XTWINOPS,
// ...) itself. These callbacks are identical between `boo ui` and `boo
// attach`; the write_pty callback (which routes replies to the session)
// and the bell/title callbacks differ, so those stay in each client.

const Handler = vt.TerminalStream.Handler;

/// Return type of a stream `Effects` callback field, so the callbacks
/// below can name types the vt module does not re-export.
pub fn EffectReturn(comptime field_name: []const u8) type {
    const Effects = Handler.Effects;
    const field = std.meta.fieldInfo(
        Effects,
        @field(std.meta.FieldEnum(Effects), field_name),
    );
    const Fn = @typeInfo(field.type).optional.child;
    return @typeInfo(@typeInfo(Fn).pointer.child).@"fn".return_type.?;
}

pub fn effectDeviceAttributes(handler: *Handler) EffectReturn("device_attributes") {
    _ = handler;
    return .{};
}

pub fn effectSize(handler: *Handler) ?vt.size_report.Size {
    const term = handler.terminal;
    return .{
        .rows = term.rows,
        .columns = term.cols,
        .cell_width = cell_px_w,
        .cell_height = cell_px_h,
    };
}
