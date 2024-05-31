const Mir = @This();

const std = @import("std");

instructions: std.MultiArrayList(Inst).Slice,
extra: []const u32,

pub const Inst = struct {
    tag: Tag,
    data: Data,

    pub const Index = enum(u32) { _ };

    pub const Tag = enum(u8) {
        load_imm32,
        @"return",
    };

    pub const Data = union {
        imm32: u32,
        extra: u32,
    };
};

pub fn deinit(self: *Mir, gpa: std.mem.Allocator) void {
    self.instructions.deinit(gpa);
    gpa.free(self.extra);
    self.* = undefined;
}
