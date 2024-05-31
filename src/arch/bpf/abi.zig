const std = @import("std");
const bits = @import("bits.zig");
const Register = bits.Register;
const RegisterManagerFn = @import("../../register_manager.zig").RegisterManager;

// r0 (exit/return) and r10 (frame pointer) omitted

pub const callee_preserved_regs = [_]Register{
    .r6, .r7, .r8, .r9,
};

pub const function_arg_regs = [_]Register{
    .r1, .r2, .r3, .r4, .r5,
};

const allocatable_registers = callee_preserved_regs ++ function_arg_regs;
pub const RegisterManager = RegisterManagerFn(@import("CodeGen.zig"), Register, &allocatable_registers);

// Register classes
const RegisterBitSet = RegisterManager.RegisterBitSet;
pub const RegisterClass = struct {
    pub const gp: RegisterBitSet = blk: {
        var set = RegisterBitSet.initEmpty();
        set.setRangeValue(.{
            .start = 0,
            .end = callee_preserved_regs.len,
        }, true);
        break :blk set;
    };

    pub const fa: RegisterBitSet = blk: {
        var set = RegisterBitSet.initEmpty();
        set.setRangeValue(.{
            .start = callee_preserved_regs.len,
            .end = callee_preserved_regs.len + function_arg_regs.len,
        }, true);
        break :blk set;
    };
};
