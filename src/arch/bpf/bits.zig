pub const Register = enum(u4) {
    // zig fmt: off
    r0, // return value from function calls, and exit value for eBPF programs
    r1, r2, r3, r4, r5, // arguments for function calls
    r6, r7, r8, r9, // callee saved registers
    r10, // read-only frame pointer
    // r0-r5 are scratch registers; all registers 64-bit
    // zig fmt: on
};
