# Heather certified program (function_ir_compile); the platform ABI around it is outside the proof.
.text
.globl scan_accept
.type scan_accept, @function
scan_accept_program:
scan_accept:
    .byte 0x48, 0x83, 0xc4, 0xc0, 0x48, 0x89, 0xf8, 0x48, 0xc1, 0xe8, 0x08, 0x48
    .byte 0x83, 0xc4, 0x40, 0xc3
.size scan_accept, .-scan_accept
.section .note.GNU-stack,"",@progbits
