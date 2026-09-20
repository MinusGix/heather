/* SysV adapter for the scanner's three-register result. Storage and ABI glue
 * are external to the scanner certificate, like the final RET instruction. */
#ifndef SCANNER
#define SCANNER decimal_step
#endif
.text
.globl scan_buffer
.type scan_buffer, @function
scan_buffer:
    push %rbx
    mov %rdi, %rbx
    mov %rsi, %rdi
    mov %rdx, %rsi
    mov %rcx, %rdx
    call SCANNER
    mov %rcx, 0(%rbx)
    mov %rax, 8(%rbx)
    mov %rdx, 16(%rbx)
    mov %rbx, %rax
    pop %rbx
    ret
.size scan_buffer, .-scan_buffer
.section .note.GNU-stack,"",@progbits
