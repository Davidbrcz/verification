#ifndef AXIOMATIQUE 
#define AXIOMATIQUE 

/*@
@ axiomatic string {
@ logic integer strlen_{L}(char* src)
@ reads src[0..];
@ axiom strlen_inside{L}:
@ \forall char*src; \forall integer x; 0 <= x < strlen_(src) ==> src[x] != 0;
@ axiom strlen_end{L}:
@ \forall char* src; src[strlen_(src)] == 0;
@ axiom strlen_pos{L}:
@ \forall char* src; strlen_(src) >= 0;
@ }
@*/

#endif
