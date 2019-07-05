
void foo()
void bar()
int nondet()
  
void C1(int a) { if(a<=0) foo(); else bar(); }
void C2(int b) { if(b>0) foo(); else bar(); }

void main() {
  int a = nondet();
  int b = nondet();
  C1(a); C2(b);
}
