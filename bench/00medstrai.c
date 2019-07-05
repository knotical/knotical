
// ARGS: -cmp C1 C2 -depth 4 -tex

void m0()
void m1()
void m2()
void m3()
void m4()
void m5()
void m6()
void m7()
void m8()
void m9()
void m10()
void m11()
void m12()
void m13()
void m14()
void m15()
void m16()
void m17()
void m18()
void m19()
int nondet()

void C1(int N) {
  if(N>0) { m1(); m2(); }
  m4(); m5();
  if(N<0) { m11(); m12(); }
  m14(); m15();
}


void C2(int N) {
  m1(); m2();
  m4(); m5();
  m11(); m12();
  m14(); m15();
}

void main() {
  int N1 = nondet();
  int N2 = nondet();
  C1(N1);
  C2(N2);
}
