
void B()
void C()
void D()
void G()
void H()
int nondet()
  
void C1(int a, int e) {
  int i = nondet();
  int j = nondet();
  while (i > 0) {
    if (a > 0) B();
    else C();
    i = nondet();
  }
  D();
  while (j > 0) {
    if (e > 0) G();
    else H();
    j = nondet();
  }
}

void C2(int b, int d) {
  int i = nondet();
  int j = nondet();
  while (i > 0) {
    if (b > 0) B();
    else C();
    i = nondet();
  }
  D();
  while (j > 0) {
    if (d > 0) G();
    else H();
    j = nondet();
  }
}

void main() {
  int a = nondet();
  int b = nondet();
  int d = nondet();
  int e = nondet();
  C1(a, e);
  C2(d, e);
}
