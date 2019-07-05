int nondet()
void evA()
void evB()
void evC()
void evD()

void C1(int n) {
  if (n < 0) {
    evA();
  } else {
    evB();
  }
}

void C2(int n) {
  if (n > 0) {
    evC();
  } else {
    evD();
  }
}

void main() {
  int n1 = nondet();
  int n2 = nondet();
  C1(n1);
  C2(n2);
}
