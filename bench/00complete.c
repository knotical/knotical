int nondet()
void evA()
void evB()
void evC()

void C1() {
  evA();
}

void C2(int n) {
  if (n > 0) {
    evB();
  } else {
    evC();
  }
}

void main() {
  int n = nondet();
  C1();
  C2(n);
}
