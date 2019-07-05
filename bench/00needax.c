
// Need an axiom to cope with the possible evB in C1
// rather than removing both evA, evB
// NOTE: Similar to 00impos.c but running with different args

// ARGS: -cmpLt C1 C2 -tex

int nondet()
void evA()
void evB()

void C1(int x) {
  if(x>0) { evA(); }
  else { evB(); }
}
void C2() {
  evA();
}

int main() {
  int x1 = nondet();
  C1(x1);
  C2();
}
