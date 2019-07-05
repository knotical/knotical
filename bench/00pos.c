// Impossible for equality comparison (no solutions)
// if we are not allowed to remove both evA and evB.

// ARGS: -cmpLt C1 C2 -no-rem evA,evB -tex

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
