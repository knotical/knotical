// ARGS: -cmpLt C1 C2 -no-rem evA,evB -tex

// NO SOLUTION
int nondet()
void evA()
void evB()

void C1(int x) {
   evB();
}
void C2() {
  evA();
}

int main() {
  int x1 = nondet();
  C1(x1);
  C2();
}
