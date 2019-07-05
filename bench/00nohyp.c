
// ARGS: -cmp C1 C2 -no-rem evA,evB -tex
int nondet()
void evA()
void evB()

void C1(int x) {
  if(x>0) { evA(); }
  else { evB(); }
}
void C2() {
  int t = nondet();
  if(t>0) { evB(); }
  else { evA(); }
}

int main() {
  int x1 = nondet();
  C1(x1);
  C2();
}
