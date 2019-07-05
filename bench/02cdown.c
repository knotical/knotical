
int nondet()
void eventA()
void eventB()

void C1(int x) {
  eventA();
  while(x>0) { x = x - 1; }
  eventB();
  eventA();
}
void C2(int x) {
  eventA();
  while(x>0) { x = x - 2; }
  eventB();
  eventA();
}

int main() {
  int x = nondet();
  C1(x);
  C2(x);
}
