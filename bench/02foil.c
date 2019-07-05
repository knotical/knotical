int nondet()
void eventA()
void eventB()

void C1(int x) {
  eventA();
  eventB();
  eventB();
}
void C2(int x) {
  eventA();
  eventA();
  eventB();
}

int main() {
  int x = nondet();
  C1(x);
  C2(x);
}
