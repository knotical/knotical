
int nondet()
void eventA()
void eventB()

void C1(int x) {
  while(x>0) {
    x = x - 1;
    eventA();
    eventB();
  }
}
void C2(int x) {
  while(x>0) {
    x = x - 1;
    eventB();
    eventA();
  }
}

int main() {
  int x = nondet();
  C1(x);
  C2(x);
}
