
int nondet()
void eventA()

void C1() {
  if(0>1) { eventA(); }
}
void C2() {
  if(1>0) { eventA(); }
}

int main() {
  C1();
  C2();
}
