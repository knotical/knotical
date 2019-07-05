
void recv()
void send()
void init()
int nondet()

void C1() {
  int a = nondet();
  if (a > 0) {
    send();
    recv();
  }
}

void C2() {
  int a = nondet();
  if (a > 0) {
    send();
  }
  recv();
}

void main() {
  C1(); C2();
}
