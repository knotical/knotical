
int recv()
void send()
void init()
int nondet()

void C1() {
  int a;
  init();
  a = recv();
  /* assume (a<=0); */
  if(a>0) {
    //init();
    send();
  }
}

void C2() {
  int a;
  init();
  a = recv();
  send();
}

void main() {
  C1(); C2();
}
