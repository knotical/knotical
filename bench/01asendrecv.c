// ARGS: -cmp C1 C2 -no-rem recv,constructReply -tex

int recv()
void log(int i)
int constructReply()
void send(int i)
void sendA(int i)
int check(int b)
int nondet()
  
void C1(int x, int c) {
  while(x>0) {
    int b = recv();
    assume(c<=0);
    if (c>0) log(b);
    if (b>0) {
      int n = constructReply();
      send(n);
      if (c>0) log(n);
    }
    x = x - 1;
  }
}

void C2(int x, int c) {
  while(x>0) {
    int b = recv();
    if (b>0) {
      int auth = check(b);
      if (auth>0) {
	int n = constructReply();
	sendA(n);
      }
    }
    else log(b);
    x = x - 1;
  }
}

void main() {
  int x1 = nondet();
  int c1 = nondet();
  int x2 = nondet();
  int c2 = nondet();
  C1(x1, c1);
  C2(x2, c2);
}
