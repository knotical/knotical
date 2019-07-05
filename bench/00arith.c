int nondet()
  void foo()
  void bar()
  
void C1(int x, int c) {
  while(x>0) {
    if ( x % 2 == 0)
      foo();
    else
      bar();
  }
}

void C2(int x, int c) {
  foo();
  while(x>0) {
    if ( x%2 == 0)
      bar();
    else
      foo();
  }
}

void main() {
  int x = nondet();
  int c = nondet();
  C1(x,c); C2(x,c);
}
