// Interproc does not support % operation

int nondet()

void C1(int N) {
  int i = 0;
  int t;
  int n;
  while (i<N){
    //if (i%2 == 0){
    n = nondet();
    if (n > 0) {
      t = 1;
    } else {
      t = 0;
    }
    i = i+1;
  }
}


void C2(int N) {
  int i = 0;
  int t;
  int n;
  while (i<N){
    //if (i%2 != 0){
    n = nondet();
    if (n <= 0) {
      t = 0;
    } else {
      t = 1;
    }
    i = i+1;
  }
}

void main() {
  int N = nondet();
  C1(N);
  C2(N);
}
