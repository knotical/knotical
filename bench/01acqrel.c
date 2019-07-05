

int nondet()

void C1(int n) {
  int A=0; int R=0;
      while(1>0) {
         A = 1;
         A = 0;
         while(n>0) {
             n = n-1;
         }
         R = 1;
         R = 0;
      }
      while(n>0) { int x; x=x+0; }
}

void C2(int n) {
  int AA=0; int RR=0;
      while(n>0) {
         AA = 1;
         AA = 0;
         while(n>0) {
             n = n-1;
         }
         RR = 1;
         RR = 0;
      }
      while(1>0) { int x; x=x; }
}


int main() {
    int n = nondet();
    C1(n);
    C2(n);
}
