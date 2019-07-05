
int getchar()
int nondet()

int array_alloc(int size)
int array_read(int val)
void array_write(int buffer, int val)
void show(int mes)
//void exit(int i)
  
void C1(int x) {
    int c = array_alloc(1000);

    if ( x == 0 ) {
        show(1);
        //exit(0);         
    }

    int b = getchar();
    while (b != 0){
      array_write(c, b);
      b = b - 1;
    }
    int r = array_read(c);
}

void C2(int x)
{
    int a = nondet();
    int c = array_alloc(a);
    
    if ( x == 0 ) {
        show(2);
        //exit(0);         
    }

    int b = getchar();
    while (b != 0 && a > b){
      array_write(c, b);
      b = b-1;
    }
    int r = array_read(c);
}

void main(){
    int x = nondet();
    C1(x);
    C2(x);

}









