// ARGS: -cmp C1 C2 -depth 7 -tex

int getchar()
int nondet()

// model an array
int array_alloc(int size)
int array_read(int array_id, int loc)
void array_write(int array_id, int loc, int val)

void set_brk()

void C1()
{
  int buffer = array_alloc(1024);         
  int i = 0;
  int c;
  int brk = 0;
  while(brk<1) {
    c = getchar();
    if (c == 32)
      brk = 1;
    //set_brk();
    else {
      if (c == 33)
        brk = 1;
      //set_brk();
      else {
	array_write(buffer, i, c);  //store read characters into buffer
	i = i + 1;
      }
    }
  }
}
 
void C2()
{
  int buffer = array_alloc(1024);
  int i = 0;
  int c;
  int brk = 0;
  while(brk<1) {
    c = getchar();
    if (c == 32)
      brk = 1;
    //set_brk();
    else if (c == 33)
      brk = 1;
    //set_brk();
    else {
      //assume(i>=1024);
      if (i < 1024)
        brk = 1;
      //set_brk();
      else {
        array_write(buffer,i,c);
        i=i+1;
      }
    }
  }
}

void main() { C1(); C2(); }
