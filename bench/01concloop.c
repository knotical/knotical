
// ARGS: -cmp C1 C2 -no-rem evA -tex

void printf(int i)

int scanf(int i)

int nondet()

void evA(int i) {
  printf(i);
}

void C1()
{
   int count=1;
   while (count <= 4)
   {
     evA(count); 
     count = count + 1;
   }
}

void C2()
{
   int count=1;
   int number;
   number = nondet();
   //printf(1); 
   //number = scanf(2);
   while (count <= 4 && number >= 0)
     {
       evA(count); 
       count = count + 1;
   }
}

void main() { C1(); C2(); }
