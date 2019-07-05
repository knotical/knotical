
// ARGS: -cmpLt C1 C2 -tex

void printf(int i)

int scanf(int i)

int nondet()

void C1()
{
   int count=1;
   while (count <= 4)
   {
     printf(count); 
     count = count + 1;
   }
}

void C2()
{
   int count=1;
   int number;
   number = nondet();
   printf(count); 
   number = scanf(2);
   while (number >= 0 && count <= 4)
     {
       //printf(count); 
       count = count + 1;
   }
}

void main() { C1(); C2(); }
