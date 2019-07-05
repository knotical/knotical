// ARGS: -cmpLt C1 C2 -tex

void printf(int i)

int scanf(int i)

int nondet()
  
void C1()
{
   int count = nondet();
   while (count <= 4)
   {
     printf(count); 
     count = count + 1;
   }
}

void C2(int number)
{
   int count = nondet();
   assume(number >= 0);
   //assume(count <= 4);
   while (count <= 4 && number >= 0)
     {
       printf(count); 
       count = count + 1;
   }
}

void main() {
  C1();
  int number;
  number = nondet();
  C2(number); }
