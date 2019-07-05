
int nondet()

void evA()

void C1(int count)
{
   while (count <= 4)
   {
     evA(); 
     count = count + 1;
   }
}

void C2(int count, int number)
{
   while (count <= 4 && number >= 0)
     {
       evA(); 
       count = count + 1;
   }
}

void main() {
  int c = nondet();
  int n = nondet();
  C1(c);
  C2(c, n);
}
