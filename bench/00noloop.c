
// ARGS: -cmp C1 C2 -no-rem evA -tex

int nondet()
void evA()

void C1(int count)
{
  assume (count > 4);
  while (count <= 4)
  {
     evA(); 
     count = count + 1;
  }
}

void C2(int count)
{
   while (count <= 4)
     {
       evA(); 
       count = count + 1;
   }
}

void main() {
  int c1 = nondet();
  int c2 = nondet();
  C1(c1);
  C2(c2);
}
