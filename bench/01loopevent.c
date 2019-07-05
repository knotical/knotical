// ARGS: -cmp C1 C2 -no-rem eventA -tex
//void printf(int a, int b, int c)
void eventA()
int nondet()

void C1(int i,int j)
{
   while (i <= 4 || j <= 3)
   {
     eventA(); //printf(1, i, j);
     i = i+1;
     j = j+1;
   }
}

void C2(int i,int j)
{
   while (i <= 4 || j <= 3)
   {
	int a=i+j; 
	eventA(); //printf(1, i, j);
	i=i+1;
	j=j+1;
	if (a > 5)
	{
	  eventA(); //printf(2, a, 0);
	}
   }
}

void main() {
  int i = nondet();
  int j = nondet();
  C1(i,j);
  C2(i,j);
}
