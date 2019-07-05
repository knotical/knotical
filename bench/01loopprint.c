
void printf(int a, int b)
int nondet()

void C1(int i,int j)
{
   while (i <= 4 || j <= 3)
   {
     printf(i, j);
     i = i+1;
     j = j+1;
   }
}

void C2(int i,int j)
{
   while (i <= 4 || j <= 3)
   {
	int a=i+j; 
	printf(i, j);
	i=i+1;
	j=j+1;
	if (a > 5)
	{
	  printf(a, 0);
	}
   }
}

void main() {
  int i = nondet();
  int j = nondet();
  C1(i,j);
  C2(i,j);
}
