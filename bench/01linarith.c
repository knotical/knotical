
int nondet()
void shutdown()
void pingall()
void C1()
{
  int c = nondet();
  int curr_serv;
  int servers = 4;
  int resp = 0;
  int tmp;
  curr_serv = servers;
  tmp = nondet();
  while(tmp>0) {
    assume(c>0);
    if( c > 0 ) {
      c = c-1;
      shutdown();
      curr_serv = curr_serv - 1;
      resp = resp + 1;
    } else {
      assume(c < curr_serv);
      shutdown();
      curr_serv = curr_serv -1;
    }
    tmp = nondet();
  }
}

void C2()
{
  int c = nondet();
  int curr_serv;
  int servers = 4;
  int resp = 0;
  int tmp;
  curr_serv = servers;
  tmp = nondet();
  while(tmp>0) {
    assume(c>0);
    pingall();
    curr_serv = curr_serv - 1;
    if( c > 0 ) {
      c = c-1;
      resp = resp + 1;
    } else {
      assume(c < curr_serv);
    }
    shutdown();
    tmp = nondet();
  }
}

void main(){
    C1();
    C2();
}
