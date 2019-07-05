
// ARGS: -cmpLt C2 C1 -no-rem update_stats,shutdown -tex

void update_stats()
void shutdown()
void compress()
int write(int x)
void handle_send()
void write_headers()
int nondet()
void clear_connection()
void httpd_ssl_write()

void C1(int err) {
  if(err>0) {
    clear_connection();
    shutdown();
  } else {
    update_stats();
  }
}


void C2(int err, int keepalive) {
  if(err>0) {
    if(keepalive<=0) {
      shutdown();
    }
  } else {
    update_stats();
  }
}

void main() {
  int x = nondet();
  int out = nondet();
  int compress = nondet();
  int keepalive = nondet();
  int err = nondet();
  C1(err);
  C2(err, keepalive);
}


