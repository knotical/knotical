
// ARGS: -cmpLt C2 C1 -no-rem write,write_headers -tex

void update_stats()
void shutdown()
void compress()
int write(int x)
void handle_send()
void write_headers()
int nondet()
void clear_connection()
void httpd_ssl_write()

void C1(int x, int out) {
  int t = nondet();
  if(t>0) { write_headers(); }

  int err = write(out);
}

void C2(int x, int out, int compress, int keepalive) {
  if(compress>0) {
    compress();
    write_headers();
    httpd_ssl_write();
  } else {
    write_headers();
    httpd_ssl_write();
  }
  int err = write(out);
}

void main() {
  int x = nondet();
  int out = nondet();
  int compress = nondet();
  int keepalive = nondet();
  int err = nondet();
  C1(x, out);
  C2(x, out, compress, keepalive);
}


