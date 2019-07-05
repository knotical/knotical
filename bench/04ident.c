
int copyin(int a, int b)
int copyout(int a, int b, int c)
void fdrop(int a, int b)
void free(int a, int b)
int nondet()
void C1(int p, int compat) {
  // struct proc *p;
  // register struct getpeername_args {
  int uap_fdes; // int fdes;
  int uap_asa;  // caddr_t asa;
  int uap_alen; // int *alen 
  int fp, so, sa, len, err;
  int sa_len;
  int sizeof_len;

  err = copyin(uap_alen, len);
  // (caddr_t)uap->alen, (caddr_t)&len, sizeof (len));
  if (err > 0) {
    fdrop(fp, p);
    //return (error);
  }

  if(sa_len < len) { len = sa_len; } /* [1] */
  err = copyout(sa, uap_asa, len); // (caddr_t)uap->asa, (u_int)len);
  if (err>0) {
    if (sa>0) free(sa, 42); // M_SONAME);
    fdrop(fp, p);
    //return (error);
  }
  err = copyout(len,uap_alen,sizeof_len);
  //(caddr_t)&len, (caddr_t)uap->alen, sizeof (len));
}

void C2(int p, int compat) {
  
  // struct proc *p;
  // register struct getpeername_args {
  int uap_fdes; // int fdes;
  int uap_asa;  // caddr_t asa;
  int uap_alen; // int *alen 
  int fp, so, sa, len, err;
  int sa_len;
  int sizeof_len;

  err = copyin(uap_alen, len);
  // (caddr_t)uap->alen, (caddr_t)&len, sizeof (len));
  if (err > 0) {
    fdrop(fp, p);
    //return (error);
  }

  if(sa_len < len) { len = sa_len; } /* [1] */
  err = copyout(sa, uap_asa, len); // (caddr_t)uap->asa, (u_int)len);
  if (err>0) {
    if (sa>0) free(sa, 42); // M_SONAME);
    fdrop(fp, p);
    //return (error);
  }
  err = copyout(len,uap_alen,sizeof_len);
  //(caddr_t)&len, (caddr_t)uap->alen, sizeof (len));
}

void main() {
  int p = nondet();
  int compat = nondet();
  C1(p,compat);
  C2(p,compat);
}
