
void foo()
void bar()

void C1() { foo(); bar(); }
void C2() { bar(); foo(); }

void main() { C1(); C2(); }
