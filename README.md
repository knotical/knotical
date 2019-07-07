# Knotical: An Inference System of Trace Refinement Relations

## Getting Started Guide

### Using Docker

1. Install Docker. Follow the instructions on https://docs.docker.com/install/.

2. Build the Knotical image:

    ```
    docker build -t knotical .
    ```

3. Run the Knotical image:

    ```
    docker run -it knotical bash
    ```
    
### Installation on Ubuntu from scratch

NOTE: The following instructions have been tested on Ubuntu 18.04 LTS with opam 1.2.2.

1. Install Prerequisites:

    ```
    apt-get clean
    apt-get update
    apt-get install -qy libppl-dev libmpfr-dev m4 subversion gawk
    ```
    
2. Install `opam`:

    ```
    apt-get install opam
    opam init
    ```
    
   You can follow the instructions on https://opam.ocaml.org/doc/Install.html to install the latest `opam` 2.0.4. You may need to install `gcc`, `g++`, and `make` before doing that.

3. Install OCaml via `opam`:

    ```
    opam switch 4.06.1
    eval `opam config env`
    ```

4. Install Dependencies via `opam`:
 
    ```
    opam install oasis ocamlbuild
    opam install apron conf-ppl camllib safa batteries camlp4 core ocamlgraph
    eval `opam config env`
    ```
    
5. Install `Fixpoint` (http://pop-art.inrialpes.fr/people/bjeannet/bjeannet-forge/fixpoint/):
  
    ```
    svn checkout https://scm.gforge.inria.fr/anonscm/svn/bjeannet/pkg/fixpoint/
    cd fixpoint/trunk/
    cp Makefile.config.model Makefile.config
    make
    make install
    ```

6. Compile Knotical:
   
    ```
    oasis setup
    make
    ```
    
## Step by Step Instructions

### Knotical's command-line options

- `-cmp` or `cmpLt`: Find the trace refinement relations of the two methods for equality (`cmp`) or refinement (`cmpLt`)
- `-no-rem`: Specify the list of events/methods that cannot be removed or replaced
- `-depth`: Specify the depth of proof search

### Running a single example

- For instance, the following command line runs the tool Knotical on the motivating example (`bench/01sendrecv.c`) to find trace refinement relations under which the first method `C2` *refines* the second method `C1`, given that the methods `send`, `recv`, and `constructReply` aren't removed

    ```
    ./knotical.native -cmpLt C2 C1 -no-rem send,recv,constructReply bench/01sendrecv.c
    ```
    
- The result contains multiple refinement relations represented in the form of trees. A solution tree is *complete* (`C`) or *partial* (`P`) in the sense that whether or not different restrictions in its refinement relations applied to the input methods, when taken together cover all behaviors of the first method (in case of `cmpLt`) or both (in case of `cmp`). For example, the following solution tree is one of the results returned by Knotical for the motivating example. It is a *complete* solution because there are refinement relations corresponding to all cases in the first method `C2` (marked by `@1`).

    ```
    (C) d_30@2: 
     |_  d_30@2
      (C) b_12@1: 
       |_  b_12@1
         |_ (A) {I=1, J=1, K=1, M=1}
           GenAxiom {I=1} {I: ((L37 C9), () = log(b);)}
        -> Case d_30 {d: ((L14 C13), c > 0)}
        -> GenAxiom {J=1} {J: ((L14 C13), () = log(b);)}
        -> Case b_12 {b: ((L32 C18), auth > 0)}
        -> GenAxiom {K=1} {K: ((L19 C15), () = log(n);)}
        -> GenAxiom {M=1} {M: ((L30 C10), auth = check(b);)}
        -> (a_8.V_16.(c_15.M_57.C_11.S_10 + !c_15.I_33).X_9)*.!a_8 <= (a_22.V_31.J_34.(c_28.C_27.S_26.K_56 + !c_28).X_23)*.!a_22
       |_  !b_12@1
        (C) c_28@2: 
         |_  c_28@2: No solutions
         |_  !c_28@2
           |_ (A) {I=1, J=1, K=1}
           GenAxiom {I=1} {I: ((L37 C9), () = log(b);)}
        -> Case d_30 {d: ((L14 C13), c > 0)}
        -> GenAxiom {J=1} {J: ((L14 C13), () = log(b);)}
        -> Case !b_12 {b: ((L32 C18), auth > 0)}
        -> Case !c_28 {c: ((L16 C13), b > 0)}
        -> GenAxiom {K=1} {K: ((L30 C10), auth = check(b);)}
        -> (a_8.V_16.(c_15.K_61 + !c_15.I_33).X_9)*.!a_8 <= (a_22.V_31.J_34.X_23)*.!a_22
     |_  !d_30@2
       ...
    ```
    
    The first refinement relation shows that when `log` are removed in both methods and the authorization `auth` in `C2` is always successful then `C2` *refines* `C1`.

### Running the benchmarks

- To reproduce the entire experiment on the 37 benchmark programs in `bench`, run 

    ```
    bin/runAll.sh
    ```

- The experimental result is in the folder `results-YYYYMMDD-hhmmss` where `YYYYMMDD-hhmmss` is the timestamp when the script was run. The file `results-YYYYMMDD-hhmmss/SUMMARY.html` represents the summary result (Table 1 in the paper) in HTML format.
