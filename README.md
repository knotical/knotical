# Knotical: An Inference System of Trace Refinement Relations

## Getting Started Guide

### Using Docker

1. Install Docker. Follow the instructions on https://docs.docker.com/install/.

1. Build the Knotical image:

    ```
    docker build -t knotical .
    ```

1. Run the Knotical image:

    ```
    docker run -it knotical bash
    ```
    
### Installation on Ubuntu from scratch

1. Install Prerequisites:

    ```
    apt-get clean
    apt-get update
    apt-get install -qy libppl-dev libmpfr-dev m4 opam subversion
    ```
    
 1. Install OCaml compiler and Dependencies via `opam`:
 
    ```
    opam init
    opam switch 4.06.1
    eval `opam config env`
    opam install oasis ocamlbuild
    opam install apron conf-ppl camllib safa batteries camlp4 core ocamlgraph
    eval `opam config env`
    ```
    
1. Install `Fixpoint`:
  
    ```
    svn checkout https://scm.gforge.inria.fr/anonscm/svn/bjeannet/pkg/fixpoint/
    cd fixpoint/trunk/
    cp Makefile.config.model Makefile.config
    make
    make install
    ```

1. Compile Knotical:
   
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

- For instance, the following command line runs the tool Knotical over the motivating example (`bench/01sendrecv.c`) to find trace refinement relations under which the *first* method `C2` strictly refines the *second* method `C1`, given that the methods `send`, `recv`, and `constructReply` aren't removed

    ```
    ./knotical.native -cmpLt C2 C1 -no-rem send,recv,constructReply bench/01sendrecv.c
    ```
    
- The result contains multiple refinement relations represented in the form of trees. A solution tree is *complete* or *partial* in the sense that whether or not different restrictions in its refinement relations applied to the input methods, when taken together cover all behaviors of the first method (in case of `cmpLt`) or both (in case of `cmp`).

### Running the benchmarks
