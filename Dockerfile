FROM avta/knotical-core

COPY . /knotical

WORKDIR /knotical

RUN \
  svn checkout https://scm.gforge.inria.fr/anonscm/svn/bjeannet/pkg/interproc/ deps/interproc && \
  wget https://perso.ens-lyon.fr/damien.pous/symbolickat/symkat-1.4.tgz && \
  tar -xf symkat-1.4.tgz --directory deps/

RUN \
    eval `opam config env` && \
    oasis setup && \
    make