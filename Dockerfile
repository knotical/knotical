FROM avta/knotical-core:opam_2_0

COPY . /knotical

WORKDIR /knotical

RUN \
    eval `opam config env` && \
    oasis setup && \
    make
