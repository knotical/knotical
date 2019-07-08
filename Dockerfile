FROM avta/knotical-core:latest

COPY . /knotical

WORKDIR /knotical

RUN \
    eval `opam config env` && \
    oasis setup && \
    make