FROM avta/knotical-core

COPY . /knotical

WORKDIR /knotical

RUN \
    eval `opam config env` && \
    oasis setup && \
    make