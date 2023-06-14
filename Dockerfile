FROM ubuntu:bionic

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y g++ cmake libgmp-dev emacs python3 python git ccache python3-pip
RUN pip3 install matplotlib

RUN mkdir -p /paper /paper/pureptr
WORKDIR /paper

COPY lean4-ICFP20.tar.gz lean4-ICFP20.tar.gz
RUN tar -xzvf lean4-ICFP20.tar.gz
WORKDIR /paper/lean4-ICFP20
RUN mkdir build
WORKDIR /paper/lean4-ICFP20/build
RUN cmake ../src
RUN LEAN_PATH=Init=/paper/lean4-ICFP20/src/Init make -j8

WORKDIR /paper/pureptr
COPY Makefile Makefile
COPY relative.py relative.py
COPY Paper.lean Paper.lean
COPY run_term_experiment.py run_term_experiment.py

ENV LEAN_ROOT=/paper/lean4-ICFP20
ENV LEAN_PATH=Init=$LEAN_ROOT/src/Init:PurePtr=/paper/pureptr

RUN make
RUN make dump_out

## Note: takes several minutes
RUN python3 run_term_experiment.py --n_high 1000 --n_inc 1.15 --timeout 20 --n_runs 1
