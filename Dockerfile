FROM ubuntu:19.04

RUN apt-get update -y && \
    apt-get install -y g++ cmake make libboost-dev libboost-program-options-dev libboost-filesystem-dev libboost-iostreams-dev zlib1g-dev openjdk-12-jdk less unzip graphviz vim curl wget python3 python3-distutils

RUN curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py && \
    python3 get-pip.py && \
    pip install ipython

RUN wget https://strix.model.in.tum.de/files/strix-19.07.zip && \
    unzip strix-19.07.zip

WORKDIR strix

RUN make
