FROM debian:stretch

RUN echo deb http://archive.debian.org/debian stretch-backports main | tee -a /etc/apt/sources.list.d/stretch-backports.list
RUN echo deb http://archive.debian.org/debian stretch-backports-sloppy main | tee -a /etc/apt/sources.list.d/stretch-backports-sloppy.list
RUN echo "deb http://archive.debian.org/debian stretch main contrib non-free" > /etc/apt/sources.list
RUN apt-get update && apt-get upgrade -y
RUN apt-get update && apt-get install -y git curl clang build-essential python3 linux-headers-amd64 libc6-dev libclang-dev cmake pkg-config unicorn libclang-5.0 libclang-5.0-dev llvm-dev z3 libz3-dev
RUN apt-get update && apt-get -t stretch-backports-sloppy install -y libarchive13
RUN apt-get update && apt-get -t stretch-backports install -y cmake
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly-2024-03-06
RUN $HOME/.cargo/bin/rustup component add rust-src --toolchain nightly-2024-03-06-x86_64-unknown-linux-gnu
RUN $HOME/.cargo/bin/rustup component add llvm-tools-preview --toolchain nightly-2024-03-06-x86_64-unknown-linux-gnu

RUN apt-get update && apt-get install -y git g++

ENV CARGO_HOME /out/.cargo

CMD ["/bin/bash", "-c", "source $HOME/.cargo/env && cd /files && source ~/.bashrc && cargo build --release --bin liblisa-x64 --target-dir /out"]