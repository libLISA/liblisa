FROM ghcr.io/cross-rs/aarch64-unknown-linux-gnu:main

RUN dpkg --add-architecture arm64 && \
    apt-get update && \
    apt-get install --assume-yes 'libclang-*-dev' libz3-dev libz3-dev:arm64 clang python3