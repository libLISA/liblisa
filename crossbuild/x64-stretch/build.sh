#! /bin/bash

docker build -t liblisa-crossbuild crossbuild/x64-stretch/docker && \
docker run --mount src=`pwd`,target=/files,type=bind \
    --mount src=/usr/include,target=/usr/include,type=bind \
    --mount src=`readlink -f ./crossbuild/x64-stretch/out`,target=/out,type=bind liblisa-