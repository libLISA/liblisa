#! /bin/bash

# Usage: crates.io_version_check.sh liblisa || cargo publish ...

PROJECT=$1
LOCAL_VERSION=$(cargo tree -p liblisa | head -n 1 | cut -d ' ' -f2 | tail -c +2)

echo "Checking version $LOCAL_VERSION"

if curl https://crates.io/api/v1/crates/$PROJECT | jq --arg local_version "$LOCAL_VERSION" '.versions | any(.num == $local_version)' | grep true; then
    exit 0
else
    exit 1
fi