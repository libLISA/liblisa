#! /bin/bash

if [ -z "$RELEASE_ID" ]; then
    RELEASE_ID=$(jq --raw-output '.release.id' "$GITHUB_EVENT_PATH")
    echo "Discovered RELEASE_ID: $RELEASE_ID"
fi
 
if ! curl \
    -v \
    -sSL \
    -XPOST \
    -H "Authorization: token $GITHUB_TOKEN" \
    -H "Content-Type: application/octet-stream" \
    --upload-file "$FILE" \
    --fail \
    "https://uploads.github.com/repos/$GITHUB_REPOSITORY/releases/$RELEASE_ID/assets?name=$FILENAME";
then
    exit 1
fi