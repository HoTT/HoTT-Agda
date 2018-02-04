#!/bin/bash
mkdir -p $HOME/agdai-backup
for DIR in core theorems; do
  rsync -avc $DIR/ $HOME/agdai-backup/$DIR --filter "+ */" --filter "+ *.agdai" --filter "- *"
done
