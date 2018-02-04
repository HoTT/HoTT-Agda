#!/bin/bash
for DIR in core theorems; do
  mkdir -p $HOME/agdai-backup/$DIR
  rsync -avc $HOME/agdai-backup/$DIR/ $DIR --filter "+ */" --filter "+ *.agdai" --filter "- *"
done
