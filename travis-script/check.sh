#!/bin/bash
set -o pipefail # so that Bash will report the failure of type checking
stack exec agda -- --library-file=travis-script/libraries --without-K --rewriting "$@" | ts
