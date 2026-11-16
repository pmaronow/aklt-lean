#!/bin/bash
# wait-file.sh PATH [MAX_SECONDS]: exit 0 when PATH exists, 1 on timeout.
for i in $(seq 1 $(( ${2:-7200} / 20 ))); do [ -e "$1" ] && exit 0; sleep 20; done; exit 1
