#!/bin/bash
# log.sh "text": append a RESUME.md entry stamped with the real UTC time.
printf '\n- %s UTC — %s\n' "$(date -u +%H:%M)" "$*" >> ~/aklt-lean/RESUME.md
