Orchestrator message (not tampering): I stopped your run and resumed it with a narrower sandbox, on purpose. Your
working directory is now /home/ubuntu/aklt/scratch/PORT1 and your writable roots are only that directory plus
/home/ubuntu/aklt/tools, /home/ubuntu/aklt/bin, /home/ubuntu/aklt/state and /home/ubuntu/aklt/reports/PORT1.
Everything else (the main repo /home/ubuntu/aklt/repo, other worktrees, logs, other campaigns) is read-only for you,
as your brief intended. For tests, clone the repo into scratch (git clone --shared or a plain clone; link Mathlib
packages from /home/ubuntu/aklt/repo/.lake/packages with a symlink, never modify them); write test logs under
scratch. Use /home/ubuntu/aklt/bin/sol-retry.py and luna-retry.py as the retry wrappers to adapt (they now write
continuation prompts to ~/aklt/scratch/retry/<model>-<session>-<n>.md). Continue the task from where you stopped;
the deliverable (/home/ubuntu/aklt/reports/PORT1/report.md and tools/v1) and all rules in /home/ubuntu/aklt/briefs/PORT1.md are unchanged.
