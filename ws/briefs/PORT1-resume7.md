Orchestrator message — urgent performance fix (tools v6). The production campaign has 431 leaves to register and
`aklt-ladder add` takes ~3–6 minutes per leaf: it creates a fresh MERGE_REG worktree and runs
`lake build +Module:olean` module by module over the node's whole dependency closure, with a `du` budget scan
around each step. At that rate registration alone takes a day. Required changes:
1. `aklt-ladder add-many FILE.json` (a JSON list of the usual leaf objects): ONE detached worktree at `validated`,
   ONE build of the union of statement modules (a single `lake build` invocation with all targets), ONE generated
   Lean file that performs the node check for every leaf (frozen nullary `def : Prop`, deps), then creation of the
   writer worktrees and queue/ladder entries for all leaves that pass; leaves that fail are reported individually
   and do not block the others. Same semantics and state as repeated `add`. Target: 431 leaves in a few minutes.
2. Writer worktrees (`KEY_L`, `KEY_S`) and integration/registration worktrees start from a SEEDED build instead of
   an empty `.lake/build`: maintain one prebuilt full build per validated commit under
   `~/aklt/state/build-seed/<commit>/` (built once, by the tools, outside any agent sandbox) and copy it into each
   new worktree (`cp -a --reflink=auto`; about 1.3 GB, seconds), so that a writer only compiles its own files. Lake's
   artifact cache (`LAKE_ARTIFACT_CACHE=true`, cache under the toolchain's `lake/cache`) works on this toolchain
   and may be used by tool-side builds (it cut a fresh-worktree build from 52 s to 8 s); agents' sandboxes cannot
   write that cache, so do not rely on it for agents. The cleaner must delete seeded builds of finished tasks as
   before.
3. Do the disk-budget `du` at most once per command (or cache it for 60 s).
A slow `register_leaves.py` run using `aklt-ladder add` is in progress right now (it holds `ladder.lock`
intermittently; 3 leaves registered so far; loops are NOT running). Develop and test in scratch; when v6 is ready,
install it (v1–v5 kept, dispatcher repointed, operator disk policy and all state preserved), and tell me in the
report exactly how to (a) stop the slow registration safely and (b) run `add-many`. Add tests (add-many equals
repeated add on a fixture; a failing leaf does not block others; seeded worktree builds only the new file; cleaner
removes seeded builds). Report section "resume7" + ORCH-SUMMARY. No daemons or agents.
