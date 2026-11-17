# Portable commands and retained path literals

Release commands resolve the repository from their script location. The cold
driver takes `--input-dir`, `--report-dir`, `--jobs`, and `--memory-gb` arguments.
Its default input parent is `data/` in the repository; its default report directory
is a sibling named `<checkout-name>-verification`. Reports are outside the source
tree so temporary comparison modules never become repository sources. The driver
uses the pinned dependency revisions and requires an explicit official-verifier
checkout through `--verifier` or `PALOMAR_VERIFIER`.

H3 production commands always set both `H3_INPUT_DIR` and `H3_REPORT_DIR`; all
published examples do so. The original absolute defaults remain byte-identical
inside the receipt-pinned H3 programs. The historical planning and merge-check
programs are not release build entry points.

The incoming H1 interface uses `H1_REGEN_REPORT` for reports, but several inspected
exporters and the input-receipt command still use literal input locations.
`H1_INPUT_DIR` does not override those versions. The cold driver's explicit H1
adapter contract is documented in `regeneration/H1-INTEGRATION.md`; its named
integration field is completed against the final hand-back. The current driver
fails before starting any build when that adapter is absent. This avoids relying
on a machine-specific data mount or claiming that an unused variable works.
No receipt-pinned H1 tool is changed by the layout commit.

`verification/layout/absolute-paths.tsv.gz` lists every distinct absolute path
literal by file and line, with a reason. It includes compressed historical
reports and excludes the inventory itself to avoid recursive duplication.
Read it with `gzip -dc verification/layout/absolute-paths.tsv.gz`.
Machine-specific entries fall into these categories:

- Retained H1/H3 runner defaults and historical tools: kept byte-identical to
  preserve active build contexts; H3 defaults have documented overrides, and H1
  has the explicit adapter completion field.
- Two unchanged Lean comments: historical diagnostic references, not imports or
  build inputs. The hard constraint prohibits even comment edits in Lean files.
- Historical verification receipts and verbatim review/study reports: paths
  identify the environment actually measured. They are evidence, not commands
  or required release paths, and are not rewritten as results for another tree.
- Standard Linux/tool paths such as `/proc`, `/usr/bin/time`, `/dev/null`, and
  sandbox `/tmp`: runtime interfaces or executable locations, not a particular
  user's checkout. User-selected data, report, verifier, and bubblewrap paths
  are explicit arguments.

The manuscript is unedited; any original citation or spelling convention is
preserved. Exact external Lean names, paper labels, and input-data keys are
likewise preserved. The explanatory prose and new verification commands use
American English.

Regenerate the inventory after a source hand-back with
`python3 scripts/path_inventory.py`. It reads tracked files and does not edit
runner sources, receipts, or interface inventories.
