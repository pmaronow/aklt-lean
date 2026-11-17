#!/usr/bin/env python3
"""Fill the @@R_*@@ fields of the drafted VERIFICATION.md from the regression receipt.

usage: fill_regression.py RECEIPT_JSON DRAFT_MD OUTPUT_MD
Refuses to write unless the receipt records acceptance by every kernel.
"""
import json, re, sys

d = json.load(open(sys.argv[1])); s = open(sys.argv[2]).read()
st = {x['stage']: x for x in d['stages']}
assert d['status'] == 'all-mechanical-components-pass', d['status']
assert d['mandatory_kernels_accept'] is True and d['conron_accept'] is True
assert d['verification_surface'] == 'two-input regression' and d['dirty'] is False
for name, x in st.items():
    assert x['exit_code'] == 0 or name == 'source-configuration', (name, x['exit_code'])
assert [f['code'] for f in d['author_metadata_findings']] == ['package.metadata_todo', 'package.license_missing']
m = re.search(r'accepted (\d+) declarations \(--verified\)', d['conron_outcome']['detail'])
gib = lambda b: f'{b / 2**30:.3f}'
cpu = lambda x: x['cpu_s'] if x['cpu_s'] > x['sampled_tree_cpu_s'] else x['sampled_tree_cpu_s']
b, e, c, k = st['default-build'], st['solution-export'], st['protected-comparator'], st['conron-replay']
values = {
 'R_BUILD_WALL': f"{b['wall_s']:.1f}", 'R_BUILD_CPUH': f"{cpu(b) / 3600:.3f}", 'R_BUILD_RSS': gib(b['peak_tree_rss_bytes']),
 'R_EXPORT_DECLS': f"{int(m.group(1)):,}", 'R_EXPORT_BYTES': f"{d['solution_export']['bytes']:,}", 'R_EXPORT_SHA': d['solution_export']['sha256'],
 'R_EXPORT_WALL': f"{e['wall_s']:.1f}", 'R_EXPORT_CPU': f"{cpu(e):.1f}", 'R_EXPORT_RSS': gib(e['peak_tree_rss_bytes']),
 'R_COMP_WALL': f"{c['wall_s']:.1f}", 'R_COMP_CPU': f"{cpu(c):.1f}", 'R_COMP_RSS': gib(c['peak_tree_rss_bytes']),
 'R_CONRON_WALL': f"{k['wall_s']:.1f}", 'R_CONRON_CPU': f"{cpu(k):.1f}", 'R_CONRON_RSS': gib(k['peak_tree_rss_bytes']),
}
for key, value in values.items():
    assert s.count('@@' + key + '@@') == 1, key
    s = s.replace('@@' + key + '@@', value)
assert '@@' not in s
open(sys.argv[3], 'w').write(s)
print(json.dumps({**values, 'source_commit': d['source_commit'], 'conron': d['conron_outcome']['detail'][:80]}, indent=1))
