from pathlib import Path
p=Path('/home/ubuntu/aklt/reports/REL_FEAS/final_report.py');s=p.read_text()
a='### Converted 64-plane sample: multiplication versus shifts'
b="""### Minimal kernel-memory failure and a statement-preserving repair

The standalone **RELFEAS.MulOrderOOM** example uses only Init:

    def large : Nat := 2^2097152 - 1
    def expected : Nat := (Nat.shiftLeft 97632666219444 2097152) - 97632666219444
    theorem small_first : 97632666219444 * large = expected := by decide +kernel
    theorem large_first : large * 97632666219444 = expected := by decide +kernel

Lean checks both in 0.30 s / 0.287 GiB. No giant decimal literal is present in the export: the large integer is represented by the short power expression. This separates kernel normalization from the earlier reader bottleneck.

| Proof/export root | con-ron s / GiB | con-ron outcome | NanoDa s / GiB | NanoDa outcome |
|---|---:|---|---:|---|
| small_first, direct computation | 9.55 / 4.052 | RSS_CAP at 4 GiB; no acceptance | 0.10 / 0.002 | ACCEPT |
| large_first, direct computation | 2.92 / 0.043 | ACCEPT | 0.10 / 0.002 | ACCEPT |
| Same small-first statement, explicit commutation | 4.62 / 0.043 | ACCEPT | 0.10 / 0.001 | ACCEPT |

The repaired declaration **RELFEAS.MulOrderOOMReformulated.checked** keeps the original small-first equality:

    theorem checked : 97632666219444 * large = expected :=
      Eq.trans (Nat.mul_comm _ _) large_first

Its Lean build takes 0.20 s / 0.272 GiB; all these theorem audits report no axioms. Checker progress places the capped run in the theorem's check phase. The failed export and successful reformulation have the same mathematical target, with explicit equality transport replacing conversion of the expensive product. A smaller 786,432-bit control shows the same asymmetry without hitting its cap: 2.21 s / 1.688 GiB versus 0.61 s / 0.043 GiB. Reproduction drivers are mul_order_oom.py and mul_reformulate_oom.py; all files remain under this report.

This directly identifies a **large-Nat multiplication operand-order / normalization hazard**. It does not establish that every Nat.rec or bitwise operation is intrinsically slow. In particular, the original full B1 row runs did not reach a reported kernel check, so this is a separate isolated hazard, corroborated on real data by the lane evidence below.

"""+a
assert a in s;s=s.replace(a,b)
s=s.replace('A complete converted three-row export is being tested', 'A complete converted three-row export was attempted')
s=s.replace('Corrected V2 full converted group: capped experiment is running; no full-catalog shift acceptance is claimed.', 'Corrected V2 full converted group: no complete export or checker acceptance was obtained.')
lines=s.splitlines()
for i,line in enumerate(lines):
 if "s+=f'| nested shift rewrite V2 |" in line:
  lines[i]=r""" s+=f'| nested shift rewrite V2 | {val(d.get("export"))} {verdict(d.get("export"))} | NOT RUN: export failed | NOT RUN: export failed |\n'"""
s='\n'.join(lines)+'\n'
a='### Comparator measurements and the serial kernel gate'
b="""The V2 exporter hit its **2,400-second / 20 GiB** limit, with sampled peak 9.154 GiB, before completing the environment. Its partial histogram contains 531,397 2,000–2,999-digit leaves and maximum 2,467 digits, confirming the nested rewrite operated on the emitted prefix. This is an expensive post-processing prototype, not a validated complete-case source encoding. No independent checker was run on the incomplete file. The successful small-source encoding controls cannot be extrapolated to a complete new release without the fresh consumer pilot.

"""+a
assert a in s;s=s.replace(a,b)
a='1. **Use the native, balanced decimal serializer immediately.**'
b="""1. **Put the large operand first in computed Nat products, and transport the original statement explicitly.** On the standalone example above, direct small-first computation reaches 4 GiB without acceptance; the same statement proved using Nat.mul_comm and the large-first computation ACCEPTS at 0.043 GiB. The H3 lane's real multiplication and complete-row controls corroborate the improvement. For a packed checker, introduce an internal large-first variant; prove its weighted-list sum equals the old sum by list induction and Nat.mul_comm, lift that equality through the Boolean checker, and generate the old checked statement using an equality chain ending in decide +kernel on the new variant. Retain all bounds and the old public statement. The generic equivalence is still proof work for the lane; Fit.SwapSound is not yet proved.
2. **Use the native, balanced decimal serializer immediately.**"""
assert a in s;s=s.replace(a,b)
s=s.replace('2. **Pilot balanced add/shift encoding', '3. **Pilot balanced add/shift encoding')
s=s.replace('3. **Resolve the sequential replay', '4. **Resolve the sequential replay')
s=s.replace('4. **If the author accepts', '5. **If the author accepts')
s=s.replace('5. **Higher-cost proof-format work:**', '6. **Higher-cost proof-format work:**')
s=s.replace('release-test-top-final/receipt.json; final runner SHA matches delivery. Clean source build, scan, audit, rebuilt fast exporter, both checkers and sandboxed three-kernel Comparator. con-ron 36.14 s, NanoDa 11.94 s, Comparator 82.82 s. Earlier stock-exporter run also passed.', 'release-test-top-delivered/receipt.json; final runner SHA matches delivery. Clean source build, scan, audit, rebuilt fast exporter, both checkers and sandboxed three-kernel Comparator. con-ron 23.59 s, NanoDa 5.85 s, Comparator 59.19 s. Earlier stock-exporter run also passed.')
s=s.replace('release-test-final/receipt.json; includes attachment inventory, source/artifact hashes and library registration. con-ron 10.33 s, NanoDa 0.10 s, three-kernel Comparator 10.73 s.', 'release-test-attachment-delivered/receipt.json; final runner SHA matches delivery; attachment inventory, source/artifact hashes and library registration. con-ron 6.05 s, NanoDa 0.10 s, three-kernel Comparator 6.35 s.')
s=s.replace('- Full converted row experiment is separate from original-byte acceptance and remains explicitly labeled.', '- Full nested re-encoding export TIMEOUT at 40 min; no complete converted row-group checker acceptance.')
s=s.replace('- Stock huge Nat decimal export/parse is a measured bottleneck; minimal reflexive example and exact logs delivered.', '- Minimal small-first Nat.mul hits 4 GiB; an explicit Nat.mul_comm proof of the same statement ACCEPTS at 43 MiB.\\n- Stock huge Nat decimal export/parse is a measured bottleneck; minimal reflexive example and exact logs delivered.')
s=s.replace('The new auxiliary closed statements are combine_eq and rebuild_eq above,', 'The new auxiliary closed statements are the MulOrder/explicit commutation examples, combine_eq and rebuild_eq above,')
p.write_text(s)
