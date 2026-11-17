# Release artifacts and numeric inputs

Release tag: **TBD-RELEASE-TAG**. Download the numeric input archives, generated-source
archives, and receipt bundles attached to that release of this repository. Extract
numeric inputs as `data/h1/` and `data/h3/` under the repository, or pass their common
parent with `--input-dir`. These archives are excluded from Git. Generated Lean
sources are proof inputs, not trusted compiled objects; the Lean kernel checks
their proofs during compilation.

## Numeric input pins

H1 consists of an index and sixteen compressed integer-witness chunks. The pins
below are copied from the index used by the H1 exporters; the index itself is
pinned independently. See `verification/inputs/H1.json`. H3 uses five compressed
stationary arrays and one finite-window quotient table, pinned by
`AKLT/Cert/H3/inputs.json`. The combined input size is 2,608,431,187 bytes.

| Family / file | Bytes | SHA-256 |
|---|---:|---|
| `h1/index.json` | 5,227 | `6451c08de041cbf8def4a6c87e6b45b23e17a1152eab4917b7836aaeb19a66f7` |
| `h1/chunks/patterns-0000-0499.jsonl.gz` | 276,235 | `dbb56f1aa779c2d32a9256bedbe6ac42208ae911447bdb4dde6f8d8fb8087a9a` |
| `h1/chunks/patterns-0500-0999.jsonl.gz` | 1,847,486 | `d29299ebde7832bd17397bf3d94e90f2ebf99fa8bb75ff30ad267019a1a05d9b` |
| `h1/chunks/patterns-1000-1499.jsonl.gz` | 1,297,267 | `8b5609a61c554a237f9ac50b4c67254955049c31581efb3e8eb774f4cde4de4c` |
| `h1/chunks/patterns-1500-1999.jsonl.gz` | 200,758 | `93b8080b677fbf59d86ea172a3984470b79cccf2deecccaf5805fae5cb4df5e9` |
| `h1/chunks/patterns-2000-2499.jsonl.gz` | 403,673 | `fa930b4694645add72151f0775ca87c5627979c99a3b859b6353a445d764a4b5` |
| `h1/chunks/patterns-2500-2999.jsonl.gz` | 277,111 | `776b1662df39b1f2d51c2ab30a0f6732c47dbf5dc5403d6f6df762bb19907594` |
| `h1/chunks/patterns-3000-3499.jsonl.gz` | 1,590,385 | `9ce86b9d6eb6c76eb731b04d4dfcb8c64286a7c937019429158e22f1d492c600` |
| `h1/chunks/patterns-3500-3999.jsonl.gz` | 498,355 | `c1335f3f4c8f67914c19a4ccca5497a7bcf6185daa20814b41da2f3e5fbc4482` |
| `h1/chunks/patterns-4000-4499.jsonl.gz` | 272,935 | `7d5baca5341c69b36e2963d1d6fa0e9adce792ee1d555878af176b184f128545` |
| `h1/chunks/patterns-4500-4999.jsonl.gz` | 1,986,079 | `4eda2e203e089f36639e7bc9a974e7fac22556aa44b2ec6e0f9ce3dfed2d9650` |
| `h1/chunks/patterns-5000-5499.jsonl.gz` | 1,021,171 | `83a850cff5944ec6405c7fa1f91d4e452b9c1ec0079318f006fba688698247d8` |
| `h1/chunks/patterns-5500-5999.jsonl.gz` | 248,001 | `684f3c77c337b4483cb01f5fbb288abe02740167dff31db80c18be7364def665` |
| `h1/chunks/patterns-6000-6499.jsonl.gz` | 284,283 | `a8c5c77768e69a3cdc32484315696e795d261f5c82de229cf5760078331398ac` |
| `h1/chunks/patterns-6500-6999.jsonl.gz` | 335,857 | `8fcb3de6e837be4cc6950ca531a5d1bd8345331f04c0c67b6d8972ea34c605af` |
| `h1/chunks/patterns-7000-7499.jsonl.gz` | 1,348,115 | `ebca2f81acf041ccb8dfa1e5b4c4ed815f34651fd11ff266db12aeabe16b7164` |
| `h1/chunks/patterns-7500-7961.jsonl.gz` | 445,826 | `097e5cc010c74f41558c8d0abfc5fda39c821d4d086894fc3c047d32b16568f7` |
| `h3/stationary_B_m10_R70_d1_coarse.bin.gz` | 519,220,825 | `3bdc2f5cfe54b15548ccf4b40384ab9585938385bb7860cf94ad1706239293a2` |
| `h3/stationary_B_m10_R70_d2_coarse.bin.gz` | 519,332,467 | `6303cba2e5ae59f1ba80ba52b2017a243e362a2ccea44ca776f04e166b8a679b` |
| `h3/stationary_C_m10_R70_d1_coarse.bin.gz` | 518,111,962 | `2aabb88c464f3c3181fa92300548d6ea466321fccab09d32b654b8f0a07a8a6f` |
| `h3/stationary_C_m10_R70_d2_coarse.bin.gz` | 519,265,291 | `0f75d0d12cc3d1c75f18fe68f7f81e78792ef671eda85688c2538ff9c35f352b` |
| `h3/stationary_C_m10_R70_d3_coarse.bin.gz` | 519,388,981 | `6f709cca42dc57a5e52755767eea6af9e6527804661699a4e37f8796ede020e7` |
| `h3/windows_m10_min.txt` | 772,897 | `671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785` |

H1 index provenance also lists support files, original Python programs, and
operator-construction inputs. The release exporters consume the index and
sixteen chunks above; the auxiliary files do not enter that regeneration route.

## Generated-source archives

| Family | Modules | Archive | Bytes | SHA-256 |
|---|---:|---|---:|---|
| H1 | 7,964 | `H1-module-sources.tar.gz` | 25,987,925 | `a27c7dc50ccf88bf53ddeb1d739764eebe623c763bc31ec3f34fd521af9c543f` |
| H3 | 5,032 | `H3-modules.tar.gz` | 4,168,219,365 | `4eab44fec523c00dc6f6c620eb74d25b47077c67b67c23da582440fa0710f60f` |

These are the pinned source-only archives. **TBD-RELEASE-ARCHIVE-PINS**:
confirm the published archives retain these exact bytes; otherwise record the
published names, sizes, and hashes here. No `.olean` is part of these archives.

Install each archive into a checkout with no generated sources:

```sh
python3 scripts/install_certificates.py \
  --archive data/H3-modules.tar.gz \
  --sha256 4eab44fec523c00dc6f6c620eb74d25b47077c67b67c23da582440fa0710f60f
python3 scripts/install_certificates.py \
  --archive data/H1-module-sources.tar.gz \
  --sha256 a27c7dc50ccf88bf53ddeb1d739764eebe623c763bc31ec3f34fd521af9c543f
```

The exact allowed generated paths are in `verification/generated-modules.json`.
The installer refuses unexpected paths, duplicate entries, symlinks, archive
escapes, hash mismatches, and overwriting an existing source. Numeric generation
with `scripts/cold-verify.sh` provides a separate route from the pinned inputs.

## Certificate documentation

[H1](regeneration/H1.md) and [H3](regeneration/H3.md) describe the two families,
commands, measurements, resource requirements, and receipts. Their tooling notes
are [H1 changes](regeneration/H1-CHANGES.md) and
[H3 changes](regeneration/H3-CHANGES.md). The shared API note is
`docs/REGEN-INTERFACE.md`; machine-readable interfaces remain under
`verification/regen-interface/`.

The release assets include runner manifests, input pins, source hashes, compiled
artifact hashes, per-module timing and axiom logs, and closing receipts.
`VERIFICATION.md` identifies the combined Lean source digest and final results.
