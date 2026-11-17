STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM019/AKLT/W/MOM019/Main.lean)

## Exported declarations

- `AKLT.W.MOM019.main : AKLT.Blueprint.Mom.TripleNumeratorStatement`.
- `phi_sq : goldenRatio ^ 2 = goldenRatio + 1`, `radius_sq : icoRadius ^ 2 = goldenRatio + 2`, `radius_ne : icoRadius ≠ 0`, `phi_fourth : goldenRatio ^ 4 = 3 * goldenRatio + 2`, and `radius_fourth : icoRadius ^ 4 = 5 * (goldenRatio + 1)`.
- `ico_first : ∀ i, moment (fun v => v i) = 0` and `ico_third : ∀ i j k, moment (fun v => v i * v j * v k) = 0`.
- `ico_second : ∀ i j, moment (fun v => v i * v j) = if i = j then 1 / 3 else 0`.
- `ico_fourth : ∀ i j k l, moment (fun v => v i * v j * v k * v l) = ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / 15`.
- `ico_tensor_law : TensorLaw moment 1`.
- `moment_sum : moment (fun v => ∑ x, f x v) = ∑ x, moment (f x)`, `moment_const_mul : moment (fun v => c * f v) = c * moment f`, and `moment_add : moment (fun v => f v + g v) = moment f + moment g`.
- `moment_linear_dot : moment (fun v => v i * dot v a) = a i / 3`; `moment_linear_dot_pair : moment (fun v => v i * dot v a * dot v b) = 0`; `moment_linear_dot_triple : moment (fun v => v i * dot v a * dot v b * dot v c) = (a i * dot b c + b i * dot a c + c i * dot a b) / 15`.
- `moment_local_triple` states that `moment (fun v => v i * localProduct a v)` equals `(a 0 i + a 1 i + a 2 i) / 3 + (a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) + a 2 i * dot (a 0) (a 1)) / 15`.

## Axioms

`#print axioms` was run for `main` and every helper lemma listed above; each reported:

```text
'AKLT.W.MOM019.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.MOM019.Main` — succeeded in 66 seconds.
- Axiom audit: `lake env lean /tmp/MOM019_Audit.lean` — succeeded in 5.5 seconds.

## Open issues and limitations

- None. The explicit fourth-tensor coordinate enumeration uses a local heartbeat cap of `1000000`; no forbidden proof placeholders or axioms were introduced.

## ORCH-SUMMARY

- Delivered `AKLT.W.MOM019.main` with the exact requested statement.
- The proof expands the three factors and contracts the second and fourth moments of the finite U law.
- The requested Lake build succeeds; theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No open issues. The fourth-tensor enumeration has a local heartbeat cap of `1000000`.
