import AKLT.Gen.Bellman.Basic
import AKLT.Gen.Bellman.Extension
import AKLT.Gen.Bellman.Quotient
import AKLT.Gen.Bellman.Growth
import AKLT.Gen.Bellman.Certificates

/-!
# Generic Bellman and automaton path-sum theory

Import this module for the complete generic API in `AKLT.Gen.Bellman`.

* `System.stopped_total_le`: first-hit path-sum soundness, arbitrary label and state types.
* `local_global`, `local_global_total_le`: finite modifications controlled by free rows.
* `Automaton.quotient_compatible`, `Automaton.stopped_total_pullback`: exact labelled lumping.
* `all_length_path_bound`, `alm`: positive-vector growth and the finite-prefix constant.
* `scaled_ennreal_row_sound`: natural-number row checks imply exact scaled inequalities.

Concrete applications must prove their transition and reward definitions, quotient compatibility
(including arrival-dependent coefficients), per-edge outside domination, finite row checks and
caps, terminal support, and true-path/prefix domination. This library contains no such data and
does not assert that a numerical certificate passes.
-/
