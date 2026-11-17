module
public import AKLT.Blueprint.Mom.NodesMoments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.MOM001

open AKLT.Defs

private def icoNumerator (j : IcoLetter) : Vec3 :=
  let a := signValue j.2.1
  let b := signValue j.2.2 * goldenRatio
  if j.1 = 0 then ![0, a, b]
  else if j.1 = 1 then ![a, b, 0] else ![b, 0, a]

private theorem icoVector_eq_div (j : IcoLetter) :
    icoVector j = fun i => icoNumerator j i / icoRadius := rfl

theorem main : AKLT.Blueprint.Mom.IcoInjectivityStatement := by
  intro j k h
  have hphi : 0 < goldenRatio := by
    rw [goldenRatio]
    positivity
  have hr : 0 < icoRadius := by
    rw [icoRadius]
    positivity
  have hnum (i : Fin 3) : icoNumerator j i = icoNumerator k i := by
    have heq := congrFun h i
    rw [icoVector_eq_div, icoVector_eq_div] at heq
    field_simp [ne_of_gt hr] at heq
    exact heq
  have h0 := hnum (0 : Fin 3)
  have h1 := hnum (1 : Fin 3)
  have h2 := hnum (2 : Fin 3)
  rcases j with ⟨g, ⟨s, t⟩⟩
  rcases k with ⟨g', ⟨s', t'⟩⟩
  fin_cases g <;> fin_cases s <;> fin_cases t <;>
    fin_cases g' <;> fin_cases s' <;> fin_cases t' <;>
    simp [icoNumerator, signValue] at h0 h1 h2 <;>
    first | nlinarith [hphi] | rfl

end AKLT.W.MOM001

#print axioms AKLT.W.MOM001.main
