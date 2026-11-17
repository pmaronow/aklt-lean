module
public import AKLT.Defs.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:moment`: three real coordinates; Euclidean geometry is expressed by `dot`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- The Euclidean scalar product. -/
def dot (a b : Vec3) : ℝ := ∑ i, a i * b i

/-- The Euclidean squared norm. -/
def normSq (a : Vec3) : ℝ := dot a a

/-- `d:moment`: arbitrary unit pins, independent of any frame alphabet. -/
abbrev UnitVector := {a : Vec3 // normSq a = 1}

/-- Closed unit ball used by the covering and leaf statements. -/
abbrev BallVector := {a : Vec3 // normSq a ≤ 1}

/-- `d:moment`: the golden ratio. -/
def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- `d:moment`: normalization of each icosahedron vertex. -/
def icoRadius : ℝ := Real.sqrt (goldenRatio + 2)

/-- `d:moment`: twelve labels, with the two signs independent. -/
abbrev IcoLetter := Fin 3 × Fin 2 × Fin 2

/-- The two independent sign values. -/
def signValue (j : Fin 2) : ℝ := if j = 0 then 1 else -1

/-- `d:moment`: the twelve explicit icosahedron vectors, without assuming their moments. -/
def icoVector (j : IcoLetter) : Vec3 :=
  let a := signValue j.2.1
  let b := signValue j.2.2 * goldenRatio
  let v : Vec3 := if j.1 = 0 then ![0, a, b]
    else if j.1 = 1 then ![a, b, 0] else ![b, 0, a]
  fun k => v k / icoRadius

/-- `d:moment`: the actual finite set `D`, as a range of its twelve labels. -/
def icoSet : Finset Vec3 := Finset.univ.image icoVector

/-- `d:moment`: the fourth-moment functional, defined for arbitrary functions by a finite sum. -/
def moment (f : Vec3 → ℝ) : ℝ := (1 / 12) * ∑ j : IcoLetter, f (icoVector j)

/-- `d:domain`: site status; there is no scalar trace mass. -/
inductive Status where
  | U | D | X
  deriving DecidableEq, Repr

instance : Fintype Status := ⟨{.U, .D, .X}, by intro s; cases s <;> simp⟩

/-- A common finite support: twelve unit labels and one zero label.
The extra label has weight zero at a U site. -/
abbrev SpinLetter := Option IcoLetter

/-- The zero atom and the twelve geometric atoms. -/
def spinVector : SpinLetter → Vec3
  | none => 0
  | some j => icoVector j

/-- `d:moment`: exact weights of `lambda_U` and `lambda_D`.
X sites are omitted from every partition sum. -/
def spinWeight (s : Status) : SpinLetter → ℝ
  | none => if s = .D then 2 / 5 else 0
  | some _ => if s = .U then 1 / 12 else if s = .D then 1 / 20 else 0

/-- The finite site functional for either active status. -/
def siteFunctional (s : Status) (f : Vec3 → ℝ) : ℝ :=
  ∑ j : SpinLetter, spinWeight s j * f (spinVector j)

/-- A polynomial is admissible when its total degree is at most four. -/
def DegreeFour (p : MvPolynomial (Fin 3) ℝ) : Prop := p.totalDegree ≤ 4

/-- `l:moments`: separate degree includes the inserted observable. -/
def SeparateDegreeFour {ι : Type*} (p : MvPolynomial (ι × Fin 3) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ x : ι, (∑ k : Fin 3, m (x, k)) ≤ 4

/-- A finite product functional, also defined for the empty product of sites. -/
def productFunctional {ι : Type*} [Fintype ι] (s : ι → Status)
    (f : (ι → Vec3) → ℝ) : ℝ := by
  classical
  exact ∑ n : ι → SpinLetter, (∏ x, spinWeight (s x) (n x)) * f (fun x => spinVector (n x))

end AKLT.Defs
