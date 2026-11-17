module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.GAP030

open AKLT.Challenge

theorem main : AKLT.Blueprint.Gap.BlockVolumeBoundStatement := by
  intro L N M hM hL hN
  let offset : Fin (2 * M + 1) × Fin (2 * M + 1) → Site L N :=
    fun p => ((p.1.val : ZMod L.val), (p.2.val : ZMod N.val))
  have hL' : 2 * M + 1 ≤ L.val := by omega
  have hN' : 2 * M + 1 ≤ N.val := by omega
  have offset_injective : Function.Injective offset := by
    intro p q hpq
    have hx : (p.1.val : ZMod L.val) = (q.1.val : ZMod L.val) :=
      congrArg Prod.fst hpq
    have hy : (p.2.val : ZMod N.val) = (q.2.val : ZMod N.val) :=
      congrArg Prod.snd hpq
    have hx' : p.1.val % L.val = q.1.val % L.val :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mp hx
    have hy' : p.2.val % N.val = q.2.val % N.val :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mp hy
    have hx'' : p.1.val = q.1.val := by
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le p.1.isLt hL'),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le q.1.isLt hL')] at hx'
      exact hx'
    have hy'' : p.2.val = q.2.val := by
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le p.2.isLt hN'),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le q.2.isLt hN')] at hy'
      exact hy'
    apply Prod.ext
    · exact Fin.ext hx''
    · exact Fin.ext hy''
  have hcard := Fintype.card_le_of_injective offset offset_injective
  simpa [AKLT.Challenge.Site, ZMod.card, AKLT.Blueprint.Gap.volumeCount,
    pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

end AKLT.W.GAP030
