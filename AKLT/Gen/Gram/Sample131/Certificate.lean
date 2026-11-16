import AKLT.Gen.Gram.Sample131.Header
import AKLT.Gen.Gram.Sample131.Rows00
import AKLT.Gen.Gram.Sample131.Rows01
import AKLT.Gen.Gram.Sample131.Rows02
import AKLT.Gen.Gram.Sample131.Rows03
import AKLT.Gen.Gram.Sample131.Rows04
import AKLT.Gen.Gram.Sample131.Rows05
import AKLT.Gen.Gram.Sample131.Rows06
import AKLT.Gen.Gram.Sample131.Rows07
import AKLT.Gen.Gram.Sample131.Rows08
import AKLT.Gen.Gram.Sample131.Rows09
import AKLT.Gen.Gram.Sample131.Rows10
import AKLT.Gen.Gram.Sample131.Rows11
import AKLT.Gen.Gram.Sample131.Rows12
import AKLT.Gen.Gram.Sample131.Rows13
import AKLT.Gen.Gram.Sample131.Rows14
import AKLT.Gen.Gram.Sample131.Rows15
import AKLT.Gen.Gram.Sample131.Rows16
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows_checked : checkRows lData 1 1 0 mData lData = true := by
  change checkRows lData 1 1 0 (m0 ++ (m1 ++ (m2 ++ (m3 ++ (m4 ++ (m5 ++ (m6 ++ (m7 ++ (m8 ++ (m9 ++ (m10 ++ (m11 ++ (m12 ++ (m13 ++ (m14 ++ (m15 ++ (m16 ++ ([])))))))))))))))))) (l0 ++ (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ (l8 ++ (l9 ++ (l10 ++ (l11 ++ (l12 ++ (l13 ++ (l14 ++ (l15 ++ (l16 ++ ([])))))))))))))))))) = true
  apply checkRows_append_true m0_length l0_length rows0_checked
  apply checkRows_append_true m1_length l1_length rows1_checked
  apply checkRows_append_true m2_length l2_length rows2_checked
  apply checkRows_append_true m3_length l3_length rows3_checked
  apply checkRows_append_true m4_length l4_length rows4_checked
  apply checkRows_append_true m5_length l5_length rows5_checked
  apply checkRows_append_true m6_length l6_length rows6_checked
  apply checkRows_append_true m7_length l7_length rows7_checked
  apply checkRows_append_true m8_length l8_length rows8_checked
  apply checkRows_append_true m9_length l9_length rows9_checked
  apply checkRows_append_true m10_length l10_length rows10_checked
  apply checkRows_append_true m11_length l11_length rows11_checked
  apply checkRows_append_true m12_length l12_length rows12_checked
  apply checkRows_append_true m13_length l13_length rows13_checked
  apply checkRows_append_true m14_length l14_length rows14_checked
  apply checkRows_append_true m15_length l15_length rows15_checked
  apply checkRows_append_true m16_length l16_length rows16_checked
  rfl
theorem checked : checker mData lData 1 1 1 = true := by
  simp only [checker, Bool.and_eq_true]
  exact ⟨header_checked, rows_checked⟩
theorem posDef_real : (toMatrix mData).PosDef := checker_sound checked
open scoped ComplexOrder
theorem posDef_complex : (castMatrix (matrix mData.length mData) :
    Matrix (Fin mData.length) (Fin mData.length) ℂ).PosDef := checker_sound_complex checked
theorem posDef_rat : (castMatrix (matrix mData.length mData) :
    Matrix (Fin mData.length) (Fin mData.length) ℚ).PosDef := checker_sound_rat checked
#print axioms rows_checked
#print axioms checked
#print axioms posDef_real
#print axioms posDef_complex
#print axioms posDef_rat
end AKLT.Gen.Gram.Sample131
