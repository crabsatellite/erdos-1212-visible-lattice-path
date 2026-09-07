import Erdos1212Kernel.IwaniecPaperQBoundedLevel
import Erdos1212Kernel.IwaniecPaperQRankSaturation
import Erdos1212Kernel.IwaniecPaperASaturatedStep

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 550000

theorem iwaniecParitySieveProfile_add_two (rank : Nat) (s : Real) :
    iwaniecParitySieveProfile (rank + 2) s = iwaniecParitySieveProfile rank s := by
  simp only [iwaniecParitySieveProfile, Nat.even_add, even_two, iff_true]

theorem iwaniecPaperQMajorant_add_two {C level s : Real} (hC : 0 ≤ C)
    (rank : Nat) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecPaperQMajorant C rank level s ≤ iwaniecPaperQMajorant C (rank + 2) level s := by
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hW := (iwaniecAuxWeightPower_pos level (hstart.trans hs)).le
  have hG := (iwaniecAuxG_pos_exactDomain rank hs).le
  have hratio := iwaniec_rank_ratio_mono (show rank ≤ rank + 2 by omega)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC) hW) hG) (sq_nonneg (Real.log level))
  unfold iwaniecPaperQMajorant
  rw [iwaniecParitySieveProfile_add_two, iwaniecAuxG_add_two]
  exact add_le_add le_rfl hh

/-- The actual large-rank Q induction step. Saturation keeps parity,
so both the full main profile and G are unchanged; only r/(r+1) grows. -/
theorem eventually_iwaniecPaperQ_saturated_step :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (C : Real) (rank : Nat) (s : Real), 0 ≤ C →
      iwaniecAuxGStart rank ≤ s →
      2 * Real.log level / Real.log (Real.log level) ≤ ((rank + 2 : Nat) : Real) →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level s <
        iwaniecPaperQMajorant C rank level s →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (rank + 2) level s <
        iwaniecPaperQMajorant C (rank + 2) level s := by
  filter_upwards [eventually_iwaniecPaperQ_large_rank_saturated] with level hsat
  refine ⟨hsat.1, ?_⟩
  intro C rank s hC hs hrank hIH
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  rw [(hsat.2 rank s (hstart.trans hs) hrank).1]
  exact hIH.trans_le (iwaniecPaperQMajorant_add_two hC rank hs)

end

end Erdos1212Kernel
