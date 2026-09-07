import Erdos1212Kernel.IwaniecPaperABoundedLevel
import Erdos1212Kernel.IwaniecPaperARankThreshold
import Erdos1212Kernel.IwaniecCorollaryThreeProfile

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 550000

theorem iwaniec_rank_ratio_mono {m n : Nat} (hmn : m ≤ n) :
    (m : Real) / ((m : Real) + 1) ≤ (n : Real) / ((n : Real) + 1) := by
  apply (div_le_div_iff₀ (by positivity : 0 < (m : Real) + 1) (by positivity : 0 < (n : Real) + 1)).mpr
  have hh : (m : Real) ≤ n := by exact_mod_cast hmn
  nlinarith only [hh]

theorem iwaniecPaperAMajorant_add_two {C level s : Real} (hC : 0 ≤ C) (hy : 1 < level)
    (rank : Nat) (hs : iwaniecAuxGStart (rank + 1) ≤ s) :
    iwaniecPaperAMajorant C rank level s ≤ iwaniecPaperAMajorant C (rank + 2) level s := by
  have hstart1 : 1 ≤ iwaniecAuxGStart (rank + 1) := by unfold iwaniecAuxGStart; split_ifs <;> norm_num
  have hW := (iwaniecAuxWeightPower_pos level (hstart1.trans hs)).le
  have hG := (iwaniecAuxG_pos_exactDomain (rank + 1) hs).le
  have hratio := iwaniec_rank_ratio_mono (show rank ≤ rank + 2 by omega)
  have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) hW) hG)
    (sq_nonneg (Real.log level))) (show 0 ≤ level by linarith)
  unfold iwaniecPaperAMajorant
  rw [show rank + 2 + 1 = (rank + 1) + 2 by omega, iwaniecAuxG_add_two]
  exact hh

theorem iwaniecPaperA_saturated_step_bound {C level s : Real}
    (hC : 0 ≤ C) (hy : 1 < level) (rank : Nat)
    (hs : iwaniecAuxGStart (rank + 1) ≤ s)
    (hfactorial : level ≤ ((rank + 2).factorial : Real))
    (hIH : (iwaniecPaperA rank level s : Real) ≤ iwaniecPaperAMajorant C rank level s) :
    (iwaniecPaperA (rank + 2) level s : Real) ≤ iwaniecPaperAMajorant C (rank + 2) level s := by
  rw [iwaniecPaperA_rank_add_two_saturated rank level s hfactorial]
  exact hIH.trans (iwaniecPaperAMajorant_add_two hC hy rank hs)

theorem eventually_iwaniecPaperA_saturated_step :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (C : Real) (rank : Nat) (s : Real), 0 ≤ C →
      iwaniecAuxGStart (rank + 1) ≤ s →
      2 * Real.log level / Real.log (Real.log level) ≤ ((rank + 2 : Nat) : Real) →
      (iwaniecPaperA rank level s : Real) ≤ iwaniecPaperAMajorant C rank level s →
      (iwaniecPaperA (rank + 2) level s : Real) ≤ iwaniecPaperAMajorant C (rank + 2) level s := by
  filter_upwards [eventually_gt_atTop (1 : Real), eventually_iwaniecFactorial_dominates_level] with level hy hfac
  refine ⟨hy, ?_⟩
  intro C rank s hC hs hrank hIH
  exact iwaniecPaperA_saturated_step_bound hC hy rank hs (hfac (rank + 2) hrank) hIH

end

end Erdos1212Kernel
