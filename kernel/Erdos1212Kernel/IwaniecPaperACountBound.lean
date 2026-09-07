import Erdos1212Kernel.IwaniecPaperAMiddleStep
import Erdos1212Kernel.IwaniecPaperARankOne
import Erdos1212Kernel.IwaniecPaperASaturatedStep

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 800000

/-- Uniform bound on the actual support count. The domain is the actual
G_(r+1) domain; it is not identified with a different printed endpoint. -/
theorem exists_iwaniecPaperA_count_bound :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, 1 ≤ rank → ∀ level s : Real,
      1 < level → iwaniecAuxGStart (rank + 1) ≤ s → s ≤ iwaniecPaperXi level →
        (iwaniecPaperA rank level s : Real) ≤ iwaniecPaperAMajorant C rank level s := by
  obtain ⟨C₁, _hC₁, hbase⟩ := exists_iwaniecPaperA_rank_one_constant
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    (eventually_iwaniecPaperA_middle_step.and
      (eventually_iwaniecPaperA_saturated_step.and (Real.tendsto_log_atTop.eventually_gt_atTop 1)))
  let Y := max Y₀ (Real.exp 12288)
  let CY := (1 + Real.log Y) ^ 3 / iwaniecAuxM (2 * Real.log Y)
  let C := max C₁ (max 2 CY)
  have hCbase : C₁ ≤ C := le_max_left _ _
  have hC2 : 2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCY : CY ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hlogY : 12288 ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos (12288 : Real)) (le_max_right Y₀ (Real.exp 12288))
    simpa only [Real.log_exp] using hh
  have hC : 0 < C := by linarith
  refine ⟨C, hC, ?_⟩
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro hr level s hy hs hsξ
      by_cases hrone : rank = 1
      · subst rank
        have hs2 : 2 ≤ s := by simpa [iwaniecAuxGStart] using hs
        exact hbase C hCbase level s hy hs2 hsξ
      · have hr2 : 2 ≤ rank := by omega
        by_cases hyY : level ≤ Y
        · exact iwaniecPaperA_bounded_level_bound hlogY hCY hr hy hyY hs hsξ
        · have hYlevel : Y₀ ≤ level := (le_max_left _ _).trans (le_of_not_ge hyY)
          obtain ⟨hmid, hsat, hL⟩ := hY₀ level hYlevel
          by_cases hlarge : 2 * Real.log level / Real.log (Real.log level) ≤ (rank : Real)
          · have hthreshold : 2 < 2 * Real.log level / Real.log (Real.log level) := by
              apply (lt_div_iff₀ (Real.log_pos hL)).mpr
              have hh := Real.log_le_sub_one_of_pos (show 0 < Real.log level by linarith)
              linarith
            have hrReal : (2 : Real) < rank := hthreshold.trans_le hlarge
            have hr3 : 3 ≤ rank := by
              have hh : 2 < rank := by exact_mod_cast hrReal
              omega
            let k := rank - 2
            have hk : 1 ≤ k := by dsimp [k]; omega
            have hkr : k < rank := by dsimp [k]; omega
            have heq : rank = k + 2 := by dsimp [k]; omega
            have hstart : iwaniecAuxGStart (k + 1) ≤ s := by
              have hh := hs
              rw [heq, show k + 2 + 1 = (k + 1) + 2 by omega, iwaniecAuxGStart_add_two] at hh
              exact hh
            have hIH := ih k hkr hk level s hy hstart hsξ
            have hh := hsat.2 C k s hC.le hstart (by simpa only [← heq] using hlarge) hIH
            simpa only [← heq] using hh
          · let n := rank - 1
            have hn : 1 ≤ n := by dsimp [n]; omega
            have hnr : n < rank := by dsimp [n]; omega
            have heq : rank = n + 1 := by dsimp [n]; omega
            have hstart : iwaniecAuxGStart ((n + 1) + 1) ≤ s := by simpa only [← heq] using hs
            have hRange : (n : Real) + 1 ≤ 2 * Real.log level / Real.log (Real.log level) := by
              have hh := (lt_of_not_ge hlarge).le
              have hcast : (rank : Real) = (n : Real) + 1 := by exact_mod_cast heq
              rwa [hcast] at hh
            have hIH : ∀ y t : Real, 1 < y → iwaniecAuxGStart (n + 1) ≤ t → t ≤ iwaniecPaperXi y →
                (iwaniecPaperA n y t : Real) ≤ iwaniecPaperAMajorant C n y t := by
              intro y t hy ht htξ
              exact ih n hnr hn y t hy ht htξ
            have hh := hmid.2 C n s hC2 hn hstart hsξ hRange hIH
            simpa only [← heq] using hh

end

end Erdos1212Kernel
