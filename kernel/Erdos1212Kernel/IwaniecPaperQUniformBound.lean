import Erdos1212Kernel.IwaniecPaperQMiddleStep
import Erdos1212Kernel.IwaniecPaperQBaseRanks
import Erdos1212Kernel.IwaniecPaperQSaturatedStep

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 800000

/-- Uniform Theorem 4 bound on the actual finite parity sums Q.
The absolute constant is chosen before rank, level, and parameter.
The extra rank-one case is the proved zero padding, not a premise. -/
theorem exists_iwaniecPaperQ_uniform_bound :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, 1 ≤ rank → ∀ level s : Real,
      1 < level → iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level s <
        iwaniecPaperQMajorant C rank level s := by
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    (eventually_iwaniecPaperQ_middle_step.and
      (eventually_iwaniecPaperQ_saturated_step.and
        (eventually_iwaniecPaperQ_two_base.and (Real.tendsto_log_atTop.eventually_gt_atTop 1))))
  let Y := max Y₀ (Real.exp 64)
  let CY := (1 + Real.log Y) ^ 3 / iwaniecAuxM (2 * Real.log Y)
  let C := max 2 CY
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCY : CY ≤ C := le_max_right _ _
  have hC : 0 < C := by linarith only [hC2]
  have hlogY : 64 ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos (64 : Real)) (le_max_right Y₀ (Real.exp 64))
    simpa only [Real.log_exp] using hh
  refine ⟨C, hC, ?_⟩
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro hr level s hy hs hsξ
      by_cases hrone : rank = 1
      · subst rank
        exact iwaniecPaperQ_one_bound hC hy hs
      · have hr2 : 2 ≤ rank := by omega
        by_cases hyY : level ≤ Y
        · exact iwaniecPaperQ_bounded_level_bound hlogY hCY hr hy hyY hs
        · have hYlevel : Y₀ ≤ level := (le_max_left _ _).trans (le_of_not_ge hyY)
          obtain ⟨hmid, hsat, hbase, _hL⟩ := hY₀ level hYlevel
          by_cases hrtwo : rank = 2
          · subst rank
            have hs2 : 2 ≤ s := by simpa only [iwaniecAuxGStart, even_two, if_true] using hs
            exact hbase.2 C s hC2 hs2
          · have hr3 : 3 ≤ rank := by omega
            by_cases hlarge : 2 * Real.log level / Real.log (Real.log level) ≤ (rank : Real)
            · let k := rank - 2
              have hk : 1 ≤ k := by dsimp [k]; omega
              have hkr : k < rank := by dsimp [k]; omega
              have heq : rank = k + 2 := by dsimp [k]; omega
              have hstart : iwaniecAuxGStart k ≤ s := by
                have hh := hs
                rw [heq, iwaniecAuxGStart_add_two] at hh
                exact hh
              have hIH := ih k hkr hk level s hy hstart hsξ
              have hh := hsat.2 C k s hC.le hstart (by simpa only [← heq] using hlarge) hIH
              simpa only [← heq] using hh
            · let n := rank - 1
              have hn : 1 ≤ n := by dsimp [n]; omega
              have hnr : n < rank := by dsimp [n]; omega
              have heq : rank = n + 1 := by dsimp [n]; omega
              have hstart : iwaniecAuxGStart (n + 1) ≤ s := by simpa only [← heq] using hs
              have hRange : (n : Real) + 1 ≤ 2 * Real.log level / Real.log (Real.log level) := by
                have hh := (lt_of_not_ge hlarge).le
                have hcast : (rank : Real) = (n : Real) + 1 := by exact_mod_cast heq
                rwa [hcast] at hh
              have hIH : ∀ y t : Real, 1 < y → iwaniecAuxGStart n ≤ t → t ≤ iwaniecPaperXi y →
                  Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ n y t < iwaniecPaperQMajorant C n y t := by
                intro y t hy ht htξ
                exact ih n hnr hn y t hy ht htξ
              have hh := hmid.2 C n s hC2 hn hstart hsξ hRange hIH
              simpa only [← heq] using hh

/-- Iwaniec 1971, displayed Theorem 4 (4.1), on its literal rank and
parity domains, with no unproved literature output or induction premise. -/
theorem exists_iwaniecTheorem4_constant :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, 2 ≤ rank → ∀ level s : Real,
      1 < level → iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level s <
        iwaniecParitySieveProfile rank s / Real.log level +
          C * ((rank : Real) / ((rank : Real) + 1)) * iwaniecAuxWeightPower level s *
            iwaniecAuxG rank s / Real.log level ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_iwaniecPaperQ_uniform_bound
  exact ⟨C, hC, fun rank hr level s hy hs hsξ => hbound rank (by omega) level s hy hs hsξ⟩

end

end Erdos1212Kernel
