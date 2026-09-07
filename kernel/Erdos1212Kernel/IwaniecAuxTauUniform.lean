import Erdos1212Kernel.IwaniecInductionFixedWeight
import Erdos1212Kernel.IwaniecAuxiliaryWeightedDerivative
import Erdos1212Kernel.IwaniecAuxiliaryWeightedRegularity
import Erdos1212Kernel.IwaniecAuxiliaryCorollaryHigh

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem iwaniecAuxWeightPower_monotoneOn (level : Real) :
    MonotoneOn (iwaniecAuxWeightPower level) (Set.Ici (1 : Real)) := by
  intro s hs t ht hst
  have hbase := iwaniecAuxWeightBase_monotoneOn level hs ht hst
  unfold iwaniecAuxWeightPower
  exact (Real.rpow_le_rpow (iwaniecAuxWeightBase_pos level hs).le hbase (by linarith [hs.out])).trans
    (Real.rpow_le_rpow_of_exponent_le (iwaniecAuxWeightBase_one_le level ht) (by linarith only [hst]))

theorem iwaniecAuxTau_antitoneOn_closed (rank : Nat) {level : Real} (hy : 1 < level) :
    AntitoneOn (iwaniecAuxTau rank level) (Set.Icc iwaniecAuxSZero (iwaniecPaperXi level)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro s hs
    exact (iwaniecAuxTau_hasDerivAt rank hy (by linarith [hs.1, iwaniecAuxSZero_large])).continuousAt.continuousWithinAt
  · intro s hs
    have hsi := interior_subset hs
    exact (iwaniecAuxTau_hasDerivAt rank hy (by linarith [hsi.1, iwaniecAuxSZero_large])).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (iwaniecAuxTau_deriv_neg rank hy hs.1 hs.2.le).le

theorem eventually_iwaniecAuxTau_le_four :
    ∀ᶠ level : Real in atTop, 1 < level ∧ 2 ≤ iwaniecPaperXi level ∧
      ∀ (rank : Nat) (s : Real), 2 ≤ s → s ≤ iwaniecPaperXi level → iwaniecAuxTau rank level s ≤ 4 := by
  let K := 10 * iwaniecAuxSZero ^ 3 * Real.log iwaniecAuxSZero ^ 5
  have hs0 : 1 ≤ iwaniecAuxSZero := by linarith [iwaniecAuxSZero_large]
  filter_upwards [eventually_iwaniecWeightPower_fixed_linear_bound hs0,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K),
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop iwaniecAuxSZero]
    with level hweight hlog hξ
  have hy := hweight.1
  have hL1 : 1 ≤ Real.log level := (le_max_left _ _).trans hlog
  have hKL : K ≤ Real.log level := (le_max_right _ _).trans hlog
  have hsmall : K / Real.log level ^ 2 ≤ 1 :=
    (div_le_one₀ (sq_pos_of_pos (Real.log_pos hy))).mpr (by nlinarith only [hL1, hKL])
  have hW0 : iwaniecAuxWeightPower level iwaniecAuxSZero ≤ 2 := by
    have hh := hweight.2
    change iwaniecAuxWeightPower level iwaniecAuxSZero ≤ 1 + K / Real.log level ^ 2 at hh
    linarith
  refine ⟨hy, by linarith [iwaniecAuxSZero_large], ?_⟩
  intro rank s hs hsξ
  have htop : iwaniecAuxTau rank level iwaniecAuxSZero ≤ 4 := by
    have hG := iwaniecAuxG_le_two (rank + 1) (s := iwaniecAuxSZero) (by linarith [iwaniecAuxSZero_large])
    have hG0 := (iwaniecAuxG_pos (rank + 1) (s := iwaniecAuxSZero) (by linarith [iwaniecAuxSZero_large])).le
    have hh := mul_le_mul hW0 hG hG0 (by norm_num : (0 : Real) ≤ 2)
    exact hh.trans (by norm_num)
  by_cases hlow : s ≤ iwaniecAuxSZero
  · have hWs := (iwaniecAuxWeightPower_monotoneOn level (show 1 ≤ s by linarith) hs0 hlow).trans hW0
    have hGs := iwaniecAuxG_le_two (rank + 1) hs
    have hh := mul_le_mul hWs hGs (iwaniecAuxG_pos (rank + 1) hs).le (by norm_num : (0 : Real) ≤ 2)
    exact hh.trans (by norm_num)
  · exact (iwaniecAuxTau_antitoneOn_closed rank hy ⟨le_rfl, hξ⟩ ⟨le_of_not_ge hlow, hsξ⟩ (le_of_not_ge hlow)).trans htop

end

end Erdos1212Kernel
