import Erdos1212Kernel.IwaniecAuxiliaryWeightedDerivative
import Erdos1212Kernel.IwaniecAuxiliaryWeightedRegularity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- Source (3.15). The positive value of tau at xi is retained in the
FTC bound before dropping it to obtain the stated strict inequality. -/
theorem iwaniecAuxLemmaEleven (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s < iwaniecPaperXi level) :
    (∫ t in s..(iwaniecPaperXi level), iwaniecAuxWeightedIntegrand rank level t) <
      iwaniecAuxTau rank level s := by
  have hsThree : 3 < s := by linarith [iwaniecAuxSZero_large]
  have hsubset : Set.Icc s (iwaniecPaperXi level) ⊆ Set.Ioi (3 : Real) := by
    intro t ht
    exact hsThree.trans_le ht.1
  have hcont := (iwaniecAuxTau_continuousOn rank hy).mono hsubset
  have hint : IntegrableOn (iwaniecAuxWeightedIntegrand rank level) (Set.Icc s (iwaniecPaperXi level)) :=
    ((iwaniecAuxWeightedIntegrand_continuousOn rank level).mono hsubset).integrableOn_Icc
  let slope := fun t : Real => -(iwaniecAuxWeightPower level t *
    (iwaniecAuxWeightLogDerivative level t * iwaniecAuxG (rank + 1) t - iwaniecAuxGKernel rank t))
  have hd : ∀ t ∈ Set.Ioo s (iwaniecPaperXi level),
      HasDerivWithinAt (fun t => -iwaniecAuxTau rank level t) (slope t) (Set.Ioi t) t := by
    intro t ht
    exact (iwaniecAuxTau_hasDerivAt rank hy (hsThree.trans ht.1)).neg.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ioo s (iwaniecPaperXi level), iwaniecAuxWeightedIntegrand rank level t ≤ slope t := by
    intro t ht
    have h := iwaniecAuxWeightedIntegrand_lt_neg_tau_deriv rank hy (hs.trans ht.1) ht.2.le
    rw [(iwaniecAuxTau_hasDerivAt rank hy (hsThree.trans ht.1)).deriv] at h
    exact h.le
  have hFTC := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hxi.le hcont.neg hd hint hbound
  have htopPos := iwaniecAuxTau_pos rank level (s := iwaniecPaperXi level) (by linarith)
  linarith

theorem iwaniecAuxLemmaEleven_explicit (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s < iwaniecPaperXi level) :
    (∫ t in s..(iwaniecPaperXi level),
      (1 + t ^ 2 * Real.log t ^ 5 / Real.log level ^ 2) ^ (5 * (t - 1)) *
        iwaniecAuxG rank (t - 1) * t / (t - 1) ^ 2) <
      (1 + s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2) ^ (5 * s) * iwaniecAuxG (rank + 1) s := by
  exact iwaniecAuxLemmaEleven rank hy hs hxi

end

end Erdos1212Kernel
