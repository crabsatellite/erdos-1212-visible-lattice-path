import Erdos1212Kernel.IwaniecCorollaryThreeWeight
import Erdos1212Kernel.IwaniecAuxiliaryLagRatio
import Erdos1212Kernel.IwaniecAuxiliaryLemmaEleven

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 650000

theorem iwaniecAuxG_shift_le_eight_square (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxG rank (s - 1) ≤ 8 * s ^ 2 * iwaniecAuxG (rank + 1) s := by
  have hup := (iwaniecAuxG_bounds rank (s := s - 1) (by linarith)).2
  have hlo := (iwaniecAuxG_bounds (rank + 1) (s := s) (by linarith)).1
  have hlag := iwaniecAuxM_lag_lt_four_square hs
  have hscaled := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 8 * s ^ 2 by positivity)
  nlinarith only [hup, hlag, hscaled]

theorem iwaniecCorollaryThreeScaledProfile_endpoint_bound (rank : Nat)
    (level : Real) {s : Real} (hs : 3 ≤ s) :
    iwaniecCorollaryThreeScaledProfile rank level s ≤ 20 * s ^ 2 * iwaniecAuxTau rank level s := by
  have hlowpos := (iwaniecAuxWeightLowerPower_pos level (s := s) (by linarith)).le
  have hfullpos := (iwaniecAuxWeightPower_pos level (s := s) (by linarith)).le
  have hGpos := (iwaniecAuxG_pos rank (s := s - 1) (by linarith)).le
  have hGnext := (iwaniecAuxG_pos (rank + 1) (s := s) (by linarith)).le
  have hbase := iwaniecAuxWeightBase_one_le level (s := s) (by linarith)
  have hbasepow : 1 ≤ iwaniecAuxWeightBase level s ^ 5 := one_le_pow₀ hbase
  have hW : iwaniecAuxWeightLowerPower level s ≤ iwaniecAuxWeightPower level s := by
    rw [iwaniecAuxWeightPower_split level (show 1 ≤ s by linarith)]
    nlinarith only [hbasepow, hlowpos]
  have hG := iwaniecAuxG_shift_le_eight_square rank hs
  have hratio : s / (s - 1) ≤ 3 / 2 := by
    apply (div_le_iff₀ (show 0 < s - 1 by linarith)).mpr
    linarith only [hs]
  have hratio0 : 0 ≤ s / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hratioSq : (s / (s - 1)) ^ 2 ≤ 9 / 4 := by
    have hh := pow_le_pow_left₀ hratio0 hratio 2
    norm_num at hh
    exact hh
  have hproduct := mul_le_mul hG hratioSq (sq_nonneg _) (by positivity : 0 ≤ 8 * s ^ 2 * iwaniecAuxG (rank + 1) s)
  calc
    _ = iwaniecAuxWeightLowerPower level s *
        (iwaniecAuxG rank (s - 1) * (s / (s - 1)) ^ 2) := by
      unfold iwaniecCorollaryThreeScaledProfile iwaniecCorollaryThreeProfile
      ring
    _ ≤ iwaniecAuxWeightLowerPower level s *
        ((8 * s ^ 2 * iwaniecAuxG (rank + 1) s) * (9 / 4)) :=
      mul_le_mul_of_nonneg_left hproduct hlowpos
    _ ≤ iwaniecAuxWeightPower level s * ((8 * s ^ 2 * iwaniecAuxG (rank + 1) s) * (9 / 4)) :=
      mul_le_mul_of_nonneg_right hW (by positivity)
    _ = 18 * s ^ 2 * iwaniecAuxTau rank level s := by unfold iwaniecAuxTau; ring
    _ ≤ _ := by
      have hp : 0 ≤ s ^ 2 * iwaniecAuxTau rank level s :=
        mul_nonneg (sq_nonneg s) (iwaniecAuxTau_pos rank level (by linarith)).le
      nlinarith only [hp]

theorem iwaniecAuxLemmaEleven_closed (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero ≤ s) (hxi : s ≤ iwaniecPaperXi level) :
    (∫ t in s..(iwaniecPaperXi level), iwaniecAuxWeightedIntegrand rank level t) <
      iwaniecAuxTau rank level s := by
  have hs3 : 3 < s := by linarith [iwaniecAuxSZero_large]
  by_cases heq : s = iwaniecPaperXi level
  · rw [← heq, intervalIntegral.integral_same]
    exact iwaniecAuxTau_pos rank level (by linarith)
  · have hstrict : s < iwaniecPaperXi level := lt_of_le_of_ne hxi heq
    have hsubset : Set.Icc s (iwaniecPaperXi level) ⊆ Set.Ioi (3 : Real) :=
      fun t ht => hs3.trans_le ht.1
    have hc := (iwaniecAuxTau_continuousOn rank hy).mono hsubset
    have hi : IntegrableOn (iwaniecAuxWeightedIntegrand rank level)
        (Set.Icc s (iwaniecPaperXi level)) volume :=
      ((iwaniecAuxWeightedIntegrand_continuousOn rank level).mono hsubset).integrableOn_Icc
    let slope := fun t : Real => -(iwaniecAuxWeightPower level t *
      (iwaniecAuxWeightLogDerivative level t * iwaniecAuxG (rank + 1) t - iwaniecAuxGKernel rank t))
    have hd : ∀ t ∈ Set.Ioo s (iwaniecPaperXi level),
        HasDerivWithinAt (fun t => -iwaniecAuxTau rank level t) (slope t) (Set.Ioi t) t := by
      intro t ht
      exact (iwaniecAuxTau_hasDerivAt rank hy (hs3.trans ht.1)).neg.hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Ioo s (iwaniecPaperXi level), iwaniecAuxWeightedIntegrand rank level t ≤ slope t := by
      intro t ht
      have hh := iwaniecAuxWeightedIntegrand_lt_neg_tau_deriv rank hy (hs.trans_lt ht.1) ht.2.le
      rw [(iwaniecAuxTau_hasDerivAt rank hy (hs3.trans ht.1)).deriv] at hh
      exact hh.le
    have hFTC := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hstrict.le hc.neg hd hi hbound
    have hpos := iwaniecAuxTau_pos rank level (s := iwaniecPaperXi level) (by linarith)
    linarith

theorem iwaniecCorollaryThree_left_cutoff_two
    {level : Real} (hy : 1 < level) (hxi : iwaniecAuxSZero ≤ iwaniecPaperXi level) :
    2 ≤ iwaniecExpReciprocalScale (Real.log level) (iwaniecPaperXi level) := by
  have hu : 1 < Real.log (Real.log (3 * level)) := by
    by_contra hn
    have hh := iwaniecPaperXi_le_small_when_loglog_small hy (le_of_not_gt hn)
    linarith [iwaniecAuxSZero_large]
  have hL : 0 < Real.log level := Real.log_pos hy
  have hpow : 0 < Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) := by positivity
  have hquot : Real.log level / iwaniecPaperXi level =
      Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) := by
    unfold iwaniecPaperXi
    field_simp [hL.ne', hpow.ne']
  have hone : 1 ≤ Real.log level / iwaniecPaperXi level := by
    rw [hquot]
    exact Real.one_le_rpow hu.le (by norm_num)
  exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hone)

end

end Erdos1212Kernel
