import Erdos1212Kernel.IwaniecAuxiliaryLagRatio

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- The literal ratio introduced in source Lemma 10. -/
def iwaniecAuxEta (s : Real) : Real := iwaniecAuxM (s - 1) / iwaniecAuxM s

theorem iwaniecAuxEta_pos {s : Real} (hs : 3 ≤ s) : 0 < iwaniecAuxEta s :=
  div_pos (iwaniecAuxM_pos (by linarith)) (iwaniecAuxM_pos (by linarith))

theorem iwaniecAuxEta_continuousOn : ContinuousOn iwaniecAuxEta (Set.Ici (3 : Real)) := by
  have hshift : ContinuousOn (fun s : Real => iwaniecAuxM (s - 1)) (Set.Ici (3 : Real)) := by
    apply iwaniecAuxM_continuousOn.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change (2 : Real) ≤ s - 1
    linarith [hs.out]
  apply hshift.div (iwaniecAuxM_continuousOn.mono (Set.Ici_subset_Ici.mpr (by norm_num)))
  intro s hs
  exact (iwaniecAuxM_pos (by linarith [hs.out] : 2 ≤ s)).ne'

theorem iwaniecAuxMCoefficient_le_eta {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxMCoefficient s ≤ iwaniecAuxEta s := by
  have hint := iwaniecIntervalIntegrable_of_continuousOn_one _
    iwaniecAuxMWindowKernel_continuousOn (a := s - 1) (b := s) (by linarith) (by linarith)
  have hpoint : ∀ x ∈ Set.Icc (s - 1) s,
      iwaniecAuxMWindowKernel x ≤ iwaniecAuxM (s - 1) := by
    intro x hx
    have hxTwo : 2 ≤ x := by linarith [hx.1]
    have hweight : iwaniecAuxMWindowWeight x ≤ 1 := by
      unfold iwaniecAuxMWindowWeight
      have hnn : 0 ≤ (1 : Real) / (2 * x ^ 2) :=
        div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg x))
      linarith
    exact (mul_le_of_le_one_left (iwaniecAuxM_pos hxTwo).le hweight).trans
      (iwaniecAuxM_antitoneOn (show 2 ≤ s - 1 by linarith) hxTwo hx.1)
  have hbound := intervalIntegral.integral_mono_on (show s - 1 ≤ s by linarith)
    hint (g := fun _x : Real => iwaniecAuxM (s - 1)) intervalIntegrable_const hpoint
  simp only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul, one_mul] at hbound
  have hw := iwaniecAuxM_window_identity hs
  change iwaniecAuxMCoefficient s * iwaniecAuxM s =
    ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hw
  unfold iwaniecAuxEta
  rw [le_div_iff₀ (iwaniecAuxM_pos (by linarith : 2 ≤ s)), hw]
  exact hbound

theorem iwaniecAuxEta_bounds {s : Real} (hs : 3 ≤ s) :
    s - 2 ≤ iwaniecAuxEta s ∧ iwaniecAuxEta s < 4 * s ^ 2 := by
  constructor
  · apply le_trans _ (iwaniecAuxMCoefficient_le_eta hs)
    unfold iwaniecAuxMCoefficient
    rw [le_div_iff₀ (show 0 < s by linarith)]
    nlinarith
  · exact iwaniecAuxM_lag_ratio_lt hs

theorem neg_log_iwaniecAuxM_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt (fun t : Real => -Real.log (iwaniecAuxM t))
      (iwaniecAuxEta s * s / (s - 1) ^ 2) s := by
  have hraw := ((iwaniecAuxM_hasDerivAt hs).log
    (iwaniecAuxM_pos (by linarith : 2 ≤ s)).ne').neg
  convert hraw using 1
  unfold iwaniecAuxEta
  ring

/-- Exact first integral identity in source Lemma 10. No monotonicity of
eta, or estimate of this integral by its endpoint value, is assumed. -/
theorem log_iwaniecAuxEta_eq_integral {s : Real} (hs : 4 < s) :
    Real.log (iwaniecAuxEta s) =
      ∫ x in (s - 1)..s, iwaniecAuxEta x * x / (x - 1) ^ 2 := by
  have hcont : ContinuousOn (fun x : Real => iwaniecAuxEta x * x / (x - 1) ^ 2)
      (Set.Icc (s - 1) s) := by
    have heta := iwaniecAuxEta_continuousOn.mono (show Set.Icc (s - 1) s ⊆ Set.Ici (3 : Real) by
      intro x hx
      change (3 : Real) ≤ x
      linarith [hx.1])
    apply (heta.mul continuousOn_id).div ((continuousOn_id.sub continuousOn_const).pow 2)
    intro x hx
    exact pow_ne_zero 2 (show x - 1 ≠ 0 by linarith [hx.1])
  have hint : IntervalIntegrable (fun x : Real => iwaniecAuxEta x * x / (x - 1) ^ 2)
      volume (s - 1) s := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show s - 1 ≤ s by linarith)] using hcont
  have hd : ∀ x ∈ Set.uIcc (s - 1) s,
      HasDerivAt (fun t : Real => -Real.log (iwaniecAuxM t))
        (iwaniecAuxEta x * x / (x - 1) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le (show s - 1 ≤ s by linarith)] at hx
    exact neg_log_iwaniecAuxM_hasDerivAt (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  unfold iwaniecAuxEta
  rw [Real.log_div (iwaniecAuxM_pos (by linarith : 2 ≤ s - 1)).ne'
    (iwaniecAuxM_pos (by linarith : 2 ≤ s)).ne']
  ring

theorem log_iwaniecAuxEta_lower {s : Real} (hs : 3 ≤ s) :
    Real.log (s - 2) ≤ Real.log (iwaniecAuxEta s) :=
  Real.log_le_log (by linarith) (iwaniecAuxEta_bounds hs).1

end

end Erdos1212Kernel
