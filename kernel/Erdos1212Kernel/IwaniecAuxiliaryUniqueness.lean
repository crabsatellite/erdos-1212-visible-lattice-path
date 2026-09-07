import Erdos1212Kernel.IwaniecAuxiliaryRegularity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- The displayed differential definition implies its integral form using
only the paper's domain.  No derivative at the initial join `s=3` is assumed. -/
theorem iwaniecAuxiliary_integral_equation
    (sigma : Real) (f : Real → Real)
    (hcont : ContinuousOn f (Set.Ici (2 : Real)))
    (hinit : ∀ s ∈ Set.Icc (2 : Real) 3, f s = iwaniecAuxInitial sigma s)
    (hderiv : ∀ s : Real, 3 < s →
      HasDerivAt f (sigma * iwaniecAuxDelayKernel s * f (s - 1)) s)
    {s : Real} (hs : 2 ≤ s) :
    f s = iwaniecAuxBase sigma s +
      sigma * ∫ t in (3 : Real)..(max 3 s), iwaniecAuxDelayKernel t * f (t - 1) := by
  by_cases hsThree : s ≤ 3
  · rw [hinit s ⟨hs, hsThree⟩]
    simp [iwaniecAuxBase, min_eq_left hsThree, max_eq_left hsThree]
  · have hsHigh : 3 < s := lt_of_not_ge hsThree
    have hcontF : ContinuousOn f (Set.Icc (3 : Real) s) := by
      apply hcont.mono
      intro t ht
      have h := ht.1
      change (2 : Real) ≤ t
      linarith
    have hshift : ContinuousOn (fun t : Real => f (t - 1)) (Set.Icc (3 : Real) s) := by
      apply hcont.comp (continuousOn_id.sub continuousOn_const)
      intro t ht
      change (2 : Real) ≤ t - 1
      linarith [ht.1]
    have hkernel : ContinuousOn iwaniecAuxDelayKernel (Set.Icc (3 : Real) s) := by
      intro t ht
      exact (iwaniecAuxDelayKernel_continuousAt (by linarith [ht.1])).continuousWithinAt
    have hint : IntervalIntegrable
        (fun t => sigma * (iwaniecAuxDelayKernel t * f (t - 1))) volume 3 s := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hsHigh.le]
      exact continuousOn_const.mul (hkernel.mul hshift)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsHigh.le hcontF
      (f' := fun t => sigma * (iwaniecAuxDelayKernel t * f (t - 1)))
      (fun t ht => by simpa only [mul_assoc] using hderiv t ht.1) hint
    rw [intervalIntegral.integral_const_mul, hinit 3 (by norm_num)] at hFTC
    simp only [iwaniecAuxBase, min_eq_right hsHigh.le, max_eq_right hsHigh.le]
    linarith

/-- Uniqueness on the exact paper domain, so the method-of-steps object
cannot differ from the auxiliary function specified in the source. -/
theorem iwaniecAuxFunction_unique
    (sigma : Real) (f : Real → Real)
    (hcont : ContinuousOn f (Set.Ici (2 : Real)))
    (hinit : ∀ s ∈ Set.Icc (2 : Real) 3, f s = iwaniecAuxInitial sigma s)
    (hderiv : ∀ s : Real, 3 < s →
      HasDerivAt f (sigma * iwaniecAuxDelayKernel s * f (s - 1)) s) :
    Set.EqOn f (iwaniecAuxFunction sigma) (Set.Ici (2 : Real)) := by
  have hsteps : ∀ n : Nat, ∀ s ∈ Set.Icc (2 : Real) ((n : Real) + 3),
      f s = iwaniecAuxApprox sigma n s := by
    intro n
    induction n with
    | zero =>
        intro s hs
        have hsThree : s ≤ 3 := by simpa using hs.2
        rw [hinit s ⟨hs.1, hsThree⟩]
        simp [iwaniecAuxApprox, iwaniecAuxBase, min_eq_left hsThree]
    | succ n ih =>
        intro s hs
        rw [iwaniecAuxiliary_integral_equation sigma f hcont hinit hderiv hs.1]
        change iwaniecAuxBase sigma s + sigma *
          (∫ t in (3 : Real)..(max 3 s), iwaniecAuxDelayKernel t * f (t - 1)) =
          iwaniecAuxBase sigma s + sigma *
          (∫ t in (3 : Real)..(max 3 s),
            iwaniecAuxDelayKernel t * iwaniecAuxApprox sigma n (t - 1))
        apply congrArg (fun value : Real => iwaniecAuxBase sigma s + sigma * value)
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (le_max_left (3 : Real) s)] at ht
        have hupper : max 3 s ≤ (n : Real) + 4 := by
          apply max_le
          · have hn : (0 : Real) ≤ n := by positivity
            linarith
          · have h := hs.2
            push_cast at h
            linarith
        have hlag : t - 1 ∈ Set.Icc (2 : Real) ((n : Real) + 3) := by
          constructor
          · linarith [ht.1]
          · have h := ht.2.trans hupper
            linarith
        dsimp only
        rw [ih (t - 1) hlag]
  intro s hs
  exact hsteps ⌈s⌉₊ s ⟨hs, by have := Nat.le_ceil s; linarith⟩

theorem iwaniecAuxFunction_integral_equation (sigma : Real) {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxFunction sigma s = iwaniecAuxBase sigma s +
      sigma * ∫ t in (3 : Real)..(max 3 s),
        iwaniecAuxDelayKernel t * iwaniecAuxFunction sigma (t - 1) := by
  apply iwaniecAuxiliary_integral_equation sigma (iwaniecAuxFunction sigma)
  · apply (iwaniecAuxFunction_continuousOn sigma).mono
    intro t ht
    change (1 : Real) < t
    have h : 2 ≤ t := ht
    linarith
  · intro t ht
    exact iwaniecAuxFunction_initial sigma ht.2
  · exact fun t ht => iwaniecAuxFunction_hasDerivAt sigma ht
  · exact hs

end

end Erdos1212Kernel
