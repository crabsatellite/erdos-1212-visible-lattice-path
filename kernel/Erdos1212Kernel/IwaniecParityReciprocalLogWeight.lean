import Erdos1212Kernel.IwaniecReciprocalLogProfileWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecParityProfileStart_add_one (r : Nat) :
    iwaniecParityProfileStart r + 1 = (5 + (-1 : Real) ^ r) / 2 := by
  rw [neg_one_pow_eq_ite]
  unfold iwaniecParityProfileStart
  split_ifs <;> norm_num

/-- The nonconstant weight in Corollary 1 to Lemma 13, with `L=log y`. -/
def iwaniecParityReciprocalLogWeight (r : Nat) (L : Real) : Real → Real :=
  iwaniecReciprocalLogWeight L (iwaniecParitySieveProfile r)

theorem iwaniecParityReciprocalLogWeight_nonneg
    (r : Nat) {L x : Real} (hL : 0 < L)
    (hx : x ∈ iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r)) :
    0 ≤ iwaniecParityReciprocalLogWeight r L x := by
  exact iwaniecReciprocalLogWeight_nonneg _ hL
    (zero_lt_one.trans_le (one_le_iwaniecParityProfileStart r))
    (fun _ hs => iwaniecParitySieveProfile_nonneg_exactDomain r hs) hx

theorem iwaniecParityReciprocalLogWeight_continuousOn
    (r : Nat) {L : Real} (hL : 0 < L) :
    ContinuousOn (iwaniecParityReciprocalLogWeight r L)
      (iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r)) := by
  exact iwaniecReciprocalLogWeight_continuousOn _ hL
    (zero_lt_one.trans_le (one_le_iwaniecParityProfileStart r))
    (iwaniecParitySieveProfile_continuousOn_exactDomain r)

theorem iwaniecParityReciprocalLogWeight_monotoneOn
    (r : Nat) {L : Real} (hL : 0 < L) :
    MonotoneOn (iwaniecParityReciprocalLogWeight r L)
      (iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r)) := by
  exact iwaniecReciprocalLogWeight_monotoneOn _ hL
    (zero_lt_one.trans_le (one_le_iwaniecParityProfileStart r))
    (fun _ hs => iwaniecParitySieveProfile_nonneg_exactDomain r hs)
    (iwaniecParitySieveProfile_antitoneOn_exactDomain r)

theorem iwaniecExpReciprocalScale_div_log
    {L x : Real} (hL : L ≠ 0) (hx : 0 < x) :
    iwaniecExpReciprocalScale L (L / Real.log x) = x := by
  unfold iwaniecExpReciprocalScale
  have hquot : L / (L / Real.log x) = Real.log x := by
    by_cases hlog : Real.log x = 0
    · simp [hlog]
    · field_simp [hL, hlog]
  rw [hquot, Real.exp_log hx]

theorem iwaniecWeightedLogKernelIntegral_profile_eval
    (profile : Real → Real) {L B A : Real}
    (hL : 0 < L) (hB : 1 < B) (hBA : B ≤ A) (hA : A < Real.exp L) :
    iwaniecWeightedLogKernelIntegral (iwaniecReciprocalLogWeight L profile) B A =
      L⁻¹ * (∫ t in (L / Real.log A)..(L / Real.log B),
        profile (t - 1) / (t - 1)) := by
  have hAOne := hB.trans_le hBA
  have hlogA := Real.log_pos hAOne
  have hlogB := Real.log_pos hB
  have hAlpha : 1 < L / Real.log A := by
    rw [lt_div_iff₀ hlogA, one_mul]
    exact (Real.log_lt_iff_lt_exp (zero_lt_one.trans hAOne)).2 hA
  have hOrder : L / Real.log A ≤ L / Real.log B := by
    rw [div_le_div_iff₀ hlogA hlogB]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (zero_lt_one.trans hB) hBA) hL.le
  have hchange := iwaniecWeightedLogKernelIntegral_reciprocalLog_change
    profile hL hAlpha hOrder
  rwa [iwaniecExpReciprocalScale_div_log hL.ne' (zero_lt_one.trans hB),
    iwaniecExpReciprocalScale_div_log hL.ne' (zero_lt_one.trans hAOne)] at hchange

/-- Paper Corollary 1 endpoint convention, with its sharp parity-dependent
lower range and its exact integral orientation. -/
theorem iwaniecParityReciprocalLogWeight_integral
    (r : Nat) {L alpha beta : Real} (hL : 0 < L)
    (halpha : (5 + (-1 : Real) ^ r) / 2 ≤ alpha) (hab : alpha ≤ beta) :
    iwaniecWeightedLogKernelIntegral (iwaniecParityReciprocalLogWeight r L)
      (iwaniecExpReciprocalScale L beta) (iwaniecExpReciprocalScale L alpha) =
      L⁻¹ * (∫ t in alpha..beta, iwaniecParitySieveProfile r (t - 1) / (t - 1)) := by
  apply iwaniecWeightedLogKernelIntegral_reciprocalLog_change _ hL _ hab
  rw [← iwaniecParityProfileStart_add_one] at halpha
  have := one_le_iwaniecParityProfileStart r
  linarith

end

end Erdos1212Kernel
