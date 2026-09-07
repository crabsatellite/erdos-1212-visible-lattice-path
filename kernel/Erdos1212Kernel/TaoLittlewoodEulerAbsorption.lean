import Erdos1212Kernel.TaoLittlewoodTailAbsorption
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoLogFrequency_abs_identity (t : Real) :
    |t| = 2 * Real.pi * taoLogFrequency t := by
  unfold taoLogFrequency
  field_simp [Real.pi_ne_zero]

theorem taoLittlewood_zeta_denominator_lower (t σ : Real) :
    taoLogFrequency t ≤
      ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ := by
  let z : Complex := ((σ : Complex) + (t : Complex) * Complex.I) - 1
  have him : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    have hz : z.im = t := by simp [z]
    rw [hz] at h
    exact h
  have hpi : (1 : Real) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hT := taoLogFrequency_nonneg t
  have hfreq : taoLogFrequency t ≤ |t| := by
    rw [taoLogFrequency_abs_identity t]
    nlinarith
  exact hfreq.trans him

theorem taoLittlewood_extended_cutoff_lower {T : Real} (hT : 1 < T) :
    T ^ 2 / 4 < (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) := by
  let N : Real := ((2 ^ taoLittlewoodJ T : Nat) : Real)
  have hN : T / 2 < N := by simpa only [N] using taoLittlewoodJ_bottom hT
  have hsq : (T / 2) ^ 2 < N ^ 2 :=
    pow_lt_pow_left₀ hN (by positivity : 0 ≤ T / 2) (by norm_num)
  have hcast : (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) = N ^ 2 := by
    unfold N
    rw [show 2 * taoLittlewoodJ T = taoLittlewoodJ T + taoLittlewoodJ T by omega,
      pow_add]
    push_cast
    ring
  rw [hcast]
  nlinarith

theorem taoLittlewood_euler_correction_le_one {t σ : Real}
    (hT : 2 ≤ taoLogFrequency t) (hσ1 : σ ≤ 1)
    (hdelta : 1 - σ ≤ (1 : Real) / 8) :
    (((2 ^ (2 * taoLittlewoodJ (taoLogFrequency t)) : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ ≤ 1 := by
  let T := taoLogFrequency t
  have hQ := taoLittlewood_extended_cutoff_power (T := T) (σ := σ)
    (by linarith : 1 < T) hσ1 hdelta
  have hpow : T ^ (1 / 4 : Real) ≤ T := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : Real) ≤ T)
        (by norm_num : (1 / 4 : Real) ≤ 1))
  have hden := taoLittlewood_zeta_denominator_lower t σ
  have hnumden : (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) ^ (1 - σ) ≤
      ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ :=
    hQ.trans (hpow.trans hden)
  have hdenpos : 0 < ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ :=
    (by linarith : 0 < T).trans_le hden
  exact (div_le_one hdenpos).2 hnumden

theorem taoLittlewood_complex_parameter_norm_le {t σ : Real}
    (hT : 1 ≤ taoLogFrequency t) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖(σ : Complex) + (t : Complex) * Complex.I‖ ≤
      9 * taoLogFrequency t := by
  let T := taoLogFrequency t
  have habs : |t| = 2 * Real.pi * T := taoLogFrequency_abs_identity t
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    ((σ : Complex) + (t : Complex) * Complex.I)
  have hre : (((σ : Complex) + (t : Complex) * Complex.I).re) = σ := by simp
  have him : (((σ : Complex) + (t : Complex) * Complex.I).im) = t := by simp
  rw [hre, him, abs_of_nonneg hσ0, habs] at hnorm
  dsimp only [T] at hnorm ⊢
  nlinarith [mul_le_mul_of_nonneg_right hT (by norm_num : (0 : Real) ≤ 1)]

theorem taoLittlewood_sigma_reciprocal_factor_le_three {σ : Real}
    (hσ : (7 : Real) / 8 ≤ σ) : 1 + 1 / σ ≤ 3 := by
  have hσp : 0 < σ := by linarith
  have hinv : 1 / σ ≤ 8 / 7 := by
    apply (div_le_div_iff₀ hσp (by norm_num : (0 : Real) < 7)).2
    nlinarith
  linarith

theorem taoLittlewood_euler_remainder_le_128 {t σ : Real}
    (hT : 2 ≤ taoLogFrequency t) (hσ1 : σ ≤ 1)
    (hdelta : 1 - σ ≤ (1 : Real) / 8) (hσ : (7 : Real) / 8 ≤ σ) :
    ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ (2 * taoLittlewoodJ (taoLogFrequency t)) : Nat) : Real)) ^ (-σ) *
          (1 + 1 / σ) ≤ 128 := by
  let T := taoLogFrequency t
  let Q : Real := ((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)
  have hQp : 0 < Q := by unfold Q; positivity
  have hQdelta := taoLittlewood_extended_cutoff_power (T := T) (σ := σ)
    (by linarith : 1 < T) hσ1 hdelta
  have hQlower : T ^ 2 / 4 < Q := by
    simpa only [Q] using taoLittlewood_extended_cutoff_lower (by linarith : 1 < T)
  have hnorm := taoLittlewood_complex_parameter_norm_le (t := t) (σ := σ)
    (by linarith : 1 ≤ taoLogFrequency t) (by linarith) hσ1
  have hfactor := taoLittlewood_sigma_reciprocal_factor_le_three hσ
  have hrewrite : Q ^ (-σ) = Q ^ (1 - σ) / Q := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hQp]
    congr 1 <;> ring
  rw [hrewrite]
  have hTq : T ^ (1 / 4 : Real) ≤ T := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : Real) ≤ T)
        (by norm_num : (1 / 4 : Real) ≤ 1))
  have hnumer : ‖(σ : Complex) + (t : Complex) * Complex.I‖ * Q ^ (1 - σ) ≤
      9 * T * T := mul_le_mul hnorm (hQdelta.trans hTq) (by positivity) (by positivity)
  have hquot : (‖(σ : Complex) + (t : Complex) * Complex.I‖ * Q ^ (1 - σ)) / Q < 36 := by
    apply (div_lt_iff₀ hQp).2
    nlinarith
  calc
    ‖(σ : Complex) + (t : Complex) * Complex.I‖ * (Q ^ (1 - σ) / Q) *
          (1 + 1 / σ) =
        ((‖(σ : Complex) + (t : Complex) * Complex.I‖ * Q ^ (1 - σ)) / Q) *
          (1 + 1 / σ) := by ring
    _ ≤ 36 * 3 := mul_le_mul hquot.le hfactor (by positivity) (by norm_num)
    _ ≤ 128 := by norm_num

end

end Erdos1212Kernel
