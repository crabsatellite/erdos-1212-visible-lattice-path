import Erdos1212Kernel.TaoZetaExtendedCutoff

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

/-- Canonical Littlewood scales with the Euler cutoff moved to
`2^(2J)`, so the k=2 dyadic tail and Euler remainder carry a negative
power of the frequency. -/
theorem riemannZeta_norm_le_littlewood_extended_canonical
    (t σ : Real)
    (hT : 1 < taoLogFrequency t)
    (hL : 1 < Real.log (taoLogFrequency t))
    (hlarge :
      Real.log (Real.log (taoLogFrequency t)) ^ 2 /
          (8 * Real.log 2 * Real.log (taoLogFrequency t)) ≤
        1 / (4 * (Real.log (taoLogFrequency t)) ^ (1 / 8 : Real)))
    (hseparation :
      taoLittlewoodR (taoLogFrequency t) ≤ taoLittlewoodJ (taoLogFrequency t))
    (hσlower :
      1 - taoLittlewoodWidth (taoLogFrequency t)
          (taoLittlewoodR (taoLogFrequency t)) ≤ σ)
    (hσupper : σ ≤ 1) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (taoLittlewoodJ (taoLogFrequency t) : Real) *
        (Real.log (taoLogFrequency t) +
          (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
      (taoLittlewoodJ (taoLogFrequency t) : Real) * ((2 : Real) ^ 20 *
        (((((2 ^ (2 * taoLittlewoodJ (taoLogFrequency t)) : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ taoLittlewoodJ (taoLogFrequency t) : Nat) : Real)) ^ (-σ))) +
      (((2 ^ (2 * taoLittlewoodJ (taoLogFrequency t)) : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ (2 * taoLittlewoodJ (taoLogFrequency t)) : Nat) : Real)) ^ (-σ) *
          (1 + 1 / σ) := by
  let T := taoLogFrequency t
  let R := taoLittlewoodR T
  let J := taoLittlewoodJ T
  have ht : t ≠ 0 := by
    intro ht0
    subst t
    norm_num [T, taoLogFrequency] at hT
  have hR : 1 ≤ R := taoLittlewoodR_one hT hL
  have hwidthPos : 0 < taoLittlewoodWidth T R := taoLittlewoodWidth_pos hL hR
  have hwidthOne : taoLittlewoodWidth T R < 1 :=
    taoLittlewoodWidth_lt_one_of_large hT hL hlarge
  have hσ0 : 0 < σ := by linarith
  have hstrip : 1 - σ ≤ taoLittlewoodWidth T R := by linarith
  have hwidthDecay : taoLittlewoodWidth T R ≤
      taoExplicitDecayExponent T (((2 ^ R : Nat) : Real)) :=
    taoLittlewoodWidth_le_explicitDecay hT hL hR (taoLittlewoodR_lower T) hlarge
  have hbase := riemannZeta_norm_le_extended_dyadic_cutoff t σ R J (2 * J)
    ht hσ0 hσupper hR hseparation (by omega) hT.le
    (taoLittlewoodJ_top hT) (hstrip.trans hwidthDecay)
  have hbaseR : (1 : Real) ≤ ((2 ^ R : Nat) : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero R (by norm_num)))
  have hsmall : (((2 ^ R : Nat) : Real)) ^ (1 - σ) ≤ Real.log T := by
    calc
      _ ≤ (((2 ^ R : Nat) : Real)) ^ (taoLittlewoodWidth T R) :=
        Real.rpow_le_rpow_of_exponent_le hbaseR hstrip
      _ = Real.log T := taoLittlewood_scale_rpow hL hR
  have hJ0 : (0 : Real) ≤ J := by positivity
  have hlow : (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
      (2 : Real) ^ 42 * Real.log (2 + T)) ≤
      (J : Real) * (Real.log T + (2 : Real) ^ 42 * Real.log (2 + T)) :=
    mul_le_mul_of_nonneg_left (add_le_add hsmall le_rfl) hJ0
  have hsub : 2 * J - J = J := by omega
  rw [hsub] at hbase
  dsimp only [T, R, J] at hbase hlow ⊢
  exact hbase.trans (add_le_add (add_le_add (add_le_add hlow le_rfl) le_rfl) le_rfl)

end

end Erdos1212Kernel
