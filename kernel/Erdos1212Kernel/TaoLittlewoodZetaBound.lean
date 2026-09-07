import Erdos1212Kernel.TaoLittlewoodScale

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

/-- The explicit Littlewood-strip consumer.  All exponential-sum and zeta
inputs have been discharged; only the elementary choice of the two dyadic
indices and a single large-frequency real inequality remain visible. -/
theorem riemannZeta_norm_le_littlewood_strip (t σ : Real) (R J : Nat)
    (hT : 1 < taoLogFrequency t)
    (hL : 1 < Real.log (taoLogFrequency t))
    (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hTop : (((2 ^ J : Nat) : Real)) ≤ taoLogFrequency t)
    (hRlow :
      8 * Real.log (taoLogFrequency t) /
          Real.log (Real.log (taoLogFrequency t)) ≤ (R : Real))
    (hlarge :
      Real.log (Real.log (taoLogFrequency t)) ^ 2 /
          (8 * Real.log 2 * Real.log (taoLogFrequency t)) ≤
        1 / (4 * (Real.log (taoLogFrequency t)) ^ (1 / 8 : Real)))
    (hWidthOne : taoLittlewoodWidth (taoLogFrequency t) R < 1)
    (hσlower : 1 - taoLittlewoodWidth (taoLogFrequency t) R ≤ σ)
    (hσupper : σ ≤ 1) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (J : Real) * (Real.log (taoLogFrequency t) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
      (((2 ^ J : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ J : Nat) : Real)) ^ (-σ) * (1 + 1 / σ) := by
  have ht : t ≠ 0 := by
    intro ht0
    subst t
    norm_num [taoLogFrequency] at hT
  have hwidthPos := taoLittlewoodWidth_pos hL hR
  have hσ0 : 0 < σ := by linarith
  have hwidthDecay : taoLittlewoodWidth (taoLogFrequency t) R ≤
      taoExplicitDecayExponent (taoLogFrequency t) (((2 ^ R : Nat) : Real)) :=
    taoLittlewoodWidth_le_explicitDecay hT hL hR hRlow hlarge
  have hstrip : 1 - σ ≤ taoLittlewoodWidth (taoLogFrequency t) R := by linarith
  have hzeta := riemannZeta_norm_le_of_dyadic_endpoint t σ R J ht hσ0 hσupper
    hR hRJ hT.le hTop (hstrip.trans hwidthDecay)
  have hbase : (1 : Real) ≤ ((2 ^ R : Nat) : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero R (by norm_num)))
  have hsmall : (((2 ^ R : Nat) : Real)) ^ (1 - σ) ≤
      Real.log (taoLogFrequency t) := by
    calc
      (((2 ^ R : Nat) : Real)) ^ (1 - σ) ≤
          (((2 ^ R : Nat) : Real)) ^
            (taoLittlewoodWidth (taoLogFrequency t) R) :=
        Real.rpow_le_rpow_of_exponent_le hbase hstrip
      _ = Real.log (taoLogFrequency t) := taoLittlewood_scale_rpow hL hR
  have hJ : (0 : Real) ≤ J := by positivity
  have hmain : (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
      (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) ≤
      (J : Real) * (Real.log (taoLogFrequency t) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) :=
    mul_le_mul_of_nonneg_left (add_le_add hsmall le_rfl) hJ
  exact hzeta.trans (add_le_add (add_le_add hmain le_rfl) le_rfl)

end

end Erdos1212Kernel
