import Erdos1212Kernel.TaoLittlewoodScaleChoice

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoLittlewoodR_one {T : Real} (hT : 1 < T)
    (hL : 1 < Real.log T) : 1 ≤ taoLittlewoodR T := by
  apply Nat.one_le_ceil_iff.mpr
  have hll : 0 < Real.log (Real.log T) := Real.log_pos hL
  positivity

theorem taoLittlewoodWidth_lt_one_of_large {T : Real}
    (hT : 1 < T) (hL : 1 < Real.log T)
    (hlarge :
      Real.log (Real.log T) ^ 2 /
          (8 * Real.log 2 * Real.log T) ≤
        1 / (4 * (Real.log T) ^ (1 / 8 : Real))) :
    taoLittlewoodWidth T (taoLittlewoodR T) < 1 := by
  have hR := taoLittlewoodR_one hT hL
  have hdecay := taoLittlewoodWidth_le_explicitDecay hT hL hR
    (taoLittlewoodR_lower T) hlarge
  rw [taoExplicitDecayExponent_two_pow hR] at hdecay
  have hr : (0 : Real) < taoLittlewoodR T := by exact_mod_cast hR
  have hpow : 1 ≤ T ^ (1 / (taoLittlewoodR T : Real)) :=
    Real.one_le_rpow hT.le (by positivity)
  have hquarter : 1 / (4 * T ^ (1 / (taoLittlewoodR T : Real))) ≤ (1 : Real) / 4 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hdecay.trans_lt (hquarter.trans_lt (by norm_num))

/-- Fully instantiated finite Littlewood bound: `R` and `J` are now the
canonical ceiling/floor choices, rather than caller-supplied witnesses. -/
theorem riemannZeta_norm_le_littlewood_canonical (t σ : Real)
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
      (((2 ^ taoLittlewoodJ (taoLogFrequency t) : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ taoLittlewoodJ (taoLogFrequency t) : Nat) : Real)) ^ (-σ) *
          (1 + 1 / σ) := by
  have hR := taoLittlewoodR_one hT hL
  exact riemannZeta_norm_le_littlewood_strip t σ
    (taoLittlewoodR (taoLogFrequency t)) (taoLittlewoodJ (taoLogFrequency t))
    hT hL hR hseparation (taoLittlewoodJ_top hT)
    (taoLittlewoodR_lower _) hlarge
    (taoLittlewoodWidth_lt_one_of_large hT hL hlarge) hσlower hσupper

end

end Erdos1212Kernel
