import Erdos1212Kernel.TaoFiniteDyadicSecondTail

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

/-- Canonical zeta with an Euler cutoff beyond the frequency scale.  The
prefix up to `2^J` uses the arbitrary-order Littlewood estimate; the
remaining blocks up to `2^K` use the uniform k=2 estimate. -/
theorem riemannZeta_norm_le_extended_dyadic_cutoff
    (t σ : Real) (R J K : Nat)
    (ht : t ≠ 0) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 1 ≤ R) (hRJ : R ≤ J) (hJK : J ≤ K)
    (hT1 : 1 ≤ taoLogFrequency t)
    (hTop : (((2 ^ J : Nat) : Real)) ≤ taoLogFrequency t)
    (hWidthR : 1 - σ ≤
      taoExplicitDecayExponent (taoLogFrequency t) (((2 ^ R : Nat) : Real))) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
      ((K - J : Nat) : Real) * ((2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ))) +
      (((2 ^ K : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ K : Nat) : Real)) ^ (-σ) * (1 + 1 / σ) := by
  have hN : 1 ≤ (2 ^ K : Nat) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero K (by norm_num))
  have hzeta := riemannZeta_norm_le_partial_add_correction_add_error
    σ t hσ0 ht (2 ^ K) hN
  have hlow := taoFiniteDyadic_zeta_endpoint_conditions t σ R J ht hσ0.le hσ1
    hR hRJ hT1 hTop hWidthR
  have htail := taoFiniteDyadic_secondDerivative_tail t σ J K ht hσ0.le hσ1 hJK
  have hsplit : (∑ n ∈ Finset.Ico 1 (2 ^ K), taoZetaTerm σ t n) =
      (∑ n ∈ Finset.Ico 1 (2 ^ J), taoZetaTerm σ t n) +
        ∑ n ∈ Finset.Ico (2 ^ J) (2 ^ K), taoZetaTerm σ t n := by
    rw [Finset.sum_Ico_consecutive]
    · exact one_le_pow₀ (by norm_num)
    · exact pow_le_pow_right₀ (by norm_num) hJK
  have hpartial : ‖∑ n ∈ Finset.Ico 1 (2 ^ K), taoZetaTerm σ t n‖ ≤
      (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
      ((K - J : Nat) : Real) * ((2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ))) := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hlow htail)
  exact hzeta.trans (add_le_add (add_le_add hpartial le_rfl) le_rfl)

end

end Erdos1212Kernel
