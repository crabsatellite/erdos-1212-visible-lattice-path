import Erdos1212Kernel.TaoZetaEulerCanonicalTruncation
import Erdos1212Kernel.TaoDyadicEndpointConditions

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoZetaEulerCorrection_norm (σ t : Real) (N : Nat) (hN : 1 ≤ N) :
    ‖(N : Complex) ^ (1 - ((σ : Complex) + (t : Complex) * Complex.I)) /
        (((σ : Complex) + (t : Complex) * Complex.I) - 1)‖ =
      (N : Real) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ := by
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Complex.norm_div]
  change ‖(((N : Real) : Complex) ^
      (1 - ((σ : Complex) + (t : Complex) * Complex.I)))‖ /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  simp

/-- Canonical zeta is bounded by a literal Dirichlet prefix, the explicit
Euler correction, and the explicit Euler remainder. -/
theorem riemannZeta_norm_le_partial_add_correction_add_error (σ t : Real)
    (hσ : 0 < σ) (ht : t ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      ‖∑ n ∈ Finset.Ico 1 N, taoZetaTerm σ t n‖ +
        (N : Real) ^ (1 - σ) /
          ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
        ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
          (N : Real) ^ (-σ) * (1 + 1 / σ) := by
  let s : Complex := (σ : Complex) + (t : Complex) * Complex.I
  let P : Complex := ∑ n ∈ Finset.Ico 1 N, taoZetaTerm σ t n
  let C : Complex :=
    (N : Complex) ^ (1 - s) / (s - 1)
  let E : Real := ‖s‖ * (N : Real) ^ (-σ) * (1 + 1 / σ)
  have hEuler : ‖riemannZeta s - (P + C)‖ ≤ E := by
    simpa only [s, P, C, E] using
      riemannZeta_euler_formula_bound_real σ t hσ ht N hN
  have hdecomp : riemannZeta s = (riemannZeta s - (P + C)) + (P + C) := by ring
  have hmain : ‖riemannZeta s‖ ≤ ‖P‖ + ‖C‖ + E := by
    rw [hdecomp]
    calc
      ‖(riemannZeta s - (P + C)) + (P + C)‖ ≤
          ‖riemannZeta s - (P + C)‖ + ‖P + C‖ := norm_add_le _ _
      _ ≤ E + (‖P‖ + ‖C‖) := add_le_add hEuler (norm_add_le _ _)
      _ = ‖P‖ + ‖C‖ + E := by ring
  have hC : ‖C‖ = (N : Real) ^ (1 - σ) / ‖s - 1‖ := by
    simpa only [C, s] using taoZetaEulerCorrection_norm σ t N hN
  simpa only [s, P, E, hC] using hmain

/-- The exact consumer joining the endpoint-driven mixed dyadic bound to the
canonical zeta function at the dyadic truncation `N = 2^J`. -/
theorem riemannZeta_norm_le_of_dyadic_endpoint (t σ : Real) (R J : Nat)
    (ht : t ≠ 0) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hT1 : 1 ≤ taoLogFrequency t)
    (hTop : (((2 ^ J : Nat) : Real)) ≤ taoLogFrequency t)
    (hWidthR : 1 - σ ≤
      taoExplicitDecayExponent (taoLogFrequency t) (((2 ^ R : Nat) : Real))) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
      (((2 ^ J : Nat) : Real)) ^ (1 - σ) /
        ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (((2 ^ J : Nat) : Real)) ^ (-σ) * (1 + 1 / σ) := by
  have hN : 1 ≤ (2 ^ J : Nat) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero J (by norm_num))
  have hzeta := riemannZeta_norm_le_partial_add_correction_add_error σ t hσ0 ht
    (2 ^ J) hN
  have hpartial := taoFiniteDyadic_zeta_endpoint_conditions t σ R J ht hσ0.le hσ1
    hR hRJ hT1 hTop hWidthR
  exact hzeta.trans (add_le_add (add_le_add hpartial le_rfl) le_rfl)

end

end Erdos1212Kernel
