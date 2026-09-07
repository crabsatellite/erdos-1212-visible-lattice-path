import Erdos1212Kernel.TaoZetaEulerContinuation
import Erdos1212Kernel.TaoFiniteDyadicZetaBlocks

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

/-- The quantitative Euler truncation estimate for mathlib's canonical
`riemannZeta`, throughout the punctured right half-plane. -/
theorem riemannZeta_sub_taoZetaEulerApprox_bound {s : Complex}
    (hs : 0 < s.re) (him : s.im ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ‖riemannZeta s - taoZetaEulerApprox s N‖ ≤
      ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) := by
  rcases lt_trichotomy s.im 0 with himneg | himzero | himpos
  · rw [← taoZetaEulerLimit_eq_riemannZeta_lower ⟨hs, himneg⟩]
    exact taoZetaEulerLimit_truncation_error hs (by
      intro hs1
      apply him
      rw [hs1]
      norm_num) N hN
  · exact False.elim (him himzero)
  · rw [← taoZetaEulerLimit_eq_riemannZeta_upper ⟨hs, himpos⟩]
    exact taoZetaEulerLimit_truncation_error hs (by
      intro hs1
      apply him
      rw [hs1]
      norm_num) N hN

/-- Tao's Euler--Maclaurin formula (Notes 2, equation (21)), now stated
directly for the canonical zeta function and with an explicit error. -/
theorem riemannZeta_euler_formula_bound {s : Complex}
    (hs : 0 < s.re) (him : s.im ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ‖riemannZeta s -
        ((∑ n ∈ Finset.Ico 1 N, (n : Complex) ^ (-s)) +
          (N : Complex) ^ (1 - s) / (s - 1))‖ ≤
      ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) := by
  simpa only [taoZetaEulerApprox] using
    riemannZeta_sub_taoZetaEulerApprox_bound hs him N hN

/-- The same canonical truncation estimate in the real `(σ,t)` coordinates
consumed by the dyadic exponential-sum development. -/
theorem riemannZeta_euler_formula_bound_real (σ t : Real)
    (hσ : 0 < σ) (ht : t ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I) -
        ((∑ n ∈ Finset.Ico 1 N, taoZetaTerm σ t n) +
          (N : Complex) ^ (1 - ((σ : Complex) + (t : Complex) * Complex.I)) /
            (((σ : Complex) + (t : Complex) * Complex.I) - 1))‖ ≤
      ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
        (N : Real) ^ (-σ) * (1 + 1 / σ) := by
  let s : Complex := (σ : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs : 0 < s.re := by simpa only [hsre] using hσ
  have him : s.im ≠ 0 := by simpa only [hsim] using ht
  have h := riemannZeta_euler_formula_bound hs him N hN
  simpa only [s, hsre, taoZetaTerm] using h

end

end Erdos1212Kernel
