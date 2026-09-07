import Erdos1212Kernel.TaoZetaLocalZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem complex_re_finset_sum {α : Type*} (S : Finset α) (f : α → Complex) :
    (∑ x ∈ S, f x).re = ∑ x ∈ S, (f x).re := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, ih, Complex.add_re]

theorem taoZetaZero_re_lt_one {ρ : Complex} (hρ : riemannZeta ρ = 0) :
    ρ.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hρ

theorem taoZetaZero_reciprocal_re_nonneg {s ρ : Complex}
    (hs : 1 < s.re) (hρ : riemannZeta ρ = 0) :
    0 ≤ (1 / (s - ρ)).re := by
  have hre : 0 < (s - ρ).re := by
    rw [Complex.sub_re]
    linarith [taoZetaZero_re_lt_one hρ]
  rw [Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul]
  simpa only [zero_div, add_zero] using
    div_nonneg hre.le (Complex.normSq_nonneg (s - ρ))

theorem taoZetaNearbyReciprocalSum_re_nonneg {s : Complex} {R : Real}
    (hs : 1 < s.re) :
    0 ≤ (taoZetaNearbyReciprocalSum s R).re := by
  unfold taoZetaNearbyReciprocalSum
  have hreSum : (∑ ρ ∈ taoZetaZerosInClosedBall s R, 1 / (s - ρ)).re =
      ∑ ρ ∈ taoZetaZerosInClosedBall s R, (1 / (s - ρ)).re := by
    exact complex_re_finset_sum _ _
  rw [hreSum]
  exact Finset.sum_nonneg fun ρ hρ =>
    taoZetaZero_reciprocal_re_nonneg hs (mem_taoZetaZerosInClosedBall.mp hρ).2

theorem taoZetaNearbyReciprocalSum_re_ge_term {s ρ : Complex} {R : Real}
    (hs : 1 < s.re) (hρmem : ρ ∈ taoZetaZerosInClosedBall s R) :
    (1 / (s - ρ)).re ≤ (taoZetaNearbyReciprocalSum s R).re := by
  unfold taoZetaNearbyReciprocalSum
  have hreSum : (∑ z ∈ taoZetaZerosInClosedBall s R, 1 / (s - z)).re =
      ∑ z ∈ taoZetaZerosInClosedBall s R, (1 / (s - z)).re := by
    exact complex_re_finset_sum _ _
  rw [hreSum]
  have hρzero := (mem_taoZetaZerosInClosedBall.mp hρmem).2
  have hnonneg : ∀ z ∈ (taoZetaZerosInClosedBall s R).erase ρ,
      0 ≤ (1 / (s - z)).re := by
    intro z hz
    exact taoZetaZero_reciprocal_re_nonneg hs
      (mem_taoZetaZerosInClosedBall.mp (Finset.mem_of_mem_erase hz)).2
  rw [← Finset.add_sum_erase _ _ hρmem]
  exact le_add_of_nonneg_right (Finset.sum_nonneg hnonneg)

theorem dist_same_imaginary_part (σ β t : Real) :
    dist ((β : Complex) + (t : Complex) * Complex.I)
      ((σ : Complex) + (t : Complex) * Complex.I) = |σ - β| := by
  rw [Complex.dist_eq, show (β : Complex) + (t : Complex) * Complex.I -
      ((σ : Complex) + (t : Complex) * Complex.I) = ((β - σ : Real) : Complex) by
    push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem same_imaginary_zetaZero_mem_closedBall {σ β t R : Real}
    (hρ : riemannZeta ((β : Complex) + (t : Complex) * Complex.I) = 0)
    (hdist : |σ - β| ≤ R) :
    (β : Complex) + (t : Complex) * Complex.I ∈
      taoZetaZerosInClosedBall ((σ : Complex) + (t : Complex) * Complex.I) R := by
  rw [mem_taoZetaZerosInClosedBall, dist_same_imaginary_part]
  exact ⟨hdist, hρ⟩

end

end Erdos1212Kernel
