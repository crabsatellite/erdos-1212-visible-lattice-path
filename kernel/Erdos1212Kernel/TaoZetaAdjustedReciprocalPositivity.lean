import Erdos1212Kernel.TaoZetaAdjustedResidualQuantitative

namespace Erdos1212Kernel

noncomputable section

open Metric
open ComplexConjugate

set_option maxHeartbeats 1900000

theorem re_taoZetaAdjustedKernel_eq
    {c ρ : Complex} {R : Real} (hR : 0 < R) (hcρ : c ≠ ρ) :
    (taoZetaAdjustedKernel c R ρ).re =
      (c.re - ρ.re) * (R ^ 2 - Complex.normSq (c - ρ)) /
        (Complex.normSq (c - ρ) * R ^ 2) := by
  have hz : c - ρ ≠ 0 := sub_ne_zero.mpr hcρ
  have hq : Complex.normSq (c - ρ) ≠ 0 :=
    (Complex.normSq_pos.mpr hz).ne'
  have hRcast : (R : Complex) ^ 2 = ((R ^ 2 : Real) : Complex) := by
    norm_cast
  unfold taoZetaAdjustedKernel
  rw [Complex.add_re, one_div, Complex.inv_re, hRcast, Complex.div_re,
    Complex.normSq_ofReal]
  simp only [Complex.conj_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_div, add_zero]
  field_simp [hq, hR.ne']
  ring

theorem re_taoZetaAdjustedKernel_nonneg_of_zetaZero
    {c ρ : Complex} {R : Real} (hR : 0 < R) (hc : 1 < c.re)
    (hρzero : riemannZeta ρ = 0) (hρball : ρ ∈ closedBall c R) :
    0 ≤ (taoZetaAdjustedKernel c R ρ).re := by
  have hρre := taoZetaZero_re_lt_one hρzero
  have hx : 0 < c.re - ρ.re := by linarith
  have hcρ : c ≠ ρ := by
    intro heq
    subst ρ
    linarith
  have hnorm : ‖c - ρ‖ ≤ R := by
    have hdist := mem_closedBall.mp hρball
    rw [Complex.dist_eq] at hdist
    simpa only [norm_sub_rev] using hdist
  have hq : Complex.normSq (c - ρ) ≤ R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [re_taoZetaAdjustedKernel_eq hR hcρ]
  have hqpos : 0 < Complex.normSq (c - ρ) := Complex.normSq_pos.mpr
    (sub_ne_zero.mpr hcρ)
  exact div_nonneg (mul_nonneg hx.le (sub_nonneg.mpr hq))
    (mul_nonneg hqpos.le (sq_nonneg R))

theorem re_taoZetaAdjustedReciprocalSum_nonneg
    {c : Complex} {R : Real} (hR : 0 < R) (hc : 1 < c.re)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1) :
    0 ≤ (taoZetaAdjustedReciprocalSum c R).re := by
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hDnonneg := taoZetaLocalDivisor_nonneg hAvoid
  unfold taoZetaAdjustedReciprocalSum
  rw [complex_re_finset_sum]
  apply Finset.sum_nonneg
  intro ρ hρ
  rw [Complex.mul_re]
  simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
    simpa only [S, Set.Finite.mem_toFinset] using hρ
  have hρzero := taoZetaLocalDivisor_support_riemannZeta_eq_zero hAvoid hρsupport
  have hρU := (taoZetaLocalDivisor c R).supportWithinDomain hρsupport
  exact mul_nonneg (by exact_mod_cast hDnonneg ρ)
    (re_taoZetaAdjustedKernel_nonneg_of_zetaZero hR hc hρzero hρU)

theorem re_taoZetaAdjustedReciprocalSum_ge_kernel
    {c ρ : Complex} {R : Real} (hR : 0 < R) (hc : 1 < c.re)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hρU : ρ ∈ closedBall c R) (hρzero : riemannZeta ρ = 0) :
    (taoZetaAdjustedKernel c R ρ).re ≤
      (taoZetaAdjustedReciprocalSum c R).re := by
  let D := taoZetaLocalDivisor c R
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support :=
    taoZetaZero_mem_localDivisor_support hAvoid hρU hρzero
  have hρS : ρ ∈ S := by simpa only [S, Set.Finite.mem_toFinset]
  have hDnonneg := taoZetaLocalDivisor_nonneg hAvoid
  have hDpos : (1 : Int) ≤ D ρ := by
    have hne : D ρ ≠ 0 := by simpa only [D] using hρsupport
    have hD0 : (0 : Int) ≤ D ρ := by simpa only [D] using hDnonneg ρ
    omega
  have hkernel := re_taoZetaAdjustedKernel_nonneg_of_zetaZero hR hc hρzero hρU
  have htermNonneg : ∀ u ∈ S,
      0 ≤ (((D u : Int) : Complex) * taoZetaAdjustedKernel c R u).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    have husupport : u ∈ (taoZetaLocalDivisor c R).support := by
      simpa only [S, Set.Finite.mem_toFinset] using hu
    have huzero := taoZetaLocalDivisor_support_riemannZeta_eq_zero hAvoid husupport
    have huU := (taoZetaLocalDivisor c R).supportWithinDomain husupport
    exact mul_nonneg (by exact_mod_cast hDnonneg u)
      (re_taoZetaAdjustedKernel_nonneg_of_zetaZero hR hc huzero huU)
  have hsingle :
      (((D ρ : Int) : Complex) * taoZetaAdjustedKernel c R ρ).re ≤
        ∑ u ∈ S, (((D u : Int) : Complex) * taoZetaAdjustedKernel c R u).re := by
    exact Finset.single_le_sum (fun u hu => htermNonneg u hu) hρS
  have hcoeff : (taoZetaAdjustedKernel c R ρ).re ≤
      (((D ρ : Int) : Complex) * taoZetaAdjustedKernel c R ρ).re := by
    rw [Complex.mul_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    have hDreal : (1 : Real) ≤ (D ρ : Int) := by exact_mod_cast hDpos
    nlinarith
  apply hcoeff.trans
  rw [taoZetaAdjustedReciprocalSum, complex_re_finset_sum]
  simpa only [D, S] using hsingle

theorem re_taoZetaAdjustedKernel_same_imaginary
    {σ β t R : Real} (hR : 0 < R) (hβσ : β < σ) :
    (taoZetaAdjustedKernel
      ((σ : Complex) + (t : Complex) * Complex.I) R
      ((β : Complex) + (t : Complex) * Complex.I)).re =
      1 / (σ - β) - (σ - β) / R ^ 2 := by
  let c : Complex := (σ : Complex) + (t : Complex) * Complex.I
  let ρ : Complex := (β : Complex) + (t : Complex) * Complex.I
  have hcρ : c ≠ ρ := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [c, ρ, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero] at hre
    linarith
  have hx : c.re - ρ.re = σ - β := by simp [c, ρ]
  have hq : Complex.normSq (c - ρ) = (σ - β) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [c, ρ]
    ring
  rw [re_taoZetaAdjustedKernel_eq hR hcρ, hx, hq]
  field_simp [hR.ne', sub_ne_zero.mpr (Ne.symm hβσ.ne)]

theorem three_div_four_mul_gap_le_re_taoZetaAdjustedKernel
    {σ β t R : Real} (hR : 0 < R) (hβσ : β < σ)
    (hhalf : 2 * (σ - β) ≤ R) :
    3 / (4 * (σ - β)) ≤
      (taoZetaAdjustedKernel
        ((σ : Complex) + (t : Complex) * Complex.I) R
        ((β : Complex) + (t : Complex) * Complex.I)).re := by
  have hd : 0 < σ - β := sub_pos.mpr hβσ
  have hsq : (2 * (σ - β)) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (by positivity) hhalf 2
  have hsmall : (σ - β) / R ^ 2 ≤ 1 / (4 * (σ - β)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) (by positivity : 0 < 4 * (σ - β))).2
    nlinarith
  rw [re_taoZetaAdjustedKernel_same_imaginary hR hβσ]
  calc
    3 / (4 * (σ - β)) = 1 / (σ - β) - 1 / (4 * (σ - β)) := by
      field_simp [hd.ne']
      norm_num
    _ ≤ 1 / (σ - β) - (σ - β) / R ^ 2 := sub_le_sub_left hsmall _

theorem fifteen_div_sixteen_mul_gap_le_re_taoZetaAdjustedKernel
    {σ β t R : Real} (hR : 0 < R) (hβσ : β < σ)
    (hquarter : 4 * (σ - β) ≤ R) :
    15 / (16 * (σ - β)) ≤
      (taoZetaAdjustedKernel
        ((σ : Complex) + (t : Complex) * Complex.I) R
        ((β : Complex) + (t : Complex) * Complex.I)).re := by
  have hd : 0 < σ - β := sub_pos.mpr hβσ
  have hsq : (4 * (σ - β)) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (by positivity) hquarter 2
  have hsmall : (σ - β) / R ^ 2 ≤ 1 / (16 * (σ - β)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) (by positivity : 0 < 16 * (σ - β))).2
    nlinarith
  rw [re_taoZetaAdjustedKernel_same_imaginary hR hβσ]
  calc
    15 / (16 * (σ - β)) = 1 / (σ - β) - 1 / (16 * (σ - β)) := by
      field_simp [hd.ne']
      norm_num
    _ ≤ 1 / (σ - β) - (σ - β) / R ^ 2 := sub_le_sub_left hsmall _

end

end Erdos1212Kernel
