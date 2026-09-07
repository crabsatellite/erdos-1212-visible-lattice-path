import Erdos1212Kernel.TaoZetaArbitraryWidth
import Erdos1212Kernel.TaoZetaGlobalZeroFree
import Erdos1212Kernel.TaoZetaPoleRemovedGlobal

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 650000

theorem exists_taoPNT_zero_free_disks_any_parameter (d : Real) (hd : 0 < d) :
    ∃ U₀ : Real, ∀ t : Real, U₀ ≤ taoLogFrequency t →
      let L := Real.log (taoPNTFrequency t)
      let δ := d / L
      let α := 1 + δ / 100
      let R := 4 * δ
      0 < δ ∧ R ≤ 1 ∧ 1 < α ∧ α + R ≤ 2 ∧
      ∀ w ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R,
        taoZetaPoleRemoved w ≠ 0 := by
  obtain ⟨Uz, hzero⟩ := exists_riemannZeta_zero_free_region_any_coefficient (1000 * d) (by positivity)
  let U₀ := max (Uz + 2) (max 4 (Real.exp (max 1 (1000 * d))))
  refine ⟨U₀, ?_⟩
  intro t ht
  let U := taoLogFrequency t
  let P := taoPNTFrequency t
  let L := Real.log P
  let δ := d / L
  let α := 1 + δ / 100
  let R := 4 * δ
  have hUz : Uz + 2 ≤ U := (le_max_left _ _).trans ht
  have hU4 : 4 ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hUexp : Real.exp (max 1 (1000 * d)) ≤ U :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hUpos : 0 < U := by linarith
  have hUP : U + 1 ≤ P := by
    have habs : |t| = 2 * Real.pi * U := by dsimp [U, taoLogFrequency]; field_simp
    dsimp [P, taoPNTFrequency]
    rw [habs]
    nlinarith only [hU4, Real.pi_gt_three]
  have hlogU : max 1 (1000 * d) ≤ Real.log U := by
    have hh := Real.log_le_log (Real.exp_pos _) hUexp
    simpa only [Real.log_exp] using hh
  have hlogUP : Real.log U ≤ L := Real.log_le_log hUpos (by linarith only [hUP])
  have hL1 : 1 ≤ L := (le_max_left _ _).trans (hlogU.trans hlogUP)
  have hdL : 1000 * d ≤ L := (le_max_right _ _).trans (hlogU.trans hlogUP)
  have hLpos : 0 < L := by linarith only [hL1]
  have hδpos : 0 < δ := div_pos hd hLpos
  have hδsmall : δ ≤ 1 / 1000 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith only [hdL]
  have hR1 : R ≤ 1 := by dsimp [R]; linarith only [hδsmall]
  have hα : 1 < α := by dsimp [α]; linarith only [hδpos]
  have hright : α + R ≤ 2 := by dsimp [α, R]; linarith only [hδsmall]
  refine ⟨hδpos, hR1, hα, hright, ?_⟩
  intro w hw
  have hdist := mem_ball.mp hw
  have hfreq := abs_taoLogFrequency_sub_le_dist_imaginary_centers w α t
  have hfreq1 : |taoLogFrequency w.im - U| < 1 := hfreq.trans_lt (hdist.trans_le hR1)
  obtain ⟨hflow, hfhigh⟩ := abs_lt.mp hfreq1
  have hwUz : Uz ≤ taoLogFrequency w.im := by linarith only [hflow, hUz]
  have hwU1 : 1 < taoLogFrequency w.im := by linarith only [hflow, hU4]
  have hwlogpos : 0 < Real.log (taoLogFrequency w.im) := Real.log_pos hwU1
  have hwlogle : Real.log (taoLogFrequency w.im) ≤ L :=
    Real.log_le_log (by linarith only [hwU1]) (by linarith only [hfhigh, hUP])
  have hreDist := abs_re_sub_le_dist w ((α : Complex) + (t : Complex) * Complex.I)
  have hcre : (((α : Complex) + (t : Complex) * Complex.I)).re = α := by simp
  rw [hcre] at hreDist
  have hre := (abs_lt.mp (hreDist.trans_lt hdist)).1
  have hwre : 1 - (399 / 100 : Real) * δ < w.re := by
    dsimp [α, R] at hre
    linarith only [hre]
  have hfrac : (399 / 100 : Real) * δ ≤ (1000 * d) / Real.log (taoLogFrequency w.im) := by
    have hmono := div_le_div_of_nonneg_left (by positivity : 0 ≤ 1000 * d) hwlogpos hwlogle
    have hleft : (399 / 100 : Real) * δ ≤ (1000 * d) / L := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hLpos.le
      linarith only [hd]
    exact hleft.trans hmono
  have hz := hzero w.im w.re hwUz (by linarith only [hwre, hfrac])
  apply taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero
  right
  simpa only [Complex.re_add_im] using hz

end

end Erdos1212Kernel
