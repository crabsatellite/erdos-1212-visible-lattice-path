import Erdos1212Kernel.TaoZetaGlobalZeroFree
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 1900000

def taoRieszCutoff (x : Real) : Complex :=
  Set.indicator (Set.Ioc (0 : Real) 1) (fun x => ((1 - x : Real) : Complex)) x

def taoRieszMellinKernel (s : Complex) : Complex := 1 / (s * (s + 1))

theorem hasMellin_taoRieszCutoff {s : Complex} (hs : 0 < s.re) :
    HasMellin taoRieszCutoff s (taoRieszMellinKernel s) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : Complex) (s := s) (by simp; linarith)
  have hsub := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at hsub
  convert hsub using 1
  · funext x
    unfold taoRieszCutoff
    by_cases hx : x ∈ Set.Ioc (0 : Real) 1
    · simp only [Set.indicator_of_mem hx]
      simp
    · simp only [Set.indicator_of_notMem hx, sub_zero]
  · unfold taoRieszMellinKernel
    have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
    have hs1 : s + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    field_simp [hs0, hs1]
    ring

theorem continuousAt_taoRieszCutoff {x : Real} (hx : 0 < x) :
    ContinuousAt taoRieszCutoff x := by
  have heq : taoRieszCutoff =ᶠ[nhds x]
      (fun y : Real => ((max 0 (1 - y) : Real) : Complex)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold taoRieszCutoff
    by_cases hy1 : y ≤ 1
    · rw [Set.indicator_of_mem]
      · rw [max_eq_right]
        linarith
      · exact ⟨hy, hy1⟩
    · rw [Set.indicator_of_notMem]
      · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge hy1))]
        norm_num
      · intro hmem
        exact hy1 hmem.2
  exact (by fun_prop : ContinuousAt (fun y : Real =>
    ((max 0 (1 - y) : Real) : Complex)) x).congr_of_eventuallyEq heq

theorem verticalIntegrable_taoRieszMellinKernel {σ : Real} (hσ : 0 < σ) :
    Complex.VerticalIntegrable taoRieszMellinKernel σ := by
  let C : Real := max 1 (1 / σ ^ 2)
  have hC : 0 ≤ C := le_max_left 1 _ |>.trans' zero_le_one
  have hmajor : Integrable (fun y : Real => C * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  apply hmajor.mono'
  · have hd : Continuous (fun y : Real =>
        (((σ : Complex) + (y : Complex) * I) *
          (((σ : Complex) + (y : Complex) * I) + 1))) := by fun_prop
    have hn : ∀ y : Real,
        (((σ : Complex) + (y : Complex) * I) *
          (((σ : Complex) + (y : Complex) * I) + 1)) ≠ 0 := by
      intro y
      apply mul_ne_zero
      · intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      · intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
    unfold taoRieszMellinKernel
    exact (continuous_const.div hd hn).aestronglyMeasurable
  · filter_upwards with y
    let z : Complex := (σ : Complex) + (y : Complex) * I
    have hzNormSq : ‖z‖ ^ 2 = σ ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm]
      simp [z, normSq_apply]
      ring
    have hplus : ‖z‖ ≤ ‖z + 1‖ := by
      apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + 1))).mp
      rw [Complex.sq_norm, Complex.sq_norm]
      simp [z, normSq_apply]
      nlinarith
    have hdenpos : 0 < ‖z‖ * ‖z + 1‖ := by
      have hz : z ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp [z] at hre
        linarith
      have hz1 : z + 1 ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp [z] at hre
        linarith
      positivity
    have hfirst : ‖taoRieszMellinKernel z‖ ≤ 1 / (σ ^ 2 + y ^ 2) := by
      unfold taoRieszMellinKernel
      rw [norm_div, norm_one, norm_mul]
      exact one_div_le_one_div_of_le (by positivity : 0 < σ ^ 2 + y ^ 2) (calc
          σ ^ 2 + y ^ 2 = ‖z‖ ^ 2 := hzNormSq.symm
          _ ≤ ‖z‖ * ‖z + 1‖ := by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_left hplus (norm_nonneg z))
    have hsecond : 1 / (σ ^ 2 + y ^ 2) ≤ C * (1 + y ^ 2)⁻¹ := by
      by_cases hσ1 : 1 ≤ σ ^ 2
      · have hden : 1 + y ^ 2 ≤ σ ^ 2 + y ^ 2 := by linarith
        have hinv := one_div_le_one_div_of_le (by positivity : 0 < 1 + y ^ 2) hden
        have hC1 : 1 ≤ C := le_max_left _ _
        calc
          _ ≤ 1 / (1 + y ^ 2) := hinv
          _ ≤ C * (1 + y ^ 2)⁻¹ := by
            rw [one_div]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1
              (inv_nonneg.mpr (by positivity : 0 ≤ 1 + y ^ 2))
      · have hσsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
        have hσle : σ ^ 2 < 1 := lt_of_not_ge hσ1
        have hCeq : C = 1 / σ ^ 2 := max_eq_right (by
          exact (le_div_iff₀ hσsq).2 (by nlinarith))
        rw [hCeq]
        rw [show 1 / σ ^ 2 * (1 + y ^ 2)⁻¹ =
          1 / (σ ^ 2 * (1 + y ^ 2)) by field_simp [hσsq.ne']]
        exact one_div_le_one_div_of_le (by positivity)
          (by nlinarith [sq_nonneg y])
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (inv_nonneg.mpr (by positivity)))]
      using hfirst.trans hsecond

theorem taoRiesz_mellin_inversion {σ x : Real} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ taoRieszMellinKernel x = taoRieszCutoff x := by
  have hm := hasMellin_taoRieszCutoff (s := (σ : Complex)) (by simpa using hσ)
  have hpoint (y : Real) : mellin taoRieszCutoff
      ((σ : Complex) + (y : Complex) * I) =
      taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I) :=
    (hasMellin_taoRieszCutoff (s := ((σ : Complex) + (y : Complex) * I))
      (by simp [hσ])).2
  have hvert : Complex.VerticalIntegrable (mellin taoRieszCutoff) σ := by
    unfold Complex.VerticalIntegrable
    have heq : (fun y : Real => mellin taoRieszCutoff
        ((σ : Complex) + (y : Complex) * I)) =
        (fun y : Real => taoRieszMellinKernel
          ((σ : Complex) + (y : Complex) * I)) := funext hpoint
    rw [heq]
    exact verticalIntegrable_taoRieszMellinKernel hσ
  have hInv := mellinInv_mellin_eq σ taoRieszCutoff hx hm.1 hvert
    (continuousAt_taoRieszCutoff hx)
  have hinvEq : mellinInv σ (mellin taoRieszCutoff) x =
      mellinInv σ taoRieszMellinKernel x := by
    unfold mellinInv
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [hpoint]
  rw [← hinvEq]
  exact hInv

end

end Erdos1212Kernel
