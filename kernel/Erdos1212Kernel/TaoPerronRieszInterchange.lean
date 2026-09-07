import Erdos1212Kernel.TaoPerronRieszSum

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Complex
open scoped ArithmeticFunction BigOperators

set_option maxHeartbeats 1900000

def taoRieszPerronTerm (σ x : Real) (n : Nat) (y : Real) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex) *
    (((n : Real) / x : Complex) ^
      (-((σ : Complex) + (y : Complex) * I))) *
    taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)

theorem norm_taoRieszPerronTerm {σ x : Real} (hx : 0 < x)
    {n : Nat} (hn : 0 < n) (y : Real) :
    ‖taoRieszPerronTerm σ x n y‖ =
      ArithmeticFunction.vonMangoldt n * ((n : Real) / x) ^ (-σ) *
        ‖taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)‖ := by
  unfold taoRieszPerronTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hbase : 0 < (n : Real) / x := div_pos (by exact_mod_cast hn) hx
  have hcast : (((n : Real) : Complex) / (x : Complex)) =
      (((n : Real) / x : Real) : Complex) := by push_cast; rfl
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  simp

theorem integrable_taoRieszPerronTerm {σ x : Real}
    (hσ : 0 < σ) (hx : 0 < x) (n : Nat) :
    Integrable (taoRieszPerronTerm σ x n) := by
  by_cases hn0 : n = 0
  · subst n
    have hzero : taoRieszPerronTerm σ x 0 = 0 := by
      funext y
      unfold taoRieszPerronTerm
      simp
    rw [hzero]
    exact integrable_zero _ _ _
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let A : Real := ArithmeticFunction.vonMangoldt n * ((n : Real) / x) ^ (-σ)
    have hA : 0 ≤ A := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity) _)
    have hk : Integrable (fun y : Real =>
        taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)) :=
      verticalIntegrable_taoRieszMellinKernel hσ
    have hmajor := hk.norm.const_mul A
    apply hmajor.mono'
    · have hp : Continuous (fun y : Real =>
          (((n : Real) / x : Complex) ^
            (-((σ : Complex) + (y : Complex) * I)))) := by
        have hb : ((n : Real) : Complex) / (x : Complex) ≠ 0 := by
          apply div_ne_zero
          · exact_mod_cast (show (n : Real) ≠ 0 by positivity)
          · exact_mod_cast hx.ne'
        have hexp : Continuous (fun y : Real =>
            -((σ : Complex) + (y : Complex) * I)) := by fun_prop
        exact hexp.const_cpow (Or.inl hb)
      have hd : Continuous (fun y : Real =>
          (((σ : Complex) + (y : Complex) * I) *
            (((σ : Complex) + (y : Complex) * I) + 1))) := by fun_prop
      have hdn : ∀ y : Real,
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
      have hkcont : Continuous (fun y : Real =>
          taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)) := by
        unfold taoRieszMellinKernel
        exact continuous_const.div hd hdn
      exact ((continuous_const.mul hp).mul hkcont).aestronglyMeasurable
    · filter_upwards with y
      simpa only [A] using (norm_taoRieszPerronTerm hx hn y).le

theorem integral_norm_taoRieszPerronTerm {σ x : Real}
    (hσ : 0 < σ) (hx : 0 < x) {n : Nat} (hn : 0 < n) :
    (∫ y : Real, ‖taoRieszPerronTerm σ x n y‖) =
      (ArithmeticFunction.vonMangoldt n * ((n : Real) / x) ^ (-σ)) *
        ∫ y : Real, ‖taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)‖ := by
  have hfun : (fun y : Real => ‖taoRieszPerronTerm σ x n y‖) =
      fun (y : Real) => (ArithmeticFunction.vonMangoldt n * ((n : Real) / x) ^ (-σ)) *
        ‖taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)‖ := by
    funext y
    exact norm_taoRieszPerronTerm hx hn y
  rw [hfun, integral_const_mul]

theorem summable_taoRieszPerronCoefficient {σ x : Real}
    (hσ : 1 < σ) (hx : 0 < x) :
    Summable (fun n : Nat =>
      ArithmeticFunction.vonMangoldt n * ((n : Real) / x) ^ (-σ)) := by
  have hσc : 1 < ((σ : Real) : Complex).re := by simpa using hσ
  have hs : Summable (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
      (σ : Complex)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσc
  have hscaled := hs.norm.mul_left (x ^ σ)
  refine hscaled.congr ?_
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : Real) := by exact_mod_cast hn
    rw [LSeries.norm_term_eq]
    simp only [if_neg hn0, Complex.ofReal_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [Real.div_rpow hnR.le hx.le, Real.rpow_neg hnR.le,
      Real.rpow_neg hx.le]
    field_simp [(Real.rpow_pos_of_pos hnR σ).ne',
      (Real.rpow_pos_of_pos hx σ).ne']
    <;> ring

theorem summable_integral_norm_taoRieszPerronTerm {σ x : Real}
    (hσ : 1 < σ) (hx : 0 < x) :
    Summable (fun n : Nat => ∫ y : Real, ‖taoRieszPerronTerm σ x n y‖) := by
  have hcoeff := summable_taoRieszPerronCoefficient hσ hx
  have hscaled := hcoeff.mul_right
    (∫ y : Real, ‖taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)‖)
  refine hscaled.congr ?_
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [taoRieszPerronTerm]
  · exact (integral_norm_taoRieszPerronTerm (by linarith) hx
      (Nat.pos_of_ne_zero hn0)).symm

theorem tsum_integral_taoRieszPerronTerm {σ x : Real}
    (hσ : 1 < σ) (hx : 0 < x) :
    (∑' n : Nat, ∫ y : Real, taoRieszPerronTerm σ x n y) =
      ∫ y : Real, ∑' n : Nat, taoRieszPerronTerm σ x n y := by
  exact integral_tsum_of_summable_integral_norm
    (fun n => integrable_taoRieszPerronTerm (by linarith) hx n)
    (summable_integral_norm_taoRieszPerronTerm hσ hx)

theorem tsum_taoRieszPerronTerm_eq {σ x y : Real}
    (hσ : 1 < σ) (hx : 0 < x) :
    (∑' n : Nat, taoRieszPerronTerm σ x n y) =
      taoZetaLogDerivative ((σ : Complex) + (y : Complex) * I) *
        (x : Complex) ^ ((σ : Complex) + (y : Complex) * I) *
        taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I) := by
  let s : Complex := (σ : Complex) + (y : Complex) * I
  have hsre : 1 < s.re := by simp [s, hσ]
  have hsum : Summable (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hsre
  rw [taoZetaLogDerivative_eq_vonMangoldtLSeries hsre]
  unfold LSeries
  change (∑' n : Nat, taoRieszPerronTerm σ x n y) =
    (∑' n : Nat, LSeries.term
      (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) s n) *
      (x : Complex) ^ s * taoRieszMellinKernel s
  rw [mul_assoc]
  rw [← hsum.tsum_mul_right
    ((x : Complex) ^ s * taoRieszMellinKernel s)]
  apply tsum_congr
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [taoRieszPerronTerm]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : Real) := by exact_mod_cast hn
    have hbase : (((n : Real) : Complex) / (x : Complex)) =
        ((n : Real) : Complex) * (((1 / x : Real)) : Complex) := by
      push_cast
      field_simp [hx.ne']
    have hxinv : (((1 / x : Real)) : Complex) = (x : Complex)⁻¹ := by
      push_cast
      simp [one_div]
    have hxarg : (x : Complex).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact ne_of_lt Real.pi_pos
    have hone : (((1 / x : Real)) : Complex) ^ (-s) =
        (x : Complex) ^ s := by
      rw [hxinv, Complex.inv_cpow_eq_ite, if_neg hxarg,
        Complex.cpow_neg, inv_inv]
    have hnneg : (((n : Real) : Complex) ^ (-s)) =
        (((n : Real) : Complex) ^ s)⁻¹ :=
      Complex.cpow_neg _ _
    unfold taoRieszPerronTerm
    rw [LSeries.term_of_ne_zero hn0, show
      (-((σ : Complex) + (y : Complex) * I)) = -s by rfl,
      hbase, Complex.mul_cpow_ofReal_nonneg hnR.le
        (le_of_lt (one_div_pos.mpr hx)), hnneg, hone]
    simp only [Complex.ofReal_natCast, div_eq_mul_inv]
    ring

theorem taoVonMangoldt_mellinInv_eq_integral_perronTerm
    {σ x : Real} (n : Nat) :
    (ArithmeticFunction.vonMangoldt n : Complex) *
        mellinInv σ taoRieszMellinKernel (n / x) =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ y : Real, taoRieszPerronTerm σ x n y := by
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  calc
    (ArithmeticFunction.vonMangoldt n : Complex) *
        (((1 / (2 * Real.pi) : Real) : Complex) *
          ∫ y : Real, ((n / x : Real) : Complex) ^
            (-((σ : Complex) + (y : Complex) * I)) *
              taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)) =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        ((ArithmeticFunction.vonMangoldt n : Complex) *
          ∫ y : Real, ((n / x : Real) : Complex) ^
            (-((σ : Complex) + (y : Complex) * I)) *
              taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)) := by ring
    _ = ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ y : Real, (ArithmeticFunction.vonMangoldt n : Complex) *
          (((n / x : Real) : Complex) ^
            (-((σ : Complex) + (y : Complex) * I)) *
              taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I)) := by
      rw [integral_const_mul]
    _ = ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ y : Real, taoRieszPerronTerm σ x n y := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      unfold taoRieszPerronTerm
      push_cast
      ring

theorem taoVonMangoldtRieszSum_perron_identity
    {σ x : Real} (hσ : 1 < σ) (hx : 0 < x) :
    taoVonMangoldtRieszSum x =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ y : Real,
          taoZetaLogDerivative ((σ : Complex) + (y : Complex) * I) *
            (x : Complex) ^ ((σ : Complex) + (y : Complex) * I) *
            taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I) := by
  calc
    taoVonMangoldtRieszSum x =
        ∑' n : Nat, (ArithmeticFunction.vonMangoldt n : Complex) *
          taoRieszCutoff (n / x) := (taoVonMangoldtRiesz_tsum_eq x hx).symm
    _ = ∑' n : Nat, (ArithmeticFunction.vonMangoldt n : Complex) *
          mellinInv σ taoRieszMellinKernel (n / x) := by
      apply tsum_congr
      intro n
      exact taoVonMangoldtRiesz_term_mellinInv (by linarith) hx n
    _ = ∑' n : Nat, ((1 / (2 * Real.pi) : Real) : Complex) *
          ∫ y : Real, taoRieszPerronTerm σ x n y := by
      apply tsum_congr
      intro n
      exact taoVonMangoldt_mellinInv_eq_integral_perronTerm n
    _ = ((1 / (2 * Real.pi) : Real) : Complex) *
          ∑' n : Nat, ∫ y : Real, taoRieszPerronTerm σ x n y := by
      exact tsum_mul_left
    _ = ((1 / (2 * Real.pi) : Real) : Complex) *
          ∫ y : Real, ∑' n : Nat, taoRieszPerronTerm σ x n y := by
      rw [tsum_integral_taoRieszPerronTerm hσ hx]
    _ = ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ y : Real,
          taoZetaLogDerivative ((σ : Complex) + (y : Complex) * I) *
            (x : Complex) ^ ((σ : Complex) + (y : Complex) * I) *
            taoRieszMellinKernel ((σ : Complex) + (y : Complex) * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      exact tsum_taoRieszPerronTerm_eq hσ hx

end

end Erdos1212Kernel
