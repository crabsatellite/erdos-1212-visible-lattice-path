import Erdos1212Kernel.TaoPerronContourRegularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 1900000

theorem tao_horizontal_inv_integral_eq_log_sub
    {a b Y : Real} (hY : Y ≠ 0) :
    (∫ u : Real in a..b,
        1 / (((u : Complex) - 1) + (Y : Complex) * I)) =
      Complex.log (((b : Complex) - 1) + (Y : Complex) * I) -
        Complex.log (((a : Complex) - 1) + (Y : Complex) * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _hu
    have hinner : HasDerivAt
        (fun v : Real => ((v : Complex) - 1) + (Y : Complex) * I) 1 u := by
      have hc : HasDerivAt
          (fun z : Complex => (z - 1) + (Y : Complex) * I) 1 (u : Complex) := by
        exact ((hasDerivAt_id (x := (u : Complex))).sub_const 1).add_const
          ((Y : Complex) * I)
      exact hc.comp_ofReal
    have hslit : ((u : Complex) - 1) + (Y : Complex) * I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      simpa using hY
    simpa only [one_div] using hinner.clog_real hslit
  · apply ContinuousOn.intervalIntegrable
    intro u _hu
    have hne : ((u : Complex) - 1) + (Y : Complex) * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact hY him
    have hnum : ContinuousAt (fun _ : Real => (1 : Complex)) u := continuousAt_const
    have hden : ContinuousAt
        (fun v : Real => ((v : Complex) - 1) + (Y : Complex) * I) u := by
      fun_prop
    exact (hnum.div hden hne).continuousWithinAt

theorem tao_vertical_inv_integral_eq_log_sub
    {A a b : Real} (hA : 1 < A) :
    I * (∫ v : Real in a..b,
        1 / (((A : Complex) - 1) + (v : Complex) * I)) =
      Complex.log (((A : Complex) - 1) + (b : Complex) * I) -
        Complex.log (((A : Complex) - 1) + (a : Complex) * I) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v _hv
    have hinner : HasDerivAt
        (fun t : Real => ((A : Complex) - 1) + (t : Complex) * I) I v := by
      have hc : HasDerivAt
          (fun z : Complex => ((A : Complex) - 1) + z * I) I (v : Complex) := by
        simpa only [Pi.add_apply, id_eq, zero_add, one_mul] using
          (((hasDerivAt_const (x := (v : Complex)) (c := (A : Complex))).sub_const 1).add
            ((hasDerivAt_id (x := (v : Complex))).mul_const I))
      exact hc.comp_ofReal
    have hslit : ((A : Complex) - 1) + (v : Complex) * I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp
      linarith
    convert hinner.clog_real hslit using 1 <;> ring
  · apply ContinuousOn.intervalIntegrable
    intro v _hv
    have hne : ((A : Complex) - 1) + (v : Complex) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hnum : ContinuousAt (fun _ : Real => (1 : Complex)) v := continuousAt_const
    have hden : ContinuousAt
        (fun t : Real => ((A : Complex) - 1) + (t : Complex) * I) v := by
      fun_prop
    exact ((continuousAt_const.mul (hnum.div hden hne))).continuousWithinAt

theorem tao_vertical_inv_integral_negBranch_eq_log_sub
    {A a b : Real} (hA : A < 1) :
    I * (∫ v : Real in a..b,
        1 / (((A : Complex) - 1) + (v : Complex) * I)) =
      Complex.log (-(((A : Complex) - 1) + (b : Complex) * I)) -
        Complex.log (-(((A : Complex) - 1) + (a : Complex) * I)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v _hv
    have horiginal : HasDerivAt
        (fun t : Real => ((A : Complex) - 1) + (t : Complex) * I) I v := by
      have hc : HasDerivAt
          (fun z : Complex => ((A : Complex) - 1) + z * I) I (v : Complex) := by
        simpa only [Pi.add_apply, id_eq, zero_add, one_mul] using
          (((hasDerivAt_const (x := (v : Complex)) (c := (A : Complex))).sub_const 1).add
            ((hasDerivAt_id (x := (v : Complex))).mul_const I))
      exact hc.comp_ofReal
    have hinner : HasDerivAt
        (fun t : Real => -(((A : Complex) - 1) + (t : Complex) * I)) (-I) v :=
      horiginal.neg
    have hslit : -(((A : Complex) - 1) + (v : Complex) * I) ∈
        Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp
      linarith
    convert hinner.clog_real hslit using 1 <;> field_simp <;> ring
  · apply ContinuousOn.intervalIntegrable
    intro v _hv
    have hne : ((A : Complex) - 1) + (v : Complex) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hnum : ContinuousAt (fun _ : Real => (1 : Complex)) v := continuousAt_const
    have hden : ContinuousAt
        (fun t : Real => ((A : Complex) - 1) + (t : Complex) * I) v := by
      fun_prop
    exact ((continuousAt_const.mul (hnum.div hden hne))).continuousWithinAt

theorem complex_log_neg_eq_log_add_pi_mul_I_of_im_neg
    {z : Complex} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : Complex) * I := by
  apply Complex.ext
  · simp only [Complex.log_re, Complex.neg_re, norm_neg, add_re,
      mul_re, Complex.ofReal_re, I_re, Complex.ofReal_im, I_im]
    ring
  · simp only [Complex.log_im, Complex.neg_im, add_im,
      mul_im, Complex.ofReal_re, I_im, Complex.ofReal_im, I_re]
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
    ring

theorem complex_log_neg_eq_log_sub_pi_mul_I_of_im_pos
    {z : Complex} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : Complex) * I := by
  apply Complex.ext
  · simp only [Complex.log_re, Complex.neg_re, norm_neg, sub_re,
      mul_re, Complex.ofReal_re, I_re, Complex.ofReal_im, I_im]
    ring
  · simp only [Complex.log_im, Complex.neg_im, sub_im,
      mul_im, Complex.ofReal_re, I_im, Complex.ofReal_im, I_re]
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
    ring

theorem tao_rectangle_inv_sub_one_boundary_eq_two_pi_I
    {β σ T : Real} (hβ : β < 1) (hσ : 1 < σ) (hT : 0 < T) :
    (∫ u : Real in β..σ,
        1 / (((u : Complex) - 1) + ((-T : Real) : Complex) * I)) -
      (∫ u : Real in β..σ,
        1 / (((u : Complex) - 1) + (T : Complex) * I)) +
      I * (∫ v : Real in (-T)..T,
        1 / (((σ : Complex) - 1) + (v : Complex) * I)) -
      I * (∫ v : Real in (-T)..T,
        1 / (((β : Complex) - 1) + (v : Complex) * I)) =
      2 * (Real.pi : Complex) * I := by
  have hbottom := tao_horizontal_inv_integral_eq_log_sub
    (a := β) (b := σ) (Y := -T) (neg_ne_zero.mpr hT.ne')
  have htop := tao_horizontal_inv_integral_eq_log_sub
    (a := β) (b := σ) (Y := T) hT.ne'
  have hright := tao_vertical_inv_integral_eq_log_sub
    (A := σ) (a := -T) (b := T) hσ
  have hleft := tao_vertical_inv_integral_negBranch_eq_log_sub
    (A := β) (a := -T) (b := T) hβ
  rw [hbottom, htop, hright, hleft]
  let Lb : Complex := ((β : Complex) - 1) + ((-T : Real) : Complex) * I
  let Lt : Complex := ((β : Complex) - 1) + (T : Complex) * I
  have hLbIm : Lb.im < 0 := by simp [Lb, hT]
  have hLtIm : 0 < Lt.im := by simp [Lt, hT]
  have hlogb := complex_log_neg_eq_log_add_pi_mul_I_of_im_neg hLbIm
  have hlogt := complex_log_neg_eq_log_sub_pi_mul_I_of_im_pos hLtIm
  change Complex.log (((σ : Complex) - 1) + ((-T : Real) : Complex) * I) -
      Complex.log Lb -
      (Complex.log (((σ : Complex) - 1) + (T : Complex) * I) -
        Complex.log Lt) +
      (Complex.log (((σ : Complex) - 1) + (T : Complex) * I) -
        Complex.log (((σ : Complex) - 1) + ((-T : Real) : Complex) * I)) -
      (Complex.log (-Lt) - Complex.log (-Lb)) =
        2 * (Real.pi : Complex) * I
  rw [hlogb, hlogt]
  ring

theorem tao_rectangle_const_mul_inv_sub_one_boundary
    {β σ T : Real} (c : Complex)
    (hβ : β < 1) (hσ : 1 < σ) (hT : 0 < T) :
    (∫ u : Real in β..σ,
        c * (1 / (((u : Complex) - 1) + ((-T : Real) : Complex) * I))) -
      (∫ u : Real in β..σ,
        c * (1 / (((u : Complex) - 1) + (T : Complex) * I))) +
      I * (∫ v : Real in (-T)..T,
        c * (1 / (((σ : Complex) - 1) + (v : Complex) * I))) -
      I * (∫ v : Real in (-T)..T,
        c * (1 / (((β : Complex) - 1) + (v : Complex) * I))) =
      c * (2 * (Real.pi : Complex) * I) := by
  simp_rw [intervalIntegral.integral_const_mul]
  have hbase := tao_rectangle_inv_sub_one_boundary_eq_two_pi_I hβ hσ hT
  linear_combination c * hbase

theorem intervalIntegrable_tao_horizontal_const_mul_inv
    {a b Y : Real} (c : Complex) (hY : Y ≠ 0) :
    IntervalIntegrable (fun u : Real =>
      c * (1 / (((u : Complex) - 1) + (Y : Complex) * I))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u _hu
  have hne : ((u : Complex) - 1) + (Y : Complex) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hY him
  have hnum : ContinuousAt (fun _ : Real => (1 : Complex)) u := continuousAt_const
  have hden : ContinuousAt
      (fun v : Real => ((v : Complex) - 1) + (Y : Complex) * I) u := by
    fun_prop
  exact (continuousWithinAt_const.mul
    (hnum.div hden hne).continuousWithinAt)

theorem intervalIntegrable_tao_vertical_const_mul_inv
    {a b A : Real} (c : Complex) (hA : A ≠ 1) :
    IntervalIntegrable (fun v : Real =>
      c * (1 / (((A : Complex) - 1) + (v : Complex) * I))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro v _hv
  have hne : ((A : Complex) - 1) + (v : Complex) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hA (by linarith)
  have hnum : ContinuousAt (fun _ : Real => (1 : Complex)) v := continuousAt_const
  have hden : ContinuousAt
      (fun t : Real => ((A : Complex) - 1) + (t : Complex) * I) v := by
    fun_prop
  exact (continuousWithinAt_const.mul
    (hnum.div hden hne).continuousWithinAt)

theorem taoPerron_decomposed_rectangle_boundary
    {β σ T x : Real} (hβ0 : 0 < β) (hβ : β < 1) (hσ : 1 < σ)
    (hT : 0 < T) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    (∫ u : Real in β..σ,
        (x : Complex) / 2 *
            (1 / (((u : Complex) - 1) + ((-T : Real) : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((u : Complex) + ((-T : Real) : Complex) * I)) -
      (∫ u : Real in β..σ,
        (x : Complex) / 2 *
            (1 / (((u : Complex) - 1) + (T : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((u : Complex) + (T : Complex) * I)) +
      I * (∫ v : Real in (-T)..T,
        (x : Complex) / 2 *
            (1 / (((σ : Complex) - 1) + (v : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((σ : Complex) + (v : Complex) * I)) -
      I * (∫ v : Real in (-T)..T,
        (x : Complex) / 2 *
            (1 / (((β : Complex) - 1) + (v : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((β : Complex) + (v : Complex) * I)) =
      (x : Complex) * (Real.pi : Complex) * I := by
  have hβσ : β ≤ σ := hβ.le.trans hσ.le
  have hT0 : 0 ≤ T := hT.le
  have hcont := continuousOn_taoPerronHolomorphicRemainder_rectangle
    (β := β) (σ := σ) (T := T) hβ0 hx hzero
  have hRb : IntervalIntegrable (fun u : Real =>
      taoPerronHolomorphicRemainder x
        ((u : Complex) + ((-T : Real) : Complex) * I)) volume β σ := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le hβσ] at hu
    rw [Complex.mem_reProdIm]
    simpa using (show u ∈ Set.Icc β σ ∧ -T ≤ -T ∧ -T ≤ T from
      ⟨hu, le_rfl, neg_le_self hT0⟩)
  have hRt : IntervalIntegrable (fun u : Real =>
      taoPerronHolomorphicRemainder x
        ((u : Complex) + (T : Complex) * I)) volume β σ := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le hβσ] at hu
    rw [Complex.mem_reProdIm]
    simpa using (show u ∈ Set.Icc β σ ∧ -T ≤ T ∧ T ≤ T from
      ⟨hu, neg_le_self hT0, le_rfl⟩)
  have hRr : IntervalIntegrable (fun v : Real =>
      taoPerronHolomorphicRemainder x
        ((σ : Complex) + (v : Complex) * I)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro v hv
    rw [Set.uIcc_of_le (neg_le_self hT0)] at hv
    rw [Complex.mem_reProdIm]
    simpa using (show β ≤ σ ∧ σ ≤ σ ∧ v ∈ Set.Icc (-T) T from
      ⟨hβσ, le_rfl, hv⟩)
  have hRl : IntervalIntegrable (fun v : Real =>
      taoPerronHolomorphicRemainder x
        ((β : Complex) + (v : Complex) * I)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro v hv
    rw [Set.uIcc_of_le (neg_le_self hT0)] at hv
    rw [Complex.mem_reProdIm]
    simpa using (show β ≤ β ∧ β ≤ σ ∧ v ∈ Set.Icc (-T) T from
      ⟨le_rfl, hβσ, hv⟩)
  have hPb := intervalIntegrable_tao_horizontal_const_mul_inv
    ((x : Complex) / 2) (a := β) (b := σ) (Y := -T)
      (neg_ne_zero.mpr hT.ne')
  have hPt := intervalIntegrable_tao_horizontal_const_mul_inv
    ((x : Complex) / 2) (a := β) (b := σ) (Y := T) hT.ne'
  have hPr := intervalIntegrable_tao_vertical_const_mul_inv
    ((x : Complex) / 2) (a := -T) (b := T) (A := σ) hσ.ne'
  have hPl := intervalIntegrable_tao_vertical_const_mul_inv
    ((x : Complex) / 2) (a := -T) (b := T) (A := β) hβ.ne
  rw [intervalIntegral.integral_add hPb hRb,
    intervalIntegral.integral_add hPt hRt,
    intervalIntegral.integral_add hPr hRr,
    intervalIntegral.integral_add hPl hRl]
  have hpole := tao_rectangle_const_mul_inv_sub_one_boundary
    ((x : Complex) / 2) hβ hσ hT
  have hrem := taoPerronHolomorphicRemainder_rectangle_boundary_eq_zero
    hβ0 hβσ hT0 hx hzero
  linear_combination hpole + hrem

def taoPerronFullIntegrand (x : Real) (s : Complex) : Complex :=
  taoZetaLogDerivative s * taoPerronAnalyticFactor x s

theorem taoPerronFullIntegrand_rectangle_boundary
    {β σ T x : Real} (hβ0 : 0 < β) (hβ : β < 1) (hσ : 1 < σ)
    (hT : 0 < T) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    (∫ u : Real in β..σ,
        taoPerronFullIntegrand x
          ((u : Complex) + ((-T : Real) : Complex) * I)) -
      (∫ u : Real in β..σ,
        taoPerronFullIntegrand x
          ((u : Complex) + (T : Complex) * I)) +
      I * (∫ v : Real in (-T)..T,
        taoPerronFullIntegrand x
          ((σ : Complex) + (v : Complex) * I)) -
      I * (∫ v : Real in (-T)..T,
        taoPerronFullIntegrand x
          ((β : Complex) + (v : Complex) * I)) =
      (x : Complex) * (Real.pi : Complex) * I := by
  have hβσ : β ≤ σ := hβ.le.trans hσ.le
  have hT0 : 0 ≤ T := hT.le
  have hdecomp {s : Complex}
      (hmem : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T) (hs : s ≠ 1) :
      taoPerronFullIntegrand x s =
        ((x : Complex) / 2) / (s - 1) +
          taoPerronHolomorphicRemainder x s := by
    unfold taoPerronFullIntegrand
    exact taoPerron_full_integrand_decomposition hs
      ((hzero s hmem).resolve_left hs)
  have hbottom (u : Real) (hu : u ∈ Set.Icc β σ) :
      taoPerronFullIntegrand x
          ((u : Complex) + ((-T : Real) : Complex) * I) =
        (x : Complex) / 2 *
            (1 / (((u : Complex) - 1) + ((-T : Real) : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((u : Complex) + ((-T : Real) : Complex) * I) := by
    let s : Complex := (u : Complex) + ((-T : Real) : Complex) * I
    have hs : s ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp [s] at him
      linarith
    have hmem : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [s, add_re, Complex.ofReal_re, mul_re, I_re, Complex.ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.mem_Icc, add_im,
        mul_im, mul_one, zero_add]
      exact ⟨hu, le_rfl, neg_le_self hT0⟩
    have hd := hdecomp hmem hs
    rw [show s - 1 = ((u : Complex) - 1) + ((-T : Real) : Complex) * I by
      simp [s]; ring] at hd
    simpa only [s, div_eq_mul_inv, one_div, one_mul] using hd
  have htop (u : Real) (hu : u ∈ Set.Icc β σ) :
      taoPerronFullIntegrand x ((u : Complex) + (T : Complex) * I) =
        (x : Complex) / 2 *
            (1 / (((u : Complex) - 1) + (T : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((u : Complex) + (T : Complex) * I) := by
    let s : Complex := (u : Complex) + (T : Complex) * I
    have hs : s ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp [s] at him
      linarith
    have hmem : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [s, add_re, Complex.ofReal_re, mul_re, I_re, Complex.ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.mem_Icc, add_im,
        mul_im, mul_one, zero_add]
      exact ⟨hu, neg_le_self hT0, le_rfl⟩
    have hd := hdecomp hmem hs
    rw [show s - 1 = ((u : Complex) - 1) + (T : Complex) * I by
      simp [s]; ring] at hd
    simpa only [s, div_eq_mul_inv, one_div, one_mul] using hd
  have hright (v : Real) (hv : v ∈ Set.Icc (-T) T) :
      taoPerronFullIntegrand x ((σ : Complex) + (v : Complex) * I) =
        (x : Complex) / 2 *
            (1 / (((σ : Complex) - 1) + (v : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((σ : Complex) + (v : Complex) * I) := by
    let s : Complex := (σ : Complex) + (v : Complex) * I
    have hs : s ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hmem : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [s, add_re, Complex.ofReal_re, mul_re, I_re, Complex.ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.mem_Icc, add_im,
        mul_im, mul_one, zero_add]
      exact ⟨⟨hβσ, le_rfl⟩, hv⟩
    have hd := hdecomp hmem hs
    rw [show s - 1 = ((σ : Complex) - 1) + (v : Complex) * I by
      simp [s]; ring] at hd
    simpa only [s, div_eq_mul_inv, one_div, one_mul] using hd
  have hleft (v : Real) (hv : v ∈ Set.Icc (-T) T) :
      taoPerronFullIntegrand x ((β : Complex) + (v : Complex) * I) =
        (x : Complex) / 2 *
            (1 / (((β : Complex) - 1) + (v : Complex) * I)) +
          taoPerronHolomorphicRemainder x
            ((β : Complex) + (v : Complex) * I) := by
    let s : Complex := (β : Complex) + (v : Complex) * I
    have hs : s ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hmem : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [s, add_re, Complex.ofReal_re, mul_re, I_re, Complex.ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.mem_Icc, add_im,
        mul_im, mul_one, zero_add]
      exact ⟨⟨le_rfl, hβσ⟩, hv⟩
    have hd := hdecomp hmem hs
    rw [show s - 1 = ((β : Complex) - 1) + (v : Complex) * I by
      simp [s]; ring] at hd
    simpa only [s, div_eq_mul_inv, one_div, one_mul] using hd
  rw [intervalIntegral.integral_congr (fun u hu => hbottom u (by
      simpa only [Set.uIcc_of_le hβσ] using hu)),
    intervalIntegral.integral_congr (fun u hu => htop u (by
      simpa only [Set.uIcc_of_le hβσ] using hu)),
    intervalIntegral.integral_congr (fun v hv => hright v (by
      simpa only [Set.uIcc_of_le (neg_le_self hT0)] using hv)),
    intervalIntegral.integral_congr (fun v hv => hleft v (by
      simpa only [Set.uIcc_of_le (neg_le_self hT0)] using hv))]
  exact taoPerron_decomposed_rectangle_boundary hβ0 hβ hσ hT hx hzero

theorem exists_taoPerronFullIntegrand_zero_free_rectangle_boundary :
    ∃ c : Real, 0 < c ∧
      ∀ H β σ T x : Real,
        0 ≤ H → 0 < T → T ≤ H →
        0 < β → β < 1 → 1 < σ → 0 < x →
        1 - c / Real.log (3 + H) < β →
        (∫ u : Real in β..σ,
            taoPerronFullIntegrand x
              ((u : Complex) + ((-T : Real) : Complex) * I)) -
          (∫ u : Real in β..σ,
            taoPerronFullIntegrand x
              ((u : Complex) + (T : Complex) * I)) +
          I * (∫ v : Real in (-T)..T,
            taoPerronFullIntegrand x
              ((σ : Complex) + (v : Complex) * I)) -
          I * (∫ v : Real in (-T)..T,
            taoPerronFullIntegrand x
              ((β : Complex) + (v : Complex) * I)) =
          (x : Complex) * (Real.pi : Complex) * I := by
  obtain ⟨c, hc, hzero⟩ := exists_taoZeta_zero_free_closed_rectangles
  refine ⟨c, hc, ?_⟩
  intro H β σ T x hH hT hTH hβ0 hβ hσ hx hstrip
  apply taoPerronFullIntegrand_rectangle_boundary hβ0 hβ hσ hT hx
  intro s hs
  exact Or.inr (hzero H β σ T hH hT.le hTH hstrip (hβ.le.trans hσ.le) s hs)

end

end Erdos1212Kernel
