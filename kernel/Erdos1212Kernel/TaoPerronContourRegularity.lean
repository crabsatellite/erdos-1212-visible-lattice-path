import Erdos1212Kernel.TaoZetaPoleRemovedGlobal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.DSlope

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 1900000

def taoPerronAnalyticFactor (x : Real) (s : Complex) : Complex :=
  (x : Complex) ^ s * taoRieszMellinKernel s

def taoPerronRegularPart (x : Real) (s : Complex) : Complex :=
  -logDeriv taoZetaPoleRemoved s * taoPerronAnalyticFactor x s

def taoPerronFactorDslope (x : Real) (s : Complex) : Complex :=
  dslope (taoPerronAnalyticFactor x) 1 s

def taoPerronHolomorphicRemainder (x : Real) (s : Complex) : Complex :=
  taoPerronFactorDslope x s + taoPerronRegularPart x s

theorem taoPerronAnalyticFactor_one (x : Real) :
    taoPerronAnalyticFactor x 1 = (x : Complex) / 2 := by
  unfold taoPerronAnalyticFactor taoRieszMellinKernel
  norm_num
  ring

theorem differentiableAt_taoPerronAnalyticFactor
    {x : Real} (hx : 0 < x) {s : Complex}
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt Complex (taoPerronAnalyticFactor x) s := by
  have hxC : (x : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : DifferentiableAt Complex (fun z : Complex => (x : Complex) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hxC)
  have hden : DifferentiableAt Complex (fun z : Complex => z * (z + 1)) s := by
    fun_prop
  have hkernel : DifferentiableAt Complex taoRieszMellinKernel s := by
    unfold taoRieszMellinKernel
    have hconst : DifferentiableAt Complex (fun _ : Complex => (1 : Complex)) s := by
      fun_prop
    exact hconst.div hden (mul_ne_zero hs0 hs1)
  exact hpow.mul hkernel

theorem differentiableAt_taoPerronRegularPart
    {x : Real} (hx : 0 < x) {s : Complex}
    (hH : taoZetaPoleRemoved s ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt Complex (taoPerronRegularPart x) s := by
  unfold taoPerronRegularPart
  exact (analyticAt_logDeriv_taoZetaPoleRemoved hH).differentiableAt.neg.mul
    (differentiableAt_taoPerronAnalyticFactor hx hs0 hs1)

theorem continuousAt_taoPerronFactorDslope
    {x : Real} (hx : 0 < x) {s : Complex}
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    ContinuousAt (taoPerronFactorDslope x) s := by
  unfold taoPerronFactorDslope
  by_cases hs : s = 1
  · subst s
    exact continuousAt_dslope_same.mpr
      (differentiableAt_taoPerronAnalyticFactor hx one_ne_zero (by norm_num))
  · exact (continuousAt_dslope_of_ne hs).mpr
      (differentiableAt_taoPerronAnalyticFactor hx hs0 hs1).continuousAt

theorem differentiableAt_taoPerronFactorDslope_of_ne_one
    {x : Real} (hx : 0 < x) {s : Complex}
    (hs : s ≠ 1) (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt Complex (taoPerronFactorDslope x) s := by
  unfold taoPerronFactorDslope
  exact (differentiableAt_dslope_of_ne hs).mpr
    (differentiableAt_taoPerronAnalyticFactor hx hs0 hs1)

theorem continuousAt_taoPerronHolomorphicRemainder
    {x : Real} (hx : 0 < x) {s : Complex}
    (hH : taoZetaPoleRemoved s ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    ContinuousAt (taoPerronHolomorphicRemainder x) s := by
  unfold taoPerronHolomorphicRemainder
  exact (continuousAt_taoPerronFactorDslope hx hs0 hs1).add
    (differentiableAt_taoPerronRegularPart hx hH hs0 hs1).continuousAt

theorem differentiableAt_taoPerronHolomorphicRemainder_of_ne_one
    {x : Real} (hx : 0 < x) {s : Complex}
    (hs : s ≠ 1) (hH : taoZetaPoleRemoved s ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt Complex (taoPerronHolomorphicRemainder x) s := by
  unfold taoPerronHolomorphicRemainder
  exact (differentiableAt_taoPerronFactorDslope_of_ne_one hx hs hs0 hs1).add
    (differentiableAt_taoPerronRegularPart hx hH hs0 hs1)

theorem taoPerron_logDerivative_decomposition
    {x : Real} {s : Complex} (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    taoZetaLogDerivative s * taoPerronAnalyticFactor x s =
      (1 / (s - 1)) * taoPerronAnalyticFactor x s +
        taoPerronRegularPart x s := by
  rw [taoZetaLogDerivative_eq_inv_sub_logDeriv_poleRemoved_of_ne_zero hs1 hzeta]
  unfold taoPerronRegularPart
  ring

theorem taoPerron_pole_factor_decomposition
    {x : Real} {s : Complex} (hs : s ≠ 1) :
    (1 / (s - 1)) * taoPerronAnalyticFactor x s =
      ((x : Complex) / 2) / (s - 1) + taoPerronFactorDslope x s := by
  have hds := sub_smul_dslope (taoPerronAnalyticFactor x) 1 s
  change (s - 1) * dslope (taoPerronAnalyticFactor x) 1 s =
    taoPerronAnalyticFactor x s - taoPerronAnalyticFactor x 1 at hds
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [taoPerronAnalyticFactor_one] at hds
  unfold taoPerronFactorDslope
  have hfactor : taoPerronAnalyticFactor x s =
      (x : Complex) / 2 + (s - 1) * dslope (taoPerronAnalyticFactor x) 1 s := by
    calc
      taoPerronAnalyticFactor x s = (x : Complex) / 2 +
          (taoPerronAnalyticFactor x s - (x : Complex) / 2) := by ring
      _ = (x : Complex) / 2 +
          (s - 1) * dslope (taoPerronAnalyticFactor x) 1 s := by rw [hds]
  rw [one_div, hfactor]
  field_simp [hden]

theorem taoPerron_full_integrand_decomposition
    {x : Real} {s : Complex} (hs : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    taoZetaLogDerivative s * taoPerronAnalyticFactor x s =
      ((x : Complex) / 2) / (s - 1) +
        taoPerronHolomorphicRemainder x s := by
  rw [taoPerron_logDerivative_decomposition hs hzeta,
    taoPerron_pole_factor_decomposition hs]
  unfold taoPerronHolomorphicRemainder
  ring

theorem differentiableOn_taoPerronRegularPart_rectangle
    {β σ T x : Real} (hβ : 0 < β) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    DifferentiableOn Complex (taoPerronRegularPart x)
      (Set.Icc β σ ×ℂ Set.Icc (-T) T) := by
  intro s hs
  have hrect := hs
  rw [Complex.mem_reProdIm] at hrect
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hrect
    linarith
  have hsplus : s + 1 ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith [hrect.1.1]
  have hH : taoZetaPoleRemoved s ≠ 0 :=
    taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero (hzero s hs)
  exact (differentiableAt_taoPerronRegularPart hx hH hs0 hsplus).differentiableWithinAt

theorem taoPerronRegularPart_rectangle_boundary_eq_zero
    {β σ T x : Real} (hβ : 0 < β) (hβσ : β ≤ σ)
    (hT : 0 ≤ T) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    (∫ u : Real in β..σ,
        taoPerronRegularPart x ((u : Complex) + ((-T : Real) : Complex) * I)) -
      (∫ u : Real in β..σ,
        taoPerronRegularPart x ((u : Complex) + (T : Complex) * I)) +
      I * (∫ v : Real in (-T)..T,
        taoPerronRegularPart x ((σ : Complex) + (v : Complex) * I)) -
      I * (∫ v : Real in (-T)..T,
        taoPerronRegularPart x ((β : Complex) + (v : Complex) * I)) = 0 := by
  let z : Complex := (β : Complex) + ((-T : Real) : Complex) * I
  let w : Complex := (σ : Complex) + (T : Complex) * I
  have hzre : z.re = β := by simp [z]
  have hwre : w.re = σ := by simp [w]
  have hzim : z.im = -T := by simp [z]
  have hwim : w.im = T := by simp [w]
  have hdiff : DifferentiableOn Complex (taoPerronRegularPart x)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    rw [hzre, hwre, hzim, hwim, Set.uIcc_of_le hβσ,
      Set.uIcc_of_le (neg_le_self hT)]
    exact differentiableOn_taoPerronRegularPart_rectangle hβ hx hzero
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (taoPerronRegularPart x) z w hdiff
  simpa only [hzre, hwre, hzim, hwim, Complex.real_smul] using hboundary

theorem continuousOn_taoPerronHolomorphicRemainder_rectangle
    {β σ T x : Real} (hβ : 0 < β) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    ContinuousOn (taoPerronHolomorphicRemainder x)
      (Set.Icc β σ ×ℂ Set.Icc (-T) T) := by
  intro s hs
  have hrect := hs
  rw [Complex.mem_reProdIm] at hrect
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hrect
    linarith
  have hsplus : s + 1 ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith [hrect.1.1]
  have hH : taoZetaPoleRemoved s ≠ 0 :=
    taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero (hzero s hs)
  exact (continuousAt_taoPerronHolomorphicRemainder hx hH hs0 hsplus).continuousWithinAt

theorem taoPerronHolomorphicRemainder_rectangle_boundary_eq_zero
    {β σ T x : Real} (hβ : 0 < β) (hβσ : β ≤ σ)
    (hT : 0 ≤ T) (hx : 0 < x)
    (hzero : ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
      s = 1 ∨ riemannZeta s ≠ 0) :
    (∫ u : Real in β..σ,
        taoPerronHolomorphicRemainder x
          ((u : Complex) + ((-T : Real) : Complex) * I)) -
      (∫ u : Real in β..σ,
        taoPerronHolomorphicRemainder x
          ((u : Complex) + (T : Complex) * I)) +
      I * (∫ v : Real in (-T)..T,
        taoPerronHolomorphicRemainder x
          ((σ : Complex) + (v : Complex) * I)) -
      I * (∫ v : Real in (-T)..T,
        taoPerronHolomorphicRemainder x
          ((β : Complex) + (v : Complex) * I)) = 0 := by
  let z : Complex := (β : Complex) + ((-T : Real) : Complex) * I
  let w : Complex := (σ : Complex) + (T : Complex) * I
  have hzre : z.re = β := by simp [z]
  have hwre : w.re = σ := by simp [w]
  have hzim : z.im = -T := by simp [z]
  have hwim : w.im = T := by simp [w]
  have hcont : ContinuousOn (taoPerronHolomorphicRemainder x)
      (Set.Icc β σ ×ℂ Set.Icc (-T) T) :=
    continuousOn_taoPerronHolomorphicRemainder_rectangle hβ hx hzero
  have hcont' : ContinuousOn (taoPerronHolomorphicRemainder x)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    rw [hzre, hwre, hzim, hwim, Set.uIcc_of_le hβσ,
      Set.uIcc_of_le (neg_le_self hT)]
    exact hcont
  have hdiff : ∀ s ∈ (Set.Ioo β σ ×ℂ Set.Ioo (-T) T) \ ({1} : Set Complex),
      DifferentiableAt Complex (taoPerronHolomorphicRemainder x) s := by
    intro s hs
    have hopen := hs.1
    rw [Complex.mem_reProdIm] at hopen
    have hclosed : s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      exact ⟨⟨hopen.1.1.le, hopen.1.2.le⟩,
        ⟨hopen.2.1.le, hopen.2.2.le⟩⟩
    have hsne : s ≠ 1 := by
      simpa only [Set.mem_singleton_iff] using hs.2
    have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      norm_num at hopen
      linarith
    have hsplus : s + 1 ≠ 0 := by
      intro hsplus
      have hre := congrArg Complex.re hsplus
      simp at hre
      linarith [hopen.1.1]
    have hH : taoZetaPoleRemoved s ≠ 0 :=
      taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero (hzero s hclosed)
    exact differentiableAt_taoPerronHolomorphicRemainder_of_ne_one
      hx hsne hH hs0 hsplus
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      (taoPerronHolomorphicRemainder x) z w ({1} : Set Complex)
      (Set.countable_singleton 1) hcont' (by
        simpa only [hzre, hwre, hzim, hwim, min_eq_left hβσ,
          max_eq_right hβσ, min_eq_left (neg_le_self hT),
          max_eq_right (neg_le_self hT)] using hdiff)
  simpa only [hzre, hwre, hzim, hwim, Complex.real_smul] using hboundary

theorem exists_taoZeta_zero_free_closed_rectangles :
    ∃ c : Real, 0 < c ∧
      ∀ H β σ T : Real,
        0 ≤ H → 0 ≤ T → T ≤ H →
        1 - c / Real.log (3 + H) < β →
        β ≤ σ →
        ∀ s ∈ Set.Icc β σ ×ℂ Set.Icc (-T) T,
          riemannZeta s ≠ 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_riemannZeta_zero_free_rectangles
  refine ⟨c, hc, ?_⟩
  intro H β σ T hH hT hTH hβ hβσ s hs
  have hrect := hs
  rw [Complex.mem_reProdIm] at hrect
  have himT : |s.im| ≤ T := abs_le.mpr hrect.2
  have himH : |s.im| ≤ H := himT.trans hTH
  have hre : 1 - c / Real.log (3 + H) < s.re := hβ.trans_le hrect.1.1
  have hz := hzero H s.im s.re hH himH hre
  simpa only [Complex.re_add_im] using hz

theorem exists_taoPerronRegularPart_zero_free_rectangle_boundary :
    ∃ c : Real, 0 < c ∧
      ∀ H β σ T x : Real,
        0 ≤ H → 0 ≤ T → T ≤ H →
        0 < β → β ≤ σ → 0 < x →
        1 - c / Real.log (3 + H) < β →
        (∫ u : Real in β..σ,
            taoPerronRegularPart x ((u : Complex) + ((-T : Real) : Complex) * I)) -
          (∫ u : Real in β..σ,
            taoPerronRegularPart x ((u : Complex) + (T : Complex) * I)) +
          I * (∫ v : Real in (-T)..T,
            taoPerronRegularPart x ((σ : Complex) + (v : Complex) * I)) -
          I * (∫ v : Real in (-T)..T,
            taoPerronRegularPart x ((β : Complex) + (v : Complex) * I)) = 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_taoZeta_zero_free_closed_rectangles
  refine ⟨c, hc, ?_⟩
  intro H β σ T x hH hT hTH hβ hβσ hx hstrip
  apply taoPerronRegularPart_rectangle_boundary_eq_zero hβ hβσ hT hx
  intro s hs
  exact Or.inr (hzero H β σ T hH hT hTH hstrip hβσ s hs)

end

end Erdos1212Kernel
