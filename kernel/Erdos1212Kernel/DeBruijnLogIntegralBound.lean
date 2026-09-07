import Erdos1212Kernel.DeBruijnLogPrimitiveBounds
import Erdos1212Kernel.DeBruijnLogErrorScaleLimit
import Erdos1212Kernel.DeBruijnSaddleIntegralTransport

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnSaddle_log_integral_bound {A u : Real} (hA : 1 < A) (hu : A ≤ u)
    (hbound : ∀ x ≥ A, |deBruijnSaddle x - deBruijnRhoLogMainDerivative x| ≤ 22 * deBruijnRhoLogErrorDerivative x) :
    |(∫ x in (1 : Real)..u, deBruijnSaddle x) - deBruijnRhoLogMain u| ≤
      22 * deBruijnRhoLogErrorScale u + |(∫ x in (1 : Real)..A, deBruijnSaddle x) - deBruijnRhoLogMain A| +
        22 * |deBruijnRhoLogErrorScale A| := by
  have hset : Set.uIcc A u ⊆ Set.Ioi (1 : Real) := by
    rw [Set.uIcc_of_le hu]
    intro x hx
    exact hA.trans_le hx.1
  have hiD : IntervalIntegrable deBruijnRhoLogMainDerivative volume A u :=
    (deBruijnRhoLogMainDerivative_continuousOn.mono hset).intervalIntegrable
  have hiE : IntervalIntegrable deBruijnRhoLogErrorDerivative volume A u :=
    (deBruijnRhoLogErrorDerivative_continuousOn.mono hset).intervalIntegrable
  have hD := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => deBruijnRhoLogMain_hasDerivAt (hset hx)) hiD
  have hE := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => deBruijnRhoLogErrorScale_hasDerivAt (hset hx)) hiE
  have hn := intervalIntegral.norm_integral_le_of_norm_le (f := fun x => deBruijnSaddle x - deBruijnRhoLogMainDerivative x)
    (g := fun x => 22 * deBruijnRhoLogErrorDerivative x) hu (by
      filter_upwards with x hx
      simpa only [Real.norm_eq_abs] using hbound x hx.1.le) (hiE.const_mul 22)
  rw [intervalIntegral.integral_sub (deBruijnSaddle_intervalIntegrable A u) hiD,
    intervalIntegral.integral_const_mul, hD, hE, Real.norm_eq_abs] at hn
  have hsum := intervalIntegral.integral_add_adjacent_intervals (deBruijnSaddle_intervalIntegrable 1 A)
    (deBruijnSaddle_intervalIntegrable A u)
  have hid : (∫ x in (1 : Real)..u, deBruijnSaddle x) - deBruijnRhoLogMain u =
      ((∫ x in (1 : Real)..A, deBruijnSaddle x) - deBruijnRhoLogMain A) +
      ((∫ x in A..u, deBruijnSaddle x) - (deBruijnRhoLogMain u - deBruijnRhoLogMain A)) := by
    rw [← hsum]
    ring
  rw [hid]
  have ht := abs_add_le ((∫ x in (1 : Real)..A, deBruijnSaddle x) - deBruijnRhoLogMain A)
    ((∫ x in A..u, deBruijnSaddle x) - (deBruijnRhoLogMain u - deBruijnRhoLogMain A))
  linarith [neg_le_abs (deBruijnRhoLogErrorScale A)]

theorem deBruijnSaddle_integral_log_expansion :
    Asymptotics.IsBigO atTop (fun u : Real => (∫ x in (1 : Real)..u, deBruijnSaddle x) - deBruijnRhoLogMain u)
      deBruijnRhoLogErrorScale := by
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp eventually_deBruijnSaddle_primitive_error_bound
  let A := max A₀ 2
  have hA : 1 < A := by dsimp [A]; linarith [le_max_right A₀ (2 : Real)]
  have hbound : ∀ x ≥ A, |deBruijnSaddle x - deBruijnRhoLogMainDerivative x| ≤ 22 * deBruijnRhoLogErrorDerivative x := by
    intro x hx
    exact hA₀ x ((le_max_left A₀ 2).trans hx)
  let D := |(∫ x in (1 : Real)..A, deBruijnSaddle x) - deBruijnRhoLogMain A| + 22 * |deBruijnRhoLogErrorScale A|
  apply Asymptotics.IsBigO.of_bound 23
  filter_upwards [eventually_ge_atTop A, tendsto_deBruijnRhoLogErrorScale.eventually_ge_atTop D,
    tendsto_deBruijnRhoLogErrorScale.eventually_ge_atTop 0] with u hu hD hpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  have h := deBruijnSaddle_log_integral_bound hA hu hbound
  dsimp [D] at hD
  linarith

theorem deBruijn1951SaddleIntegral_log_expansion :
    Asymptotics.IsBigO atTop (fun u : Real => deBruijn1951SaddleIntegral (deBruijnSaddle u) - deBruijnRhoLogMain u)
      deBruijnRhoLogErrorScale := by
  apply deBruijnSaddle_integral_log_expansion.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  rw [deBruijn1951SaddleIntegral_eq_inverse_integral hu]

end

end Erdos1212Kernel
