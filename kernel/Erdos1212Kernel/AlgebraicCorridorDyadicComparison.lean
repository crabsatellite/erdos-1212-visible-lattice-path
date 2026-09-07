import Erdos1212Kernel.AlgebraicCorridorSquareScale
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter Set

/-- The exact function differentiated in the paper's scale comparison. -/
def corridorLogPenalty (t : ℝ) : ℝ := t / (20000 * Real.log t)

theorem corridorLogPenalty_hasDerivAt {t : ℝ} (ht : 0 < t)
    (hlog : 0 < Real.log t) :
    HasDerivAt corridorLogPenalty
      ((Real.log t - 1) / (20000 * (Real.log t) ^ 2)) t := by
  have h := (hasDerivAt_id t).div ((Real.hasDerivAt_log ht.ne').const_mul 20000)
    (show 20000 * Real.log t ≠ 0 by positivity)
  convert h using 1
  simp only [id_eq]
  field_simp

theorem corridorLogPenalty_derivative_bounds {t : ℝ} (hlog : 2 ≤ Real.log t) :
    0 < (Real.log t - 1) / (20000 * (Real.log t) ^ 2) ∧
      (Real.log t - 1) / (20000 * (Real.log t) ^ 2) < 1 / 2 := by
  have hden : 0 < 20000 * (Real.log t) ^ 2 := by positivity
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_nonneg (Real.log t - 1)]

theorem corridorLogPenalty_increment {a b : ℝ}
    (ha : Real.exp 2 ≤ a) (hab : a < b) :
    0 < corridorLogPenalty b - corridorLogPenalty a ∧
      corridorLogPenalty b - corridorLogPenalty a < (b - a) / 2 := by
  have hpoint (x : ℝ) (hx : a ≤ x) : 0 < x ∧ 2 ≤ Real.log x := by
    have hp : 0 < x := (Real.exp_pos 2).trans_le (ha.trans hx)
    refine ⟨hp, ?_⟩
    have h := Real.log_le_log (Real.exp_pos 2) (ha.trans hx)
    simpa using h
  have hderiv (x : ℝ) (hx : a ≤ x) :=
    corridorLogPenalty_hasDerivAt (hpoint x hx).1 (by linarith [(hpoint x hx).2])
  have hcont : ContinuousOn corridorLogPenalty (Icc a b) :=
    fun x hx => (hderiv x hx.1).continuousAt.continuousWithinAt
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope corridorLogPenalty
    (fun t => (Real.log t - 1) / (20000 * (Real.log t) ^ 2)) hab hcont
    (fun x hx => hderiv x hx.1.le)
  have hbds := corridorLogPenalty_derivative_bounds (hpoint c hc.1.le).2
  rw [heq] at hbds
  have hd : 0 < b - a := sub_pos.mpr hab
  exact ⟨by have h := (lt_div_iff₀ hd).mp hbds.1; linarith,
    by have h := (div_lt_iff₀ hd).mp hbds.2; linarith⟩

theorem corridor_width_eq_exp {N : ℝ} (hN : 0 < N) :
    N * rho N = Real.exp (ell N - corridorLogPenalty (ell N)) := by
  rw [Real.exp_sub, exp_ell hN]
  simp only [rho, corridorLogPenalty, L, Real.exp_neg, div_eq_mul_inv, neg_mul]

theorem eventually_dyadic_corridor_width_ratio :
    ∀ᶠ N : ℝ in atTop,
      Real.sqrt 2 < (2 * N * rho (2 * N)) / (N * rho N) ∧
      (2 * N * rho (2 * N)) / (N * rho N) < 2 := by
  filter_upwards [eventually_large_domain,
    ell_tendsto.eventually_ge_atTop (Real.exp 2)] with N hdom hell
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hell2 : ell (2 * N) = Real.log 2 + ell N := by
    exact Real.log_mul (by norm_num) hN.ne'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinc := corridorLogPenalty_increment hell (show ell N < ell (2 * N) by
    rw [hell2]; linarith)
  rw [corridor_width_eq_exp (by positivity : 0 < 2 * N),
    corridor_width_eq_exp hN, ← Real.exp_sub]
  constructor
  · rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_exp.mpr
    rw [hell2] at hinc ⊢
    linarith
  · conv_rhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_exp.mpr
    rw [hell2] at hinc ⊢
    linarith

theorem eventually_dyadic_squareHalfSide_comparison :
    ∀ᶠ N : ℝ in atTop,
      squareHalfSide N ≤ squareHalfSide (2 * N) ∧
      squareHalfSide (2 * N) ≤ 3 * squareHalfSide N := by
  filter_upwards [eventually_dyadic_corridor_width_ratio,
    eventually_squareHalfSide_bounds, eventually_large_domain] with N hratio hside hdom
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hw : 0 < N * rho N := mul_pos hN (Real.exp_pos _)
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hlo := (lt_div_iff₀ hw).mp (hsqrt.trans hratio.1)
  have hhi := (div_lt_iff₀ hw).mp hratio.2
  constructor
  · apply Nat.floor_mono
    linarith
  · have hf : (squareHalfSide (2 * N) : ℝ) ≤ 2 * N * rho (2 * N) / 100 :=
      Nat.floor_le (by have hr : 0 < rho (2 * N) := Real.exp_pos _; positivity)
    have hf' : N * rho N / 100 < (squareHalfSide N : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hh : (10 : ℝ) ≤ squareHalfSide N := by exact_mod_cast hside.1
    have hr : (squareHalfSide (2 * N) : ℝ) ≤ 3 * (squareHalfSide N : ℝ) :=
      by nlinarith
    exact_mod_cast hr

theorem eventually_dyadic_bridge_width :
    ∀ᶠ N : ℝ in atTop,
      (2 * N) ^ (9 / 10 : ℝ) < 2 * (squareHalfSide N : ℝ) + 1 := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_nineTenths_lt_squareHalfSide 2] with N hdom hsize
  have hN : 0 ≤ N := (zero_lt_one.trans hdom.1).le
  have htwo : (2 : ℝ) ^ (9 / 10 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (9 / 10 : ℝ) ≤ 1)
    simpa using h
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN]
  have h := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN (9 / 10 : ℝ))
  have hh : (0 : ℝ) ≤ squareHalfSide N := by positivity
  linarith

end
end Erdos1212Kernel.CorridorScale
