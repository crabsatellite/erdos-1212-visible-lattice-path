import Erdos1212Kernel.AlgebraicCorridorPathSeparation

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

def squareHalfSide (N : ℝ) : ℕ := ⌊N * rho N / 100⌋₊
def squareStep (N : ℝ) : ℕ := squareHalfSide N / 10

theorem eventually_corridor_width_ge_exp :
    ∀ᶠ N : ℝ in atTop, Real.exp (19 * ell N / 20) ≤ N * rho N := by
  filter_upwards [eventually_large_domain] with N hdom
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hL : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hell : 0 ≤ ell N := zero_le_one.trans hdom.2.1
  have hsmall : ell N / (20000 * L N) ≤ ell N / 20 := by
    apply div_le_div_of_nonneg_left hell (by norm_num)
    linarith [hdom.2.2]
  change Real.exp (19 * ell N / 20) ≤ N * Real.exp (-ell N / (20000 * L N))
  conv_rhs => lhs; rw [← exp_ell hN]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

theorem eventually_C_mul_nineTenths_lt_width (C : ℝ) :
    ∀ᶠ N : ℝ in atTop, C * N ^ (9 / 10 : ℝ) < N * rho N := by
  have ht : Tendsto (fun N : ℝ => Real.exp (ell N / 20)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    simpa [div_eq_mul_inv, mul_comm] using
      ell_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  filter_upwards [eventually_large_domain, eventually_corridor_width_ge_exp,
    ht.eventually_gt_atTop C] with N hdom hwidth hC
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hpow : 0 < N ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hN _
  calc
    C * N ^ (9 / 10 : ℝ) < Real.exp (ell N / 20) * N ^ (9 / 10 : ℝ) :=
      mul_lt_mul_of_pos_right hC hpow
    _ = Real.exp (19 * ell N / 20) := by
      rw [Real.rpow_def_of_pos hN, ← Real.exp_add]
      congr 1
      unfold ell
      ring
    _ ≤ N * rho N := hwidth

theorem eventually_C_mul_nineTenths_lt_squareHalfSide (C : ℝ) :
    ∀ᶠ N : ℝ in atTop, C * N ^ (9 / 10 : ℝ) < (squareHalfSide N : ℝ) := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_nineTenths_lt_width (100 * (C + 1))]
    with N hdom hw
  have hpow : (1 : ℝ) ≤ N ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hdom.1.le (by norm_num)
  have hfloor := Nat.lt_floor_add_one (N * rho N / 100)
  change N * rho N / 100 < (squareHalfSide N : ℝ) + 1 at hfloor
  nlinarith

theorem squareHalfSide_div_nineTenths_tendsto :
    Tendsto (fun N : ℝ => (squareHalfSide N : ℝ) / N ^ (9 / 10 : ℝ))
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  filter_upwards [eventually_large_domain,
    eventually_C_mul_nineTenths_lt_squareHalfSide C] with N hdom h
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hdom.1) _)).mpr
  exact h.le

theorem eventually_squareHalfSide_bounds :
    ∀ᶠ N : ℝ in atTop,
      10 ≤ squareHalfSide N ∧ (squareHalfSide N : ℝ) ≤ N / 100 ∧
      0 < squareStep N := by
  have hrho := rho_tendsto_zero.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_large_domain, hrho,
    eventually_C_mul_nineTenths_lt_squareHalfSide 10] with N hdom hrho hlarge
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hpow : (1 : ℝ) ≤ N ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hdom.1.le (by norm_num)
  have hten : 10 ≤ squareHalfSide N := by
    have hreal : (10 : ℝ) ≤ squareHalfSide N := by nlinarith
    exact_mod_cast hreal
  have hrpos : 0 < rho N := Real.exp_pos _
  have hfloor : (squareHalfSide N : ℝ) ≤ N * rho N / 100 :=
    Nat.floor_le (by positivity)
  refine ⟨hten, ?_, Nat.div_pos hten (by norm_num)⟩
  have hmul := mul_le_mul_of_nonneg_left hrho.le hN.le
  nlinarith

theorem dyadic_squareHalfSide_div_nineTenths_tendsto :
    Tendsto (fun j : ℕ => (squareHalfSide (dyadicScale j) : ℝ) /
      (dyadicScale j) ^ (9 / 10 : ℝ)) atTop atTop :=
  squareHalfSide_div_nineTenths_tendsto.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

end
end Erdos1212Kernel.CorridorScale
