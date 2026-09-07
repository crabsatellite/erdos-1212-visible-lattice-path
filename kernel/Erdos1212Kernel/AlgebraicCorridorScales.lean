import Erdos1212Kernel.AlgebraicCorridorMonomials
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

/-! The exact parameters displayed in the paper. Every analytic use below
has an explicit large-positive-domain guard or is eventually at +infinity. -/

def ell (N : ℝ) : ℝ := Real.log N
def L (N : ℝ) : ℝ := Real.log (ell N)
def u (N : ℝ) : ℝ := 1000 * L N
def z (N : ℝ) : ℝ := N ^ (1 / u N)
def degree (N : ℝ) : ℕ := Nat.ceil (4 * u N)
def rows (N : ℝ) : ℕ := corridorInterpolationRowCount (degree N)
def band (N : ℝ) : ℕ := Nat.ceil (10000 * ell N ^ 2)
def supportGap (N : ℝ) : ℕ := Nat.ceil (ell N ^ 11)
def radius (N : ℝ) : ℕ := 2 * supportGap N + band N
def height (N : ℝ) : ℕ := Nat.ceil (Real.exp (L N ^ 6))
def rho (N : ℝ) : ℝ := Real.exp (-ell N / (20000 * L N))
def coefficientBound (N : ℝ) : ℝ :=
  ((rows N).factorial : ℝ) * (radius N : ℝ) ^ (degree N * rows N)
def valueBound (N : ℝ) : ℝ :=
  ((rows N : ℝ) + 1) * coefficientBound N * (4 * N) ^ degree N

theorem ell_tendsto : Tendsto ell atTop atTop := Real.tendsto_log_atTop
theorem L_tendsto : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp ell_tendsto

theorem eventually_large_domain : ∀ᶠ N : ℝ in atTop, 1 < N ∧ 1 ≤ ell N ∧ 1 ≤ L N := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), ell_tendsto.eventually_ge_atTop 1,
    L_tendsto.eventually_ge_atTop 1] with N hN hell hL
  exact ⟨hN, hell, hL⟩

theorem exp_ell {N : ℝ} (hN : 0 < N) : Real.exp (ell N) = N := Real.exp_log hN
theorem exp_L {N : ℝ} (hell : 0 < ell N) : Real.exp (L N) = ell N := Real.exp_log hell

theorem z_pos {N : ℝ} (hN : 0 < N) (_hu : 0 < u N) : 0 < z N := Real.rpow_pos_of_pos hN _

theorem log_z {N : ℝ} (hN : 0 < N) (_hu : 0 < u N) : Real.log (z N) = ell N / u N := by
  rw [z, Real.log_rpow hN]
  simp only [ell, div_eq_mul_inv, one_mul, mul_comm]

theorem degree_lower (N : ℝ) : 4 * u N ≤ (degree N : ℝ) := Nat.le_ceil _

theorem degree_upper {N : ℝ} (hu : 0 ≤ u N) : (degree N : ℝ) ≤ 4 * u N + 1 :=
  (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu)).le

theorem degree_bounds {N : ℝ} (hL : 1 ≤ L N) :
    1 ≤ degree N ∧ (degree N : ℝ) ≤ 5000 * L N := by
  have hu : 0 < u N := by unfold u; linarith
  have hpos : 1 ≤ degree N := Nat.one_le_ceil_iff.mpr (mul_pos (by norm_num) hu)
  have hupper := degree_upper hu.le
  unfold u at hupper
  exact ⟨hpos, by linarith⟩

theorem rows_identity (N : ℝ) :
    2 * (rows N : ℝ) = (degree N : ℝ) ^ 2 + 3 * (degree N : ℝ) := by
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (corridorInterpolationRowCount_succ (degree N))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_choose_two, Nat.cast_ofNat] at hc
  unfold rows
  nlinarith

theorem rows_bounds {N : ℝ} (hL : 1 ≤ L N) :
    1 ≤ rows N ∧ (rows N : ℝ) ≤ 20000000 * L N ^ 2 := by
  obtain ⟨hd, hdUpper⟩ := degree_bounds hL
  have hdReal : (1 : ℝ) ≤ degree N := by exact_mod_cast hd
  have hidentity := rows_identity N
  have hdsq := pow_le_pow_left₀ (Nat.cast_nonneg (degree N)) hdUpper 2
  have hLsq : L N ≤ L N ^ 2 := by nlinarith
  have hrReal : (1 : ℝ) ≤ rows N := by nlinarith [sq_nonneg ((degree N : ℝ) - 1)]
  refine ⟨by exact_mod_cast hrReal, ?_⟩
  nlinarith

/-- The exact integer rounding leaves a full degree-sized margin in the divisor exponent. -/
theorem rows_div_u_ge_twice_degree {N : ℝ} (hu : 0 < u N) :
    2 * (degree N : ℝ) ≤ (rows N : ℝ) / u N := by
  apply (le_div_iff₀ hu).mpr
  have hid := rows_identity N
  have hlow := degree_lower N
  have hd0 : (0 : ℝ) ≤ degree N := Nat.cast_nonneg _
  have hprod := mul_nonneg hd0 (sub_nonneg.mpr hlow)
  nlinarith

/-- Any fixed power of log log N is negligible compared with log N. -/
theorem eventually_C_mul_L_pow_lt_ell (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℝ in atTop, C * L N ^ k < ell N := by
  have ht := (Real.tendsto_exp_div_pow_atTop k).comp L_tendsto
  filter_upwards [ht.eventually_gt_atTop C, eventually_large_domain] with N h hdom
  change C < Real.exp (L N) / L N ^ k at h
  rw [exp_L (zero_lt_one.trans_le hdom.2.1)] at h
  exact (lt_div_iff₀ (pow_pos (zero_lt_one.trans_le hdom.2.2) k)).mp h

/-- Any fixed power of `log N` is negligible compared with `N`. -/
theorem eventually_C_mul_ell_pow_lt_N (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℝ in atTop, C * ell N ^ k < N := by
  have ht := (Real.tendsto_exp_div_pow_atTop k).comp ell_tendsto
  filter_upwards [ht.eventually_gt_atTop C, eventually_large_domain] with N h hdom
  change C < Real.exp (ell N) / ell N ^ k at h
  rw [exp_ell (zero_lt_one.trans hdom.1)] at h
  exact (lt_div_iff₀ (pow_pos (zero_lt_one.trans_le hdom.2.1) k)).mp h

end

end Erdos1212Kernel.CorridorScale
