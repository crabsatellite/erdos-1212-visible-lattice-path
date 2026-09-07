import Erdos1212Kernel.IwaniecPaperQFarFactorial

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniecQFar_rounding_margin :
    ∀ᶠ xi : Real in atTop, 15 ≤ xi ∧
      3 * Real.log xi + Real.log 2 < xi * Real.log (4 / 3 : Real) := by
  let c := Real.log (4 / 3 : Real)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (max 15 (2 * Real.log 2 / c)),
    hlim.eventually (Iio_mem_nhds (show (0 : Real) < c / 6 by positivity))] with xi hxi hlog
  have hxi15 : 15 ≤ xi := (le_max_left _ _).trans hxi
  have hxi0 : 0 < xi := by linarith
  have hconst : 2 * Real.log 2 ≤ xi * c :=
    (div_le_iff₀ hc).mp ((le_max_right _ _).trans hxi)
  have hscaled := (div_lt_iff₀ hxi0).mp (show Real.log xi / xi < c / 6 from hlog)
  refine ⟨hxi15, ?_⟩
  change 3 * Real.log xi + Real.log 2 < xi * c
  nlinarith only [hconst, hscaled]

/-- The source's literal constant-5 power bound, with the first
integer degree K and all of its rounding cost explicitly accounted for. -/
theorem iwaniecQFar_rounded_power_lt {xi T : Real} {K : Nat}
    (hxi : 15 ≤ xi) (hmargin : 3 * Real.log xi + Real.log 2 < xi * Real.log (4 / 3 : Real))
    (hT : 1 ≤ T) (hsmall : 5 * T < xi) (hK : xi - 3 ≤ (K : Real)) :
    2 * (3 * T / (K : Real)) ^ K < (5 * T / xi) ^ xi := by
  have hxi0 : 0 < xi := by linarith
  have hT0 : 0 < T := by linarith
  have hK0 : (0 : Real) < K := by linarith
  have hKfour : (4 / 5 : Real) * xi ≤ (K : Real) := by linarith
  let A := 5 * T / xi
  let B := (15 / 4 : Real) * T / xi
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hbase0 : 0 < 3 * T / (K : Real) := by positivity
  have hbase : 3 * T / (K : Real) ≤ B := by
    apply (div_le_div_iff₀ hK0 hxi0).mpr
    have hh := mul_le_mul_of_nonneg_left hKfour (show 0 ≤ (15 / 4 : Real) * T by positivity)
    nlinarith only [hh]
  have hB1 : B < 1 := (div_lt_one₀ hxi0).mpr (by nlinarith only [hsmall, hT0])
  have hlogB0 : Real.log B ≤ 0 := Real.log_nonpos hB0.le hB1.le
  have hNum : 1 ≤ (15 / 4 : Real) * T := by linarith
  have hlogB : Real.log B = Real.log ((15 / 4 : Real) * T) - Real.log xi :=
    Real.log_div (by positivity) hxi0.ne'
  have hlogBlo : -Real.log xi ≤ Real.log B := by
    rw [hlogB]
    have hh := Real.log_nonneg hNum
    linarith
  have hAB : A = B * (4 / 3 : Real) := by dsimp [A, B]; ring
  have hlogA : Real.log A = Real.log B + Real.log (4 / 3 : Real) := by
    rw [hAB, Real.log_mul hB0.ne' (by norm_num)]
  have hlogFinal : Real.log 2 + (xi - 3) * Real.log B < xi * Real.log A := by
    rw [hlogA]
    nlinarith only [hmargin, hlogBlo]
  calc
    2 * (3 * T / (K : Real)) ^ K = Real.exp (Real.log 2 + (K : Real) * Real.log (3 * T / (K : Real))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : Real) < 2), Real.exp_nat_mul, Real.exp_log hbase0]
    _ ≤ Real.exp (Real.log 2 + (K : Real) * Real.log B) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.log_le_log hbase0 hbase) hK0.le)
    _ ≤ Real.exp (Real.log 2 + (xi - 3) * Real.log B) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonpos_right hK hlogB0)
    _ < Real.exp (xi * Real.log A) := Real.exp_lt_exp.mpr hlogFinal
    _ = (5 * T / xi) ^ xi := by
      change Real.exp (xi * Real.log A) = A ^ xi
      rw [Real.rpow_def_of_pos hA0]
      congr 1
      ring

end

end Erdos1212Kernel
