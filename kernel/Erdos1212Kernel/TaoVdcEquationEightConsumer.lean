import Erdos1212Kernel.TaoVdcEquationEight

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoVdcRate_le_log_bareMax (j : Nat) {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    taoVdcRate j N T ≤ 4 * Real.log (2 + T) * taoVdcBareMax j N T := by
  have hmax1 : taoVdcBareFirst j N T ≤ taoVdcBareMax j N T := le_max_left _ _
  have hmax2 : taoVdcSecond j N T ≤ taoVdcBareMax j N T := le_max_right _ _
  have hlog : 0 ≤ Real.log (2 + T) ^ (taoVdcAlpha j) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hmax0 : 0 ≤ taoVdcBareMax j N T := by
    have hS : 0 ≤ taoVdcSecond j N T := by
      unfold taoVdcSecond
      positivity
    exact hS.trans hmax2
  have hfirst : taoVdcFirst j N T ≤ taoVdcBareMax j N T *
      Real.log (2 + T) ^ (taoVdcAlpha j) := by
    unfold taoVdcFirst taoVdcBareFirst at *
    exact mul_le_mul_of_nonneg_right hmax1 hlog
  rw [taoVdcRate_split]
  calc
    _ ≤ taoVdcBareMax j N T * Real.log (2 + T) ^ (taoVdcAlpha j) +
        taoVdcBareMax j N T := add_le_add hfirst hmax2
    _ = taoVdcBareMax j N T *
        (Real.log (2 + T) ^ (taoVdcAlpha j) + 1) := by ring
    _ ≤ taoVdcBareMax j N T * (4 * Real.log (2 + T)) :=
      mul_le_mul_of_nonneg_left (taoVdc_log_power_le_four_log j hT.le) hmax0
    _ = _ := by ring

theorem taoLogDirichlet_short_equationEight_bound (t : Real) (K N M : Nat)
    (hK : 2 ≤ K) (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0)
    (hNT : (N : Real) ≤ taoLogFrequency t)
    (hupper : taoLogFrequency t ≤ (N : Real) ^ K) :
    ‖∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        taoVdcSecond K N (taoLogFrequency t) := by
  have hN1 : 1 ≤ (N : Real) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hT := taoLogFrequency_pos ht
  obtain ⟨j, hj, hjmax⟩ := taoVdcEquationEight hN1 hT hNT K hK hupper
  have hj2 := (Finset.mem_Icc.mp hj).1
  have hbase := taoLogDirichlet_short_vdc_bound t j N M hj2 hN hMN ht
  have hamp := taoLogDerivativeAmplitude_uniform hj2
  have hrate0 := taoVdcRate_le_log_bareMax j (N := (N : Real)) (by exact_mod_cast hN) hT
  have hlogC : 0 ≤ 4 * Real.log (2 + taoLogFrequency t) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  have hrate := hrate0.trans (mul_le_mul_of_nonneg_left hjmax hlogC)
  have hcoef : 0 ≤ 256 * (2 : Real) ^ 32 := by positivity
  calc
    _ ≤ 256 * taoLogDerivativeAmplitude j ^ (2 * taoVdcAlpha j) *
        taoVdcRate j N (taoLogFrequency t) := hbase
    _ ≤ 256 * (2 : Real) ^ 32 *
        (4 * Real.log (2 + taoLogFrequency t) * taoVdcSecond K N (taoLogFrequency t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hamp (by norm_num : (0 : Real) ≤ 256)) hrate
        (taoVdcRate_pos j (by exact_mod_cast hN) hT).le hcoef
    _ = _ := by norm_num; ring

/-- Raising the minimal containing order by one makes Equation (8)
produce an actual decay factor no larger than (1/N)^beta. -/
theorem taoLogDirichlet_short_selected_decay (t : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0)
    (hNT : (N : Real) ≤ taoLogFrequency t) :
    ‖∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (1 / (N : Real)) ^
          (taoVdcBeta (taoFrequencyOrder N (taoLogFrequency t) hN + 1)) := by
  let k := taoFrequencyOrder N (taoLogFrequency t) hN
  have hk : 2 ≤ k := taoFrequencyOrder_two_le N (taoLogFrequency t) hN
  have hNpos : 0 < N := by omega
  have hT := taoLogFrequency_pos ht
  have hupper0 := taoFrequencyOrder_upper N (taoLogFrequency t) hN
  have hN1 : 1 ≤ (N : Real) := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : Real) ^ k ≤ (N : Real) ^ (k + 1) :=
    pow_le_pow_right₀ hN1 (by omega)
  have hbase := taoLogDirichlet_short_equationEight_bound t (k + 1) N M (by omega)
    hNpos hMN ht hNT (hupper0.trans hpow)
  have hratio : taoLogFrequency t / (N : Real) ^ (k + 1) ≤ 1 / (N : Real) := by
    have hNp : 0 < (N : Real) := by positivity
    apply (div_le_div_iff₀ (pow_pos hNp (k + 1)) hNp).2
    rw [show k + 1 = k + 1 by rfl, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hupper0 hNp.le]
  have hb := taoVdcBeta_pos (by omega : 2 ≤ k + 1)
  have hdecay := Real.rpow_le_rpow (by positivity) hratio hb.le
  have hlogC : 0 ≤ (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  unfold taoVdcSecond at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_left hdecay hlogC)

end

end Erdos1212Kernel
