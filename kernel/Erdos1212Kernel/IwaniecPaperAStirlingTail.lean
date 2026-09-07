import Erdos1212Kernel.IwaniecPaperACoarsePrimeTail

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem iwaniecFactorial_ge_stirling_power (n : Nat) (hn : 0 < n) :
    ((n : Real) / Real.exp 1) ^ n ≤ (n.factorial : Real) := by
  have hnPos : (0 : Real) < n := by exact_mod_cast hn
  have heN : Real.exp (n : Real) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul (1 : Real) n
  calc
    ((n : Real) / Real.exp 1) ^ n =
        Real.exp ((n : Real) * Real.log n - n) := by
      rw [div_pow, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hnPos, heN]
    _ ≤ Real.exp (Real.log (n.factorial : Real)) := Real.exp_le_exp.mpr
      (Erdos696.Mertens.log_factorial_ge n hn)
    _ = (n.factorial : Real) := Real.exp_log (by exact_mod_cast Nat.factorial_pos n)

theorem iwaniecFactorialTerm_le_stirling_power
    {M : Real} (hM : 0 ≤ M) (n : Nat) (hn : 0 < n) :
    iwaniecFactorialTerm M n ≤ (Real.exp 1 * M / n) ^ n := by
  have hnPos : (0 : Real) < n := by exact_mod_cast hn
  have hdenPos : 0 < ((n : Real) / Real.exp 1) ^ n := by positivity
  have hbound := div_le_div_of_nonneg_left (pow_nonneg hM n) hdenPos
    (iwaniecFactorial_ge_stirling_power n hn)
  change iwaniecFactorialTerm M n ≤ _ at hbound
  calc
    iwaniecFactorialTerm M n ≤ M ^ n / ((n : Real) / Real.exp 1) ^ n := hbound
    _ = (Real.exp 1 * M / n) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp

theorem eventually_iwaniecMertens_reciprocal_le_const_loglog
    {c : Real} (hc : 1 < c) :
    ∀ᶠ N : Nat in atTop,
      Erdos696.Mertens.primeReciprocalSum N ≤ c * Real.log (Real.log N) := by
  let constant := Erdos696.Mertens.meisselMertensConstant
  have hdiff := Erdos696.Mertens.mertens_second_theorem.eventually
    (gt_mem_nhds (show constant < constant + 1 by linarith))
  have hloglog : Tendsto (fun N : Nat => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hdiff,
    hloglog.eventually (eventually_ge_atTop ((constant + 1) / (c - 1)))] with N hN hlarge
  have hscaled := (div_le_iff₀ (by linarith : 0 < c - 1)).1 hlarge
  linarith

theorem eventually_iwaniecStrictPrimeReciprocalSum_le_const_loglog
    {c : Real} (hc : 1 < c) :
    ∀ᶠ level : Real in atTop, ∀ z : Real, z ≤ level →
      iwaniecStrictPrimeReciprocalSum z ≤ c * Real.log (Real.log level) := by
  have hfloor := (tendsto_nat_floor_atTop (α := Real)).eventually
    (eventually_iwaniecMertens_reciprocal_le_const_loglog hc)
  filter_upwards [eventually_ge_atTop (3 : Real), hfloor] with level hlevel hM z hz
  have hfloorTwo : 2 ≤ ⌊level⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfloorOne : (1 : Real) < (⌊level⌋₊ : Real) := by exact_mod_cast (show 1 < ⌊level⌋₊ by omega)
  have hlog : Real.log (⌊level⌋₊ : Real) ≤ Real.log level :=
    Real.log_le_log (zero_lt_one.trans hfloorOne) (Nat.floor_le (by linarith))
  have hloglog : Real.log (Real.log (⌊level⌋₊ : Real)) ≤ Real.log (Real.log level) :=
    Real.log_le_log (Real.log_pos hfloorOne) hlog
  exact (iwaniecStrictPrimeReciprocalSum_le_mertens_floor hz).trans
    (hM.trans (mul_le_mul_of_nonneg_left hloglog (by linarith)))

theorem eventually_iwaniecExp_mul_primeReciprocal_le_three_loglog :
    ∀ᶠ level : Real in atTop, ∀ z : Real, z ≤ level →
      Real.exp 1 * iwaniecStrictPrimeReciprocalSum z ≤ 3 * Real.log (Real.log level) := by
  have hc : (1 : Real) < 3 / Real.exp 1 := by
    rw [lt_div_iff₀ (Real.exp_pos 1), one_mul]
    exact Real.exp_one_lt_three
  filter_upwards [eventually_iwaniecStrictPrimeReciprocalSum_le_const_loglog hc]
    with level hlevel z hz
  have hscaled := mul_le_mul_of_nonneg_left (hlevel z hz) (Real.exp_pos 1).le
  have he : Real.exp 1 * (3 / Real.exp 1 * Real.log (Real.log level)) =
      3 * Real.log (Real.log level) := by field_simp
  rwa [he] at hscaled

/-- The literal short/long bound after Stirling, with the source's constant
`3 log log y` in the long-layer base.  The integer splitting threshold is
still explicit, so later rounding of `xi_1` cannot change the carrier. -/
theorem eventually_iwaniecPaperA_stirling_short_long_bound :
    ∀ᶠ level : Real in atTop, ∀ rank K : Nat, ∀ s : Real,
      0 < K → 1 ≤ s → 6 * Real.log (Real.log level) ≤ (K + 1 : Nat) →
      (iwaniecPaperA rank level s : Real) ≤
        3 * Real.exp ((K : Real) * Real.log level / s) +
          2 * level * (3 * Real.log (Real.log level) / K) ^ K := by
  filter_upwards [eventually_iwaniecExp_mul_primeReciprocal_le_three_loglog,
    eventually_gt_atTop (1 : Real)] with level hM hlevel
  intro rank K s hK hs hthreshold
  let z := Real.exp (Real.log level / s)
  have hzOne : 1 ≤ z := Real.one_le_exp_iff.mpr
    (div_nonneg (Real.log_pos hlevel).le (by linarith))
  have hzLevel : z ≤ level := iwaniecPaperCutoff_le_level hlevel hs
  let M := iwaniecStrictPrimeReciprocalSum z
  have hMNonneg : 0 ≤ M := by
    exact Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have heM : Real.exp 1 * M ≤ 3 * Real.log (Real.log level) := hM z hzLevel
  have hMLe : M ≤ 3 * Real.log (Real.log level) := by
    have he : 1 ≤ Real.exp 1 := by have := Real.exp_one_gt_two; linarith
    nlinarith
  have hcount := iwaniecPaperSupportCount_short_long_bound rank K
    (zero_le_one.trans hlevel.le)
    hzOne (by change 2 * M ≤ (K + 1 : Nat); linarith)
  have htail := iwaniecFactorialTerm_le_stirling_power hMNonneg K hK
  have hKPos : (0 : Real) < K := by exact_mod_cast hK
  have hbase := div_le_div_of_nonneg_right heM hKPos.le
  have hbaseNonneg : 0 ≤ Real.exp 1 * M / K := by positivity
  have hpower := pow_le_pow_left₀ hbaseNonneg hbase K
  have hscaled := mul_le_mul_of_nonneg_left (htail.trans hpower)
    (by positivity : (0 : Real) ≤ 2 * level)
  have hzPower : z ^ K = Real.exp ((K : Real) * Real.log level / s) := by
    dsimp [z]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hzPower] at hcount
  change (iwaniecPaperA rank level s : Real) ≤
    3 * Real.exp ((K : Real) * Real.log level / s) + 2 * level * M ^ K / K.factorial at hcount
  unfold iwaniecFactorialTerm at hscaled
  have htailScaled : 2 * level * M ^ K / K.factorial ≤
      2 * level * (3 * Real.log (Real.log level) / K) ^ K := by
    simpa only [mul_div_assoc] using hscaled
  exact hcount.trans (add_le_add le_rfl htailScaled)

end

end Erdos1212Kernel
