import Erdos1212Kernel.IwaniecPaperAFactorialSaturation
import Erdos1212Kernel.Analytic.BrunTitchmarsh

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem iwaniecFactorial_dominates_level
    {level : Real} (hlevel : 1 < level)
    (hloglog : 4 ≤ Real.log (Real.log level))
    (hsmall : Real.log (Real.log (Real.log level)) ≤
      Real.log (Real.log level) / 4)
    (n : Nat) (hn : 2 * Real.log level / Real.log (Real.log level) ≤ (n : Real)) :
    level ≤ (n.factorial : Real) := by
  let L := Real.log level
  let t := Real.log L
  have hL : 0 < L := Real.log_pos hlevel
  have ht : 0 < t := by dsimp [t, L]; linarith
  have htFour : 4 ≤ t := hloglog
  have hsmall' : Real.log t ≤ t / 4 := hsmall
  have htL : t ≤ L := (Real.log_le_sub_one_of_pos hL).trans (by linarith)
  let x := 2 * L / t
  have hxPos : 0 < x := div_pos (by positivity) ht
  have hxTwo : 2 ≤ x := by
    apply (le_div_iff₀ ht).2
    nlinarith
  have hxn : x ≤ (n : Real) := hn
  have hnTwo : (2 : Real) ≤ n := hxTwo.trans hxn
  have hnNat : 1 ≤ n := by exact_mod_cast (show (1 : Real) ≤ n by linarith)
  have hnPos : (0 : Real) < n := by linarith
  have hlogx : Real.log x = Real.log 2 + t - Real.log t := by
    dsimp [x, t]
    rw [Real.log_div (by positivity) ht.ne', Real.log_mul (by norm_num) hL.ne']
  have hlogxLower : 3 * t / 4 ≤ Real.log x := by
    rw [hlogx]
    have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlognLower : t / 2 ≤ Real.log (n : Real) - 1 := by
    have hmono := Real.log_le_log hxPos hxn
    linarith
  have hnProduct : 2 * L ≤ (n : Real) * t := (div_le_iff₀ ht).1 hxn
  have hmain : L ≤ (n : Real) * Real.log (n : Real) - n := by
    have hmul := mul_le_mul_of_nonneg_left hlognLower hnPos.le
    nlinarith
  have hstirling := Erdos696.Mertens.log_factorial_ge n hnNat
  have hlog : Real.log level ≤ Real.log (n.factorial : Real) := hmain.trans hstirling
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (zero_lt_one.trans hlevel),
    Real.exp_log (by exact_mod_cast Nat.factorial_pos n)] at hexp

/-- Uniform large-rank threshold in the source's normalization. -/
theorem eventually_iwaniecFactorial_dominates_level :
    ∀ᶠ level : Real in atTop, ∀ n : Nat,
      2 * Real.log level / Real.log (Real.log level) ≤ (n : Real) →
        level ≤ (n.factorial : Real) := by
  have hloglog : Tendsto (fun level : Real => Real.log (Real.log level))
      atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogRatio : Tendsto (fun t : Real => Real.log t / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall := (hlogRatio.comp hloglog).eventually
    (gt_mem_nhds (show (0 : Real) < 1 / 4 by norm_num))
  filter_upwards [eventually_gt_atTop (1 : Real),
    hloglog.eventually (eventually_ge_atTop (4 : Real)), hsmall] with level hy ht hratio
  intro n hn
  apply iwaniecFactorial_dominates_level hy ht _ n hn
  have htPos : 0 < Real.log (Real.log level) := by linarith
  have hscaled := (div_lt_iff₀ htPos).1 hratio
  linarith

/-- The large-rank branch needs no prime distribution hypothesis: the same
parity count is already saturated beyond `2 log y / log log y`. -/
theorem eventually_iwaniecPaperA_largeRank_saturated :
    ∀ᶠ level : Real in atTop, ∀ rank : Nat, ∀ s : Real,
      2 * Real.log level / Real.log (Real.log level) ≤ (rank + 2 : Nat) →
        iwaniecPaperA (rank + 2) level s = iwaniecPaperA rank level s := by
  filter_upwards [eventually_iwaniecFactorial_dominates_level] with level hlevel
  intro rank s hrank
  exact iwaniecPaperA_rank_add_two_saturated rank level s (hlevel (rank + 2) hrank)

end

end Erdos1212Kernel
