import Erdos1212Kernel.IwaniecXiPrimeCutoff
import Erdos1212Kernel.IwaniecXiTailScalar

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1600000

theorem eventually_iwaniecLogLog_le_two_log_xi :
    ∀ᶠ level : Real in atTop,
      Real.log (Real.log level) ≤ 2 * Real.log (iwaniecPaperXi level) := by
  have hsmall := (tendsto_iwaniecLog_over_sqrt_zero.comp tendsto_iwaniecLogLog_atTop).eventually
    (gt_mem_nhds (show (0 : Real) < 1 by norm_num))
  have hdiff := tendsto_iwaniecShiftedLogLog_difference.eventually
    (gt_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [eventually_iwaniecXi_denominator_bound, hsmall, hdiff,
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (4 : Real))]
    with level hdata hsmall hdiff ht
  obtain ⟨hy, htOne, hu, hden⟩ := hdata
  have htPos : 0 < Real.log (Real.log level) := by linarith
  have hrootPos := Real.sqrt_pos.mpr htPos
  have hpoly := (div_lt_iff₀ hrootPos).1 hsmall
  have huUpper : Real.log (Real.log (3 * level)) ≤ 2 * Real.log (Real.log level) := by
    linarith
  have hlogu := Real.log_le_log hu huUpper
  rw [Real.log_mul (by norm_num) htPos.ne'] at hlogu
  have hlogt : 0 ≤ Real.log (Real.log (Real.log level)) := Real.log_nonneg htOne
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    linarith
  have hrootSmall : Real.sqrt (Real.log (Real.log level)) ≤
      Real.log (Real.log level) / 2 := by
    have hsquare := Real.sq_sqrt htPos.le
    have hrootNonneg := Real.sqrt_nonneg (Real.log (Real.log level))
    nlinarith
  rw [iwaniecPaperXi_log hy hu]
  linarith

/-- Long-tail bound on the actual strict prime pool of the far point. -/
theorem eventually_iwaniecPaperA_far_point_short_plus_long :
    ∀ᶠ level : Real in atTop, ∀ rank : Nat,
      (iwaniecPaperA rank level (iwaniecPaperXi level - 1) : Real) ≤
        iwaniecXiShortMajorant level +
          level * Real.exp
            (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) +
              iwaniecPaperXi level * Real.log (Real.log (iwaniecPaperXi level))) := by
  have hlogXi := Real.tendsto_log_atTop.comp tendsto_iwaniecPaperXi_atTop
  have hloglogXi := Real.tendsto_log_atTop.comp hlogXi
  have hslack := tendsto_iwaniecPaperXi_atTop.eventually eventually_iwaniecXiSplit_slack
  filter_upwards [eventually_iwaniecXiPrimeReciprocal_exp_le_sqrt_loglog,
    eventually_iwaniecPaperXiSplit_ge_six_loglog, eventually_iwaniecLogLog_le_two_log_xi,
    hslack, hlogXi.eventually (eventually_ge_atTop (2 : Real)),
    hloglogXi.eventually (eventually_ge_atTop (6 : Real)),
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (1 : Real)),
    eventually_gt_atTop (1 : Real)]
    with level hM hsplit htv hxi hlog hloglog ht hy
  intro rank
  let xi := iwaniecPaperXi level
  let t := Real.log (Real.log level)
  let K := iwaniecXiSplitThreshold xi
  let z := iwaniecXiPrimeCutoff level
  let M := iwaniecStrictPrimeReciprocalSum z
  have hxiOne : 1 < xi := by dsimp [xi]; linarith [hxi.1]
  have hlogOne : 1 < Real.log xi := by dsimp [xi]; linarith
  have hK : 0 < K := iwaniecXiSplitThreshold_pos hxiOne hlogOne
  have hKPos : (0 : Real) < K := by exact_mod_cast hK
  have htPos : 0 < t := by dsimp [t]; linarith
  have hrootPos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htPos
  have hrootLe : Real.sqrt t ≤ t := by
    have hsq := Real.sq_sqrt htPos.le
    have hroot := Real.sqrt_nonneg t
    change 1 ≤ t at ht
    nlinarith
  have hMNonneg : 0 ≤ M :=
    Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hMLe : M ≤ Real.sqrt t := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    have h := mul_le_mul_of_nonneg_right he hMNonneg
    change Real.exp 1 * M ≤ Real.sqrt t at hM
    nlinarith
  have hKLower : 6 * t ≤ (K : Real) :=
    hsplit.trans (iwaniecXiSplit_le_threshold xi)
  have hthreshold : 2 * M ≤ (K + 1 : Nat) := by
    push_cast
    linarith
  have hzOne : 1 ≤ z := Real.one_le_exp_iff.mpr
    (div_nonneg (Real.log_pos hy).le (by linarith [hxi.1]))
  have hcount := iwaniecPaperSupportCount_sharp_short_long_bound rank K hK
    (zero_le_one.trans hy.le) hzOne hthreshold
  change (iwaniecPaperA rank level (xi - 1) : Real) ≤
    3 * z ^ (K - 1) + 2 * level * M ^ K / K.factorial at hcount
  have hstirling := iwaniecFactorialTerm_le_stirling_power hMNonneg K hK
  have hbase := div_le_div_of_nonneg_right hM hKPos.le
  have hterm : iwaniecFactorialTerm M K ≤ (Real.sqrt t / (K : Real)) ^ K :=
    hstirling.trans (pow_le_pow_left₀ (by positivity) hbase K)
  have hrootSplit : Real.sqrt t ≤ iwaniecXiSplit xi := by
    change 6 * t ≤ iwaniecXiSplit xi at hsplit
    linarith
  have hround := iwaniecXiSplitThreshold_long_power_le hxiOne hlogOne hrootPos hrootSplit
  have hscalar := iwaniecXi_sqrt_tail_scalar (by linarith [hxi.1])
    hlog hloglog ht htv
  have hlongTerm : 2 * iwaniecFactorialTerm M K ≤
      Real.exp (-xi * Real.log xi + xi * Real.log (Real.log xi)) :=
    (mul_le_mul_of_nonneg_left (hterm.trans hround) (show (0 : Real) ≤ 2 by norm_num)).trans hscalar
  have hlong : 2 * level * M ^ K / K.factorial ≤
      level * Real.exp (-xi * Real.log xi + xi * Real.log (Real.log xi)) := by
    have h := mul_le_mul_of_nonneg_left hlongTerm (zero_le_one.trans hy.le)
    convert h using 1 <;> unfold iwaniecFactorialTerm <;> ring
  have hzPower : z ^ (K - 1) =
      Real.exp (((K - 1 : Nat) : Real) * Real.log level / (xi - 1)) := by
    dsimp [z, iwaniecXiPrimeCutoff, xi]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hshort : 3 * z ^ (K - 1) ≤ iwaniecXiShortMajorant level := by
    rw [hzPower]
    have h := mul_le_mul_of_nonneg_left
      (iwaniecXiSplitThreshold_short_exp_le hxiOne hlogOne hxi.2.2 hy)
      (show (0 : Real) ≤ 3 by norm_num)
    convert h using 1 <;> dsimp [iwaniecXiShortMajorant, xi, K] <;> ring
  exact hcount.trans (add_le_add hshort hlong)

/-- The source's far-point exponential envelope, now for the actual `A`
carrier and uniformly in its rank. -/
theorem eventually_iwaniecPaperA_far_point_source_bound :
    ∀ᶠ level : Real in atTop, ∀ rank : Nat,
      (iwaniecPaperA rank level (iwaniecPaperXi level - 1) : Real) ≤
        level * Real.exp
          (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) +
            iwaniecPaperXi level * Real.log (Real.log (iwaniecPaperXi level)) +
            2 * iwaniecPaperXi level) := by
  have hlogXi := Real.tendsto_log_atTop.comp tendsto_iwaniecPaperXi_atTop
  have hloglogXi := Real.tendsto_log_atTop.comp hlogXi
  filter_upwards [eventually_iwaniecPaperA_far_point_short_plus_long,
    eventually_iwaniecXiShortMajorant_source_bound, eventually_gt_atTop (1 : Real),
    tendsto_iwaniecPaperXi_atTop.eventually (eventually_ge_atTop (1 : Real)),
    hlogXi.eventually (eventually_ge_atTop (1 : Real)),
    hloglogXi.eventually (eventually_ge_atTop (1 : Real))]
    with level hA hshort hy hxi hlog hloglog
  intro rank
  let xi := iwaniecPaperXi level
  let exponent := -xi * Real.log xi + xi * Real.log (Real.log xi)
  change 1 ≤ Real.log xi at hlog
  change 1 ≤ Real.log (Real.log xi) at hloglog
  have hpow : Real.log xi ≤ Real.log xi ^ (6 / 5 : Real) := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog (show (1 : Real) ≤ 6 / 5 by norm_num)
    simpa using h
  have hshortExponent : -xi * Real.log xi ^ (6 / 5 : Real) + xi ≤ exponent := by
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0 ≤ xi by dsimp [xi]; linarith)
    have h2 := mul_le_mul_of_nonneg_left hloglog (show 0 ≤ xi by dsimp [xi]; linarith)
    dsimp [exponent]
    nlinarith
  have hshortBase : iwaniecXiShortMajorant level ≤ level * Real.exp exponent :=
    hshort.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hshortExponent)
      (zero_le_one.trans hy.le))
  have htwo : (2 : Real) ≤ Real.exp (2 * xi) :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by dsimp [xi]; linarith))
  calc
    (iwaniecPaperA rank level (xi - 1) : Real) ≤
        iwaniecXiShortMajorant level + level * Real.exp exponent := hA rank
    _ ≤ level * Real.exp exponent + level * Real.exp exponent :=
      add_le_add hshortBase le_rfl
    _ = 2 * (level * Real.exp exponent) := by ring
    _ ≤ Real.exp (2 * xi) * (level * Real.exp exponent) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by
      change Real.exp (2 * xi) * (level * Real.exp exponent) =
        level * Real.exp (exponent + 2 * xi)
      conv_rhs => rw [Real.exp_add]
      ring

end

end Erdos1212Kernel
