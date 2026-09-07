import Erdos1212Kernel.IwaniecPaperAShortLongBound
import Erdos1212Kernel.IwaniecPaperARecursion

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem iwaniecStrictPrimeReciprocalSum_le_mertens_floor
    {z level : Real} (hz : z ≤ level) :
    iwaniecStrictPrimeReciprocalSum z ≤
      Erdos696.Mertens.primeReciprocalSum ⌊level⌋₊ := by
  have hsub : iwaniecStrictPrimePool z ⊆ Nat.primesLE ⌊level⌋₊ := by
    intro p hp
    obtain ⟨hprime, hlt⟩ := mem_iwaniecStrictPrimePool.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hlt.le.trans hz), hprime⟩
  unfold iwaniecStrictPrimeReciprocalSum
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun p : Nat => (p : Real)⁻¹) hsub
    (fun p _hp _hnot => inv_nonneg.mpr (Nat.cast_nonneg p))
  simpa only [Erdos696.Mertens.primeReciprocalSum,
    Nat.primesLE_eq_filter_range, one_div] using hsum

theorem eventually_iwaniecMertens_reciprocal_le_three_loglog :
    ∀ᶠ N : Nat in atTop,
      Erdos696.Mertens.primeReciprocalSum N ≤ 3 * Real.log (Real.log N) := by
  let c := Erdos696.Mertens.meisselMertensConstant
  have hdiff := Erdos696.Mertens.mertens_second_theorem.eventually
    (gt_mem_nhds (show c < c + 1 by linarith))
  have hloglog : Tendsto (fun N : Nat => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hdiff, hloglog.eventually (eventually_ge_atTop (c + 1)),
    hloglog.eventually (eventually_ge_atTop (0 : Real))] with N hN hlarge hnonneg
  linarith

/-- The elementary Mertens bound used in the long-layer tail, uniformly for
every smaller strict prime cutoff.  No effective prime error is asserted. -/
theorem eventually_iwaniecStrictPrimeReciprocalSum_le_three_loglog :
    ∀ᶠ level : Real in atTop, ∀ z : Real, z ≤ level →
      iwaniecStrictPrimeReciprocalSum z ≤ 3 * Real.log (Real.log level) := by
  have hfloor := (tendsto_nat_floor_atTop (α := Real)).eventually
    eventually_iwaniecMertens_reciprocal_le_three_loglog
  filter_upwards [eventually_ge_atTop (3 : Real), hfloor] with level hlevel hM z hz
  have hfloorTwo : 2 ≤ ⌊level⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfloorOne : (1 : Real) < (⌊level⌋₊ : Real) := by exact_mod_cast (show 1 < ⌊level⌋₊ by omega)
  have hlog : Real.log (⌊level⌋₊ : Real) ≤ Real.log level :=
    Real.log_le_log (zero_lt_one.trans hfloorOne) (Nat.floor_le (by linarith))
  have hloglog : Real.log (Real.log (⌊level⌋₊ : Real)) ≤ Real.log (Real.log level) :=
    Real.log_le_log (Real.log_pos hfloorOne) hlog
  exact (iwaniecStrictPrimeReciprocalSum_le_mertens_floor hz).trans
    (hM.trans (mul_le_mul_of_nonneg_left hloglog (by norm_num)))

theorem eventually_iwaniecPaperSupportCount_short_long_loglog
    : ∀ᶠ level : Real in atTop, ∀ rank K : Nat, ∀ z : Real,
      1 ≤ z → z ≤ level →
      6 * Real.log (Real.log level) ≤ (K + 1 : Nat) →
      (iwaniecPaperSupportCount rank level z : Real) ≤
        3 * z ^ K + 2 * level * (3 * Real.log (Real.log level)) ^ K / K.factorial := by
  filter_upwards [eventually_iwaniecStrictPrimeReciprocalSum_le_three_loglog,
    eventually_ge_atTop (1 : Real)] with level hM hlevel
  intro rank K z hz hzLevel hK
  have hrecip := hM z hzLevel
  have hrecipNonneg : 0 ≤ iwaniecStrictPrimeReciprocalSum z := by
    unfold iwaniecStrictPrimeReciprocalSum
    exact Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hthreshold : 2 * iwaniecStrictPrimeReciprocalSum z ≤ (K + 1 : Nat) := by
    linarith
  have hbound := iwaniecPaperSupportCount_short_long_bound rank K
    (by linarith : 0 ≤ level) hz hthreshold
  apply hbound.trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrecipNonneg hrecip K)
    (by positivity)

/-- Quantitative far-cutoff bound, uniform in the rank, with exactly the
short/long split used in Theorem 5. -/
theorem eventually_iwaniecPaperA_short_long_loglog :
    ∀ᶠ level : Real in atTop, ∀ rank K : Nat, ∀ s : Real,
      1 ≤ s → 6 * Real.log (Real.log level) ≤ (K + 1 : Nat) →
      (iwaniecPaperA rank level s : Real) ≤
        3 * Real.exp ((K : Real) * Real.log level / s) +
          2 * level * (3 * Real.log (Real.log level)) ^ K / K.factorial := by
  filter_upwards [eventually_iwaniecPaperSupportCount_short_long_loglog,
    eventually_gt_atTop (1 : Real)] with level hbound hlevel
  intro rank K s hs hK
  have hz : 1 ≤ Real.exp (Real.log level / s) :=
    Real.one_le_exp_iff.mpr (div_nonneg (Real.log_pos hlevel).le (by linarith))
  have h := hbound rank K (Real.exp (Real.log level / s)) hz
    (iwaniecPaperCutoff_le_level hlevel hs) hK
  have hexp : Real.exp (Real.log level / s) ^ K =
      Real.exp ((K : Real) * Real.log level / s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at h
  exact h

end

end Erdos1212Kernel
