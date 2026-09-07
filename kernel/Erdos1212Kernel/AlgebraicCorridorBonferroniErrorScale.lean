import Erdos1212Kernel.AlgebraicCorridorBonferroniCard

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def bonferroniCutoff (N : ℝ) : ℕ := 2 * bonferroniRank N + 1

def corridorMediumFiniteError (N : ℝ) : ℝ :=
  ((mediumPrimePool N).card : ℝ) *
      ((rosserTruncatedSubsets
        (smallPrimePool N) (bonferroniRank N)).card : ℝ) +
    (((mediumPrimePool N).powersetCard 2).card : ℝ) *
      ((corridorEvenTruncatedSubsets
        (smallPrimePool N) (bonferroniRank N)).card : ℝ)

theorem eventually_smallPrimePool_card_add_one_le_three_z :
    ∀ᶠ N : ℝ in atTop,
      ((smallPrimePool N).card + 1 : ℕ) ≤ (3 * z N : ℝ) := by
  filter_upwards [eventually_large_domain,
    z_tendsto.eventually_ge_atTop (1 : ℝ)] with N hdom hzOne
  have hsubset : smallPrimePool N ⊆ iwaniecStrictPrimePool (z N + 1) :=
    Finset.filter_subset _ _
  have hcardSubset := Finset.card_le_card hsubset
  have hstrict := iwaniecStrictPrimePool_card_le
    (show 0 ≤ z N + 1 by linarith)
  have hcardR : ((smallPrimePool N).card : ℝ) ≤ z N + 1 := by
    have hcardCast : ((smallPrimePool N).card : ℝ) ≤
        ((iwaniecStrictPrimePool (z N + 1)).card : ℝ) := by
      exact_mod_cast hcardSubset
    exact hcardCast.trans hstrict
  push_cast
  linarith

theorem eventually_mediumPrimePool_card_le_three_z :
    ∀ᶠ N : ℝ in atTop,
      ((mediumPrimePool N).card : ℝ) ≤ 3 * z N := by
  filter_upwards [eventually_large_domain,
    z_tendsto.eventually_ge_atTop (1 : ℝ)] with N hdom hzOne
  have hsubset : mediumPrimePool N ⊆
      iwaniecStrictPrimePool (2 * z N + 1) := Finset.filter_subset _ _
  have hcardSubset := Finset.card_le_card hsubset
  have hstrict := iwaniecStrictPrimePool_card_le
    (show 0 ≤ 2 * z N + 1 by linarith)
  have hcardCast : ((mediumPrimePool N).card : ℝ) ≤
      ((iwaniecStrictPrimePool (2 * z N + 1)).card : ℝ) := by
    exact_mod_cast hcardSubset
  exact (hcardCast.trans hstrict).trans (by linarith)

theorem eventually_bonferroniCutoff_le_105_L :
    ∀ᶠ N : ℝ in atTop,
      (bonferroniCutoff N : ℝ) ≤ 105 * L N := by
  filter_upwards [eventually_large_domain] with N hdom
  have hceil : (Nat.ceil (50 * L N) : ℝ) ≤ 50 * L N + 1 :=
    (Nat.ceil_lt_add_one
      (mul_nonneg (by norm_num) (by linarith [hdom.2.2]))).le
  unfold bonferroniCutoff bonferroniRank
  push_cast
  nlinarith

theorem mediumPrimePair_card_le_square (N : ℝ) :
    (((mediumPrimePool N).powersetCard 2).card : ℝ) ≤
      ((mediumPrimePool N).card : ℝ) ^ 2 := by
  rw [Finset.card_powersetCard]
  exact_mod_cast Nat.choose_le_pow (mediumPrimePool N).card 2

theorem rosser_card_le_cutoff_power (N : ℝ) :
    ((rosserTruncatedSubsets
      (smallPrimePool N) (bonferroniRank N)).card : ℝ) ≤
      (bonferroniCutoff N : ℝ) *
        ((smallPrimePool N).card + 1 : ℕ) ^ bonferroniCutoff N := by
  have hbase := rosserTruncatedSubsets_card_le
    (smallPrimePool N) (bonferroniRank N)
  let A := (smallPrimePool N).card + 1
  let K₀ := 2 * bonferroniRank N
  let K := bonferroniCutoff N
  have hK : K₀ ≤ K := by dsimp [K₀, K, bonferroniCutoff]; omega
  have hA : 0 < A := by dsimp [A]; omega
  have hpow : A ^ K₀ ≤ A ^ K := Nat.pow_le_pow_right hA hK
  have hnat : K₀ * A ^ K₀ ≤ K * A ^ K :=
    Nat.mul_le_mul hK hpow
  exact_mod_cast hbase.trans hnat

theorem evenTruncated_card_le_cutoff_power (N : ℝ) :
    ((corridorEvenTruncatedSubsets
      (smallPrimePool N) (bonferroniRank N)).card : ℝ) ≤
      (bonferroniCutoff N : ℝ) *
        ((smallPrimePool N).card + 1 : ℕ) ^ bonferroniCutoff N := by
  exact_mod_cast corridorEvenTruncatedSubsets_card_le
    (smallPrimePool N) (bonferroniRank N)

theorem corridorMediumFiniteError_le_common (N : ℝ) :
    corridorMediumFiniteError N ≤
      (((mediumPrimePool N).card : ℝ) +
        ((mediumPrimePool N).card : ℝ) ^ 2) *
        (bonferroniCutoff N : ℝ) *
        (((smallPrimePool N).card + 1 : ℕ) : ℝ) ^ bonferroniCutoff N := by
  unfold corridorMediumFiniteError
  have hodd := rosser_card_le_cutoff_power N
  have heven := evenTruncated_card_le_cutoff_power N
  have hpair := mediumPrimePair_card_le_square N
  have hq : 0 ≤ ((mediumPrimePool N).card : ℝ) := by positivity
  have hp : 0 ≤ (((mediumPrimePool N).powersetCard 2).card : ℝ) := by positivity
  have hK : 0 ≤ (bonferroniCutoff N : ℝ) := by positivity
  have hA : 0 ≤ (((smallPrimePool N).card + 1 : ℕ) : ℝ) ^
      bonferroniCutoff N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hodd hq,
    mul_le_mul_of_nonneg_left heven hp,
    mul_le_mul_of_nonneg_right hpair (mul_nonneg hK hA)]

theorem eventually_corridorMediumFiniteError_le_envelope :
    ∀ᶠ N : ℝ in atTop,
      corridorMediumFiniteError N ≤
        12 * z N ^ 2 * (105 * L N) *
          (3 * z N) ^ bonferroniCutoff N := by
  filter_upwards [eventually_large_domain,
    z_tendsto.eventually_ge_atTop (1 : ℝ),
    eventually_smallPrimePool_card_add_one_le_three_z,
    eventually_mediumPrimePool_card_le_three_z,
    eventually_bonferroniCutoff_le_105_L] with
      N hdom hzOne hsmall hmedium hK
  have hcommon := corridorMediumFiniteError_le_common N
  have hmediumNonneg : 0 ≤ ((mediumPrimePool N).card : ℝ) := by positivity
  have hzNonneg : 0 ≤ z N := by linarith
  have hsum : ((mediumPrimePool N).card : ℝ) +
      ((mediumPrimePool N).card : ℝ) ^ 2 ≤ 12 * z N ^ 2 := by
    have hsq := pow_le_pow_left₀ hmediumNonneg hmedium 2
    nlinarith [sq_nonneg (z N - 1)]
  have hpow : ((((smallPrimePool N).card + 1 : ℕ) : ℝ) ^
      bonferroniCutoff N) ≤ (3 * z N) ^ bonferroniCutoff N :=
    pow_le_pow_left₀ (by positivity) hsmall _
  have hleftNonneg : 0 ≤ ((mediumPrimePool N).card : ℝ) +
      ((mediumPrimePool N).card : ℝ) ^ 2 := by positivity
  have hrightNonneg : 0 ≤ 12 * z N ^ 2 := by positivity
  have hKNonneg : 0 ≤ (bonferroniCutoff N : ℝ) := by positivity
  have hKLNonneg : 0 ≤ 105 * L N := by nlinarith [hdom.2.2]
  have hprod :
      (((mediumPrimePool N).card : ℝ) +
        ((mediumPrimePool N).card : ℝ) ^ 2) *
          (bonferroniCutoff N : ℝ) ≤
        (12 * z N ^ 2) * (105 * L N) :=
    mul_le_mul hsum hK hKNonneg hrightNonneg
  exact hcommon.trans (mul_le_mul hprod hpow (by positivity)
    (mul_nonneg hrightNonneg hKLNonneg))

theorem eventually_corridorMediumFiniteError_le_exp_fifth :
    ∀ᶠ N : ℝ in atTop,
      corridorMediumFiniteError N ≤ Real.exp (ell N / 5) := by
  filter_upwards [eventually_large_domain,
    z_tendsto.eventually_ge_atTop (1 : ℝ),
    eventually_bonferroniCutoff_le_105_L,
    eventually_corridorMediumFiniteError_le_envelope,
    eventually_C_mul_L_pow_lt_ell 20000 1] with
      N hdom hzOne hK herror hLsmall
  have hNPos : 0 < N := zero_lt_one.trans hdom.1
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hu : 0 < u N := by unfold u; positivity
  have hzPos : 0 < z N := z_pos hNPos hu
  have hlogz : Real.log (z N) = ell N / u N := log_z hNPos hu
  have hlogzPos : 0 < Real.log (z N) := by rw [hlogz]; positivity
  have hLlogz : L N * Real.log (z N) = ell N / 1000 := by
    rw [hlogz]
    unfold u
    field_simp [hLPos.ne']
  have hlogzUpper : Real.log (z N) ≤ ell N / 1000 := by
    rw [hlogz]
    unfold u
    apply (div_le_iff₀ (by positivity : 0 < 1000 * L N)).mpr
    nlinarith
  have hlogThree : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogThreeZ : Real.log (3 * z N) ≤ 2 + Real.log (z N) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hzPos.ne']
    linarith
  have hlogThreeZNonneg : 0 ≤ Real.log (3 * z N) :=
    Real.log_nonneg (by nlinarith)
  have hKlog : (bonferroniCutoff N : ℝ) * Real.log (3 * z N) ≤
      105 * L N * (2 + Real.log (z N)) :=
    mul_le_mul hK hlogThreeZ (by positivity) (by positivity)
  have hexponent : 1260 * L N + 2 * Real.log (z N) +
      (bonferroniCutoff N : ℝ) * Real.log (3 * z N) ≤ ell N / 5 := by
    have hLsmall' : 20000 * L N < ell N := by simpa using hLsmall
    nlinarith
  have hcoef : 1260 * L N ≤ Real.exp (1260 * L N) := by
    have h := Real.add_one_le_exp (1260 * L N)
    linarith
  have hzSq : z N ^ 2 = Real.exp (2 * Real.log (z N)) := by
    calc
      z N ^ 2 = Real.exp (Real.log (z N)) ^ 2 := by
        rw [Real.exp_log hzPos]
      _ = Real.exp ((2 : ℝ) * Real.log (z N)) :=
        (Real.exp_nat_mul (Real.log (z N)) 2).symm
  have hthreePow : (3 * z N) ^ bonferroniCutoff N =
      Real.exp ((bonferroniCutoff N : ℝ) * Real.log (3 * z N)) := by
    calc
      (3 * z N) ^ bonferroniCutoff N =
          Real.exp (Real.log (3 * z N)) ^ bonferroniCutoff N := by
        rw [Real.exp_log (by positivity : 0 < 3 * z N)]
      _ = _ := (Real.exp_nat_mul (Real.log (3 * z N))
        (bonferroniCutoff N)).symm
  calc
    corridorMediumFiniteError N ≤
        12 * z N ^ 2 * (105 * L N) *
          (3 * z N) ^ bonferroniCutoff N := herror
    _ = (1260 * L N) * z N ^ 2 *
          (3 * z N) ^ bonferroniCutoff N := by ring
    _ ≤ Real.exp (1260 * L N) * z N ^ 2 *
          (3 * z N) ^ bonferroniCutoff N := by
      gcongr
    _ = Real.exp (1260 * L N + 2 * Real.log (z N) +
          (bonferroniCutoff N : ℝ) * Real.log (3 * z N)) := by
      rw [hzSq, hthreePow, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (ell N / 5) := Real.exp_le_exp.mpr hexponent

theorem eventually_corridorMediumFiniteError_le_N_fifth :
    ∀ᶠ N : ℝ in atTop,
      corridorMediumFiniteError N ≤ N ^ (1 / 5 : ℝ) := by
  filter_upwards [eventually_large_domain,
    eventually_corridorMediumFiniteError_le_exp_fifth] with N hdom herror
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hdom.1)]
  simpa [ell, div_eq_mul_inv, mul_comm] using herror

theorem eventually_corridorMediumCandidates_card_suberror_lower :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      (T : ℝ) *
          (corridorRoughDensityConstant / Real.log (z N) ^ 2) -
          N ^ (1 / 5 : ℝ) ≤
        ((corridorMediumWitnessCandidates (smallPrimePool N)
          (mediumPrimePool N) lower T).card : ℝ) := by
  filter_upwards [eventually_corridorMediumCandidates_main_lower,
    eventually_corridorRoughDensity_lower,
    eventually_corridorMediumFiniteError_le_N_fifth] with
      N hfinite hdensity herror
  intro lower T hlower
  have hfinite' := hfinite lower T hlower
  have hmain : (T : ℝ) *
      (corridorRoughDensityConstant / Real.log (z N) ^ 2) ≤
      (T : ℝ) *
        ((corridorEulerProduct (smallPrimePool N) - (ell N)⁻¹ ^ 200) *
            mediumPrimeReciprocalMass N -
          (corridorEulerProduct (smallPrimePool N) + (ell N)⁻¹ ^ 200) *
            (mediumPrimeReciprocalMass N ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg T)
  unfold corridorMediumFiniteError at herror
  ring_nf at hfinite' hmain ⊢
  linarith

theorem eventually_N_fifth_absorbed_by_rough_density :
    ∀ᶠ N : ℝ in atTop,
      4 * N ^ (1 / 5 : ℝ) ≤
        N ^ (9 / 10 : ℝ) *
          (corridorRoughDensityConstant / Real.log (z N) ^ 2) := by
  have hlittle := isLittleO_log_rpow_rpow_atTop 2
    (show (0 : ℝ) < 7 / 10 by norm_num)
  have heps : 0 < corridorRoughDensityConstant / 4 :=
    div_pos corridorRoughDensityConstant_pos (by norm_num)
  have hbound := hlittle.bound heps
  filter_upwards [eventually_large_domain,
    hbound, z_tendsto.eventually_ge_atTop (2 : ℝ)] with N hdom hboundN hzTwo
  have hNPos : 0 < N := zero_lt_one.trans hdom.1
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hu : 0 < u N := by unfold u; positivity
  have hlogz : Real.log (z N) = ell N / u N := log_z hNPos hu
  have hlogzPos : 0 < Real.log (z N) := by rw [hlogz]; positivity
  have hlogzLeEll : Real.log (z N) ≤ ell N := by
    rw [hlogz]
    apply (div_le_iff₀ hu).mpr
    have huOne : 1 ≤ u N := by unfold u; nlinarith [hdom.2.2]
    nlinarith
  have hlogSq : Real.log (z N) ^ 2 ≤ ell N ^ 2 :=
    pow_le_pow_left₀ hlogzPos.le hlogzLeEll 2
  have hbound' : ell N ^ 2 ≤
      (corridorRoughDensityConstant / 4) * N ^ (7 / 10 : ℝ) := by
    have hlogN : Real.log N = ell N := rfl
    rw [hlogN, Real.rpow_two] at hboundN
    have hleftNorm : ‖ell N ^ 2‖ = ell N ^ 2 :=
      Real.norm_of_nonneg (pow_nonneg hellPos.le 2)
    have hrightNorm : ‖N ^ (7 / 10 : ℝ)‖ = N ^ (7 / 10 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hNPos.le _)
    calc
      ell N ^ 2 = ‖ell N ^ 2‖ := hleftNorm.symm
      _ ≤ (corridorRoughDensityConstant / 4) *
          ‖N ^ (7 / 10 : ℝ)‖ := hboundN
      _ = (corridorRoughDensityConstant / 4) *
          N ^ (7 / 10 : ℝ) := by rw [hrightNorm]
  have hsmall : Real.log (z N) ^ 2 ≤
      (corridorRoughDensityConstant / 4) * N ^ (7 / 10 : ℝ) :=
    hlogSq.trans hbound'
  have hpowPos : 0 < N ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hNPos _
  have hscaled := mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hpowPos.le)
  have hpowers : N ^ (1 / 5 : ℝ) * N ^ (7 / 10 : ℝ) =
      N ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hNPos]
    norm_num
  have hcross : 4 * N ^ (1 / 5 : ℝ) * Real.log (z N) ^ 2 ≤
      N ^ (9 / 10 : ℝ) * corridorRoughDensityConstant := by
    calc
      4 * N ^ (1 / 5 : ℝ) * Real.log (z N) ^ 2 ≤
          4 * N ^ (1 / 5 : ℝ) *
            ((corridorRoughDensityConstant / 4) * N ^ (7 / 10 : ℝ)) := hscaled
      _ = N ^ (9 / 10 : ℝ) * corridorRoughDensityConstant := by
        rw [← hpowers]
        ring
  calc
    4 * N ^ (1 / 5 : ℝ) ≤
        (N ^ (9 / 10 : ℝ) * corridorRoughDensityConstant) /
          Real.log (z N) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hlogzPos)).mpr hcross
    _ = N ^ (9 / 10 : ℝ) *
        (corridorRoughDensityConstant / Real.log (z N) ^ 2) := by ring

theorem eventually_corridorMediumCandidates_card_half_main_lower :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      N ^ (9 / 10 : ℝ) ≤ 2 * (T : ℝ) →
      (T : ℝ) *
          (corridorRoughDensityConstant /
            (2 * Real.log (z N) ^ 2)) ≤
        ((corridorMediumWitnessCandidates (smallPrimePool N)
          (mediumPrimePool N) lower T).card : ℝ) := by
  filter_upwards [eventually_corridorMediumCandidates_card_suberror_lower,
    eventually_N_fifth_absorbed_by_rough_density,
    eventually_large_domain] with N hcount habsorb hdom
  intro lower T hlower hT
  have hcount' := hcount lower T hlower
  have hdensityNonneg : 0 ≤ corridorRoughDensityConstant /
      Real.log (z N) ^ 2 :=
    div_nonneg corridorRoughDensityConstant_pos.le (sq_nonneg _)
  have hTmain := mul_le_mul_of_nonneg_right hT hdensityNonneg
  have habsorbT : 2 * N ^ (1 / 5 : ℝ) ≤
      (T : ℝ) * (corridorRoughDensityConstant / Real.log (z N) ^ 2) :=
    by nlinarith
  calc
    (T : ℝ) * (corridorRoughDensityConstant /
        (2 * Real.log (z N) ^ 2)) =
      ((T : ℝ) * (corridorRoughDensityConstant /
        Real.log (z N) ^ 2)) / 2 := by ring
    _ ≤ (T : ℝ) * (corridorRoughDensityConstant /
        Real.log (z N) ^ 2) - N ^ (1 / 5 : ℝ) := by
      linarith
    _ ≤ ((corridorMediumWitnessCandidates (smallPrimePool N)
          (mediumPrimePool N) lower T).card : ℝ) := hcount'

theorem one_div_two_hundred_lt_corridorRoughDensityConstant :
    (1 / 200 : ℝ) < corridorRoughDensityConstant := by
  unfold corridorRoughDensityConstant
  norm_num

theorem eventually_rows_le_band_mul_rough_density :
    ∀ᶠ N : ℝ in atTop,
      (rows N : ℝ) ≤ (band N : ℝ) *
        (corridorRoughDensityConstant /
          (2 * Real.log (z N) ^ 2)) := by
  filter_upwards [eventually_large_domain] with N hdom
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hu : 0 < u N := by unfold u; positivity
  have hrows := (rows_bounds hdom.2.2).2
  have hband : 10000 * ell N ^ 2 ≤ (band N : ℝ) := by
    exact Nat.le_ceil _
  have hc : (1 / 200 : ℝ) ≤ corridorRoughDensityConstant :=
    one_div_two_hundred_lt_corridorRoughDensityConstant.le
  have hprod : 50 * ell N ^ 2 ≤
      (band N : ℝ) * corridorRoughDensityConstant := by
    have hmul := mul_le_mul hband hc (by norm_num) (by positivity)
    nlinarith
  have hlogz : Real.log (z N) = ell N / u N :=
    log_z (zero_lt_one.trans hdom.1) hu
  have hlogzPos : 0 < Real.log (z N) := by rw [hlogz]; positivity
  have hid : 25 * u N ^ 2 * (2 * Real.log (z N) ^ 2) =
      50 * ell N ^ 2 := by
    rw [hlogz]
    field_simp
    ring
  have hlower : 25 * u N ^ 2 ≤
      (band N : ℝ) * corridorRoughDensityConstant /
        (2 * Real.log (z N) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hid]
    exact hprod
  have hrowScale : (rows N : ℝ) ≤ 25 * u N ^ 2 := by
    unfold u
    nlinarith [sq_nonneg (L N)]
  calc
    (rows N : ℝ) ≤ 25 * u N ^ 2 := hrowScale
    _ ≤ (band N : ℝ) * corridorRoughDensityConstant /
        (2 * Real.log (z N) ^ 2) := hlower
    _ = (band N : ℝ) *
        (corridorRoughDensityConstant /
          (2 * Real.log (z N) ^ 2)) := by ring

theorem eventually_two_band_le_N_nine_tenths :
    ∀ᶠ N : ℝ in atTop,
      (2 * band N : ℕ) ≤ N ^ (9 / 10 : ℝ) := by
  have hlittle := isLittleO_log_rpow_rpow_atTop 2
    (show (0 : ℝ) < 9 / 10 by norm_num)
  have heps : (0 : ℝ) < 1 / 20002 := by norm_num
  have hbound := hlittle.bound heps
  filter_upwards [eventually_large_domain, hbound] with N hdom hboundN
  have hNPos : 0 < N := zero_lt_one.trans hdom.1
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hceil : (band N : ℝ) ≤ 10000 * ell N ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 10000 * ell N ^ 2)).le
  have hband : (2 * band N : ℕ) ≤ (20002 : ℝ) * ell N ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (ell N - 1)]
  have hbound' : ell N ^ 2 ≤ (1 / 20002 : ℝ) * N ^ (9 / 10 : ℝ) := by
    rw [show Real.log N = ell N by rfl, Real.rpow_two] at hboundN
    have hleftNorm : ‖ell N ^ 2‖ = ell N ^ 2 :=
      Real.norm_of_nonneg (pow_nonneg hellPos.le 2)
    have hrightNorm : ‖N ^ (9 / 10 : ℝ)‖ = N ^ (9 / 10 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hNPos.le _)
    calc
      ell N ^ 2 = ‖ell N ^ 2‖ := hleftNorm.symm
      _ ≤ (1 / 20002 : ℝ) * ‖N ^ (9 / 10 : ℝ)‖ := hboundN
      _ = (1 / 20002 : ℝ) * N ^ (9 / 10 : ℝ) := by rw [hrightNorm]
  calc
    ((2 * band N : ℕ) : ℝ) ≤ 20002 * ell N ^ 2 := hband
    _ ≤ 20002 * ((1 / 20002 : ℝ) * N ^ (9 / 10 : ℝ)) := by
      gcongr
    _ = N ^ (9 / 10 : ℝ) := by ring

end

end Erdos1212Kernel.CorridorScale
