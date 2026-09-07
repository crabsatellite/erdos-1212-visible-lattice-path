import Erdos1212Kernel.AlgebraicCorridorMediumMomentBounds
import Erdos1212Kernel.TaoThetaRootLogError
import Erdos1212Kernel.IwaniecRootLogDecay

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter Topology
open scoped BigOperators

theorem ell_div_L_tendsto :
    Tendsto (fun N : ℝ => ell N / L N) atTop atTop := by
  have hbase := (Real.tendsto_exp_div_pow_atTop 1).comp L_tendsto
  apply hbase.congr'
  filter_upwards [eventually_large_domain] with N hdom
  simp only [Function.comp_apply, pow_one,
    exp_L (zero_lt_one.trans_le hdom.2.1)]

theorem log_z_tendsto : Tendsto (fun N : ℝ => Real.log (z N)) atTop atTop := by
  have hscaled := ell_div_L_tendsto.const_mul_atTop
    (show (0 : ℝ) < 1 / 1000 by norm_num)
  apply hscaled.congr'
  filter_upwards [eventually_large_domain] with N hdom
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  rw [log_z (zero_lt_one.trans hdom.1) hu]
  unfold u
  field_simp [show L N ≠ 0 by exact (zero_lt_one.trans_le hdom.2.2).ne']

theorem z_tendsto : Tendsto z atTop atTop := by
  have hexp := Real.tendsto_exp_atTop.comp log_z_tendsto
  apply hexp.congr'
  filter_upwards [eventually_large_domain] with N hdom
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  simp only [Function.comp_apply]
  rw [Real.exp_log (z_pos (zero_lt_one.trans hdom.1) hu)]

theorem floor_z_tendsto : Tendsto (fun N : ℝ => ⌊z N⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp z_tendsto

theorem floor_two_z_tendsto :
    Tendsto (fun N : ℝ => ⌊2 * z N⌋₊) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (z_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

theorem smallPrimePool_eq_primesLE_floor
    {N : ℝ} (hz : 0 ≤ z N) :
    smallPrimePool N = Nat.primesLE ⌊z N⌋₊ := by
  ext p
  rw [mem_smallPrimePool, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hpz⟩
    exact ⟨Nat.le_floor hpz, hp⟩
  · rintro ⟨hpz, hp⟩
    exact ⟨hp, (show (p : ℝ) ≤ (⌊z N⌋₊ : ℝ) by exact_mod_cast hpz).trans
      (Nat.floor_le hz)⟩

theorem smallPrimePool_eulerProduct_eq_mertensProd
    {N : ℝ} (hz : 0 ≤ z N) :
    corridorEulerProduct (smallPrimePool N) =
      Erdos696.Mertens.mertensProd ⌊z N⌋₊ := by
  unfold corridorEulerProduct Erdos696.Mertens.mertensProd
  rw [smallPrimePool_eq_primesLE_floor hz]
  congr 1
  ext p
  simp [Nat.mem_primesLE, and_comm]

theorem smallPrimePool_mertens_tendsto :
    Tendsto (fun N : ℝ => corridorEulerProduct (smallPrimePool N) *
      Real.log (⌊z N⌋₊ : ℕ)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hcomp := Erdos696.Mertens.mertens_equation_15.comp floor_z_tendsto
  apply hcomp.congr'
  filter_upwards [eventually_large_domain] with N hdom
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  simp only [Function.comp_apply]
  rw [smallPrimePool_eulerProduct_eq_mertensProd
    (z_pos (zero_lt_one.trans hdom.1) hu).le]

def corridorMertensLowerConstant : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / 2

theorem corridorMertensLowerConstant_pos :
    0 < corridorMertensLowerConstant := by
  unfold corridorMertensLowerConstant
  positivity

theorem eventually_smallPrimePool_eulerProduct_lower :
    ∀ᶠ N : ℝ in atTop,
      corridorMertensLowerConstant / Real.log (z N) ≤
        corridorEulerProduct (smallPrimePool N) := by
  have hhalf : corridorMertensLowerConstant <
      Real.exp (-Real.eulerMascheroniConstant) := by
    unfold corridorMertensLowerConstant
    nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  have hmertens := smallPrimePool_mertens_tendsto.eventually
    (Ioi_mem_nhds hhalf)
  filter_upwards [hmertens, eventually_large_domain,
    z_tendsto.eventually_ge_atTop (3 : ℝ)] with N hm hdom hz3
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hzPos : 0 < z N := z_pos (zero_lt_one.trans hdom.1) hu
  have hfloorTwo : 2 ≤ ⌊z N⌋₊ := by
    apply (Nat.le_floor_iff hzPos.le).mpr
    norm_num
    linarith
  have hfloorPos : (0 : ℝ) < (⌊z N⌋₊ : ℕ) := by
    exact_mod_cast (show 0 < ⌊z N⌋₊ by omega)
  have hlogFloorLe : Real.log (⌊z N⌋₊ : ℕ) ≤ Real.log (z N) :=
    Real.log_le_log hfloorPos (Nat.floor_le hzPos.le)
  have hV := smallPrimePool_eulerProduct_nonneg N
  have hscaled : corridorMertensLowerConstant ≤
      corridorEulerProduct (smallPrimePool N) * Real.log (z N) := by
    calc
      corridorMertensLowerConstant ≤
          corridorEulerProduct (smallPrimePool N) *
            Real.log (⌊z N⌋₊ : ℕ) := hm.le
      _ ≤ corridorEulerProduct (smallPrimePool N) * Real.log (z N) :=
        mul_le_mul_of_nonneg_left hlogFloorLe hV
  have hlogzPos : 0 < Real.log (z N) := by
    rw [log_z (zero_lt_one.trans hdom.1) hu]
    exact div_pos (zero_lt_one.trans_le hdom.2.1) hu
  exact (div_le_iff₀ hlogzPos).mpr hscaled

theorem eventually_theta_error_le_quarter :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ x / 4 := by
  obtain ⟨a, A, X₀, ha, hA, hX₀, herr⟩ :=
    exists_taoTheta_root_log_error
  have hdecay := (tendsto_iwaniecRootLogDecay ha).const_mul A
  simp only [mul_zero] at hdecay
  filter_upwards [eventually_ge_atTop X₀,
    hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))]
      with x hx hsmall
  have hxNonneg : 0 ≤ x := hX₀.trans hx |>.trans' (by norm_num)
  have hraw := herr x hx
  have hscaled := mul_le_mul_of_nonneg_left hsmall.le hxNonneg
  unfold iwaniecRootLogDecay at hsmall hscaled
  calc
    |Chebyshev.theta x - x| ≤
        A * x * Real.exp (-a * Real.sqrt (Real.log x)) := hraw
    _ = x * (A * Real.exp (-a * Real.sqrt (Real.log x))) := by ring
    _ ≤ x * (1 / 4 : ℝ) := hscaled
    _ = x / 4 := by ring

theorem eventually_theta_error_le_tenth :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ x / 10 := by
  obtain ⟨a, A, X₀, ha, hA, hX₀, herr⟩ :=
    exists_taoTheta_root_log_error
  have hdecay := (tendsto_iwaniecRootLogDecay ha).const_mul A
  simp only [mul_zero] at hdecay
  filter_upwards [eventually_ge_atTop X₀,
    hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))]
      with x hx hsmall
  have hxNonneg : 0 ≤ x := by linarith [hX₀]
  have hraw := herr x hx
  have hscaled := mul_le_mul_of_nonneg_left hsmall.le hxNonneg
  unfold iwaniecRootLogDecay at hsmall hscaled
  calc
    |Chebyshev.theta x - x| ≤
        A * x * Real.exp (-a * Real.sqrt (Real.log x)) := hraw
    _ = x * (A * Real.exp (-a * Real.sqrt (Real.log x))) := by ring
    _ ≤ x * (1 / 10 : ℝ) := hscaled
    _ = x / 10 := by ring

theorem mediumPrimePool_eq_primesLE_sdiff
    {N : ℝ} (hz : 0 ≤ z N) :
    mediumPrimePool N =
      Nat.primesLE ⌊2 * z N⌋₊ \ Nat.primesLE ⌊z N⌋₊ := by
  ext q
  rw [mem_mediumPrimePool, Finset.mem_sdiff,
    Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨hq, hlow, hupp⟩
    refine ⟨⟨Nat.le_floor hupp, hq⟩, ?_⟩
    intro hsmall
    have hqz : (q : ℝ) ≤ z N :=
      (show (q : ℝ) ≤ (⌊z N⌋₊ : ℝ) by exact_mod_cast hsmall.1).trans
        (Nat.floor_le hz)
    linarith
  · rintro ⟨⟨hupp, hq⟩, hnotSmall⟩
    have huppR : (q : ℝ) ≤ 2 * z N :=
      (show (q : ℝ) ≤ (⌊2 * z N⌋₊ : ℝ) by exact_mod_cast hupp).trans
        (Nat.floor_le (by positivity))
    have hlow : z N < (q : ℝ) := by
      by_contra hnot
      have hqz : (q : ℝ) ≤ z N := le_of_not_gt hnot
      exact hnotSmall ⟨Nat.le_floor hqz, hq⟩
    exact ⟨hq, hlow, huppR⟩

def mediumPrimeLogMass (N : ℝ) : ℝ :=
  ∑ q ∈ mediumPrimePool N, Real.log q

theorem mediumPrimeLogMass_eq_theta_sub
    {N : ℝ} (hz : 0 ≤ z N) :
    mediumPrimeLogMass N =
      Chebyshev.theta (2 * z N) - Chebyshev.theta (z N) := by
  unfold mediumPrimeLogMass
  rw [mediumPrimePool_eq_primesLE_sdiff hz]
  have hsubset : Nat.primesLE ⌊z N⌋₊ ⊆
      Nat.primesLE ⌊2 * z N⌋₊ := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    refine ⟨?_, hp.2⟩
    apply Nat.le_floor
    calc
      (p : ℝ) ≤ (⌊z N⌋₊ : ℝ) := by exact_mod_cast hp.1
      _ ≤ z N := Nat.floor_le hz
      _ ≤ 2 * z N := by linarith
  rw [Finset.sum_sdiff_eq_sub hsubset,
    ← Chebyshev.theta_eq_sum_primesLE,
    ← Chebyshev.theta_eq_sum_primesLE]

theorem eventually_mediumPrimeLogMass_ge_quarter_z :
    ∀ᶠ N : ℝ in atTop, z N / 4 ≤ mediumPrimeLogMass N := by
  have hzErr := z_tendsto.eventually eventually_theta_error_le_quarter
  have htwoZ := z_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have htwoErr := htwoZ.eventually eventually_theta_error_le_quarter
  filter_upwards [eventually_large_domain, hzErr, htwoErr] with N hdom hzE htwoE
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hzPos : 0 < z N := z_pos (zero_lt_one.trans hdom.1) hu
  rw [abs_le] at hzE htwoE
  rw [mediumPrimeLogMass_eq_theta_sub hzPos.le]
  linarith

theorem eventually_mediumPrimeLogMass_ge_half_z :
    ∀ᶠ N : ℝ in atTop, z N / 2 ≤ mediumPrimeLogMass N := by
  have hzErr := z_tendsto.eventually eventually_theta_error_le_tenth
  have htwoZ := z_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have htwoErr := htwoZ.eventually eventually_theta_error_le_tenth
  filter_upwards [eventually_large_domain, hzErr, htwoErr] with N hdom hzE htwoE
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hzPos : 0 < z N := z_pos (zero_lt_one.trans hdom.1) hu
  rw [abs_le] at hzE htwoE
  rw [mediumPrimeLogMass_eq_theta_sub hzPos.le]
  linarith

theorem mediumPrimeLogMass_le_card_mul_log_two_z
    {N : ℝ} (hz : 0 < z N) :
    mediumPrimeLogMass N ≤
      ((mediumPrimePool N).card : ℝ) * Real.log (2 * z N) := by
  unfold mediumPrimeLogMass
  calc
    (∑ q ∈ mediumPrimePool N, Real.log q) ≤
        ∑ _q ∈ mediumPrimePool N, Real.log (2 * z N) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : (0 : ℝ) < q := by
        exact_mod_cast (prime_of_mem_mediumPrimePool hq).pos
      exact Real.log_le_log hqPos (mem_mediumPrimePool.mp hq).2.2
    _ = ((mediumPrimePool N).card : ℝ) * Real.log (2 * z N) := by
      simp

theorem mediumPrime_card_div_two_z_le_reciprocalMass
    {N : ℝ} (hz : 0 < z N) :
    ((mediumPrimePool N).card : ℝ) / (2 * z N) ≤
      mediumPrimeReciprocalMass N := by
  unfold mediumPrimeReciprocalMass
  rw [show ((mediumPrimePool N).card : ℝ) / (2 * z N) =
      ∑ _q ∈ mediumPrimePool N, (1 / (2 * z N) : ℝ) by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring]
  apply Finset.sum_le_sum
  intro q hq
  rw [← one_div]
  exact one_div_le_one_div_of_le
    (show (0 : ℝ) < q by exact_mod_cast (prime_of_mem_mediumPrimePool hq).pos)
    (mem_mediumPrimePool.mp hq).2.2

theorem mediumPrimeReciprocalMass_le_card_div_z
    {N : ℝ} (hz : 0 < z N) :
    mediumPrimeReciprocalMass N ≤
      ((mediumPrimePool N).card : ℝ) / z N := by
  unfold mediumPrimeReciprocalMass
  rw [show ((mediumPrimePool N).card : ℝ) / z N =
      ∑ _q ∈ mediumPrimePool N, (1 / z N : ℝ) by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring]
  apply Finset.sum_le_sum
  intro q hq
  rw [← one_div]
  exact one_div_le_one_div_of_le hz (mem_mediumPrimePool.mp hq).2.1.le

theorem card_mul_log_z_le_mediumPrimeLogMass
    {N : ℝ} (hz : 0 < z N) :
    ((mediumPrimePool N).card : ℝ) * Real.log (z N) ≤
      mediumPrimeLogMass N := by
  unfold mediumPrimeLogMass
  rw [show ((mediumPrimePool N).card : ℝ) * Real.log (z N) =
      ∑ _q ∈ mediumPrimePool N, Real.log (z N) by simp]
  apply Finset.sum_le_sum
  intro q hq
  exact Real.log_le_log hz (mem_mediumPrimePool.mp hq).2.1.le

theorem eventually_mediumPrimeReciprocalMass_upper :
    ∀ᶠ N : ℝ in atTop,
      mediumPrimeReciprocalMass N ≤ 3 / Real.log (z N) := by
  have htwoZ := z_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have htwoErr := htwoZ.eventually eventually_theta_error_le_quarter
  filter_upwards [eventually_large_domain, htwoErr,
    z_tendsto.eventually_ge_atTop (3 : ℝ)] with N hdom htheta hz3
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hzPos : 0 < z N := z_pos (zero_lt_one.trans hdom.1) hu
  have hlogzPos : 0 < Real.log (z N) := Real.log_pos (by linarith)
  have hmassCard := mediumPrimeReciprocalMass_le_card_div_z hzPos
  have hcardLog := card_mul_log_z_le_mediumPrimeLogMass hzPos
  have hlogTheta := mediumPrimeLogMass_eq_theta_sub hzPos.le
  have hthetaZNonneg := Chebyshev.theta_nonneg (z N)
  rw [abs_le] at htheta
  have hlogMassUpper : mediumPrimeLogMass N ≤ 3 * z N := by
    rw [hlogTheta]
    nlinarith
  have hcard : ((mediumPrimePool N).card : ℝ) ≤
      3 * z N / Real.log (z N) := by
    apply (le_div_iff₀ hlogzPos).mpr
    nlinarith
  have hzNonneg := hzPos.le
  calc
    mediumPrimeReciprocalMass N ≤
        ((mediumPrimePool N).card : ℝ) / z N := hmassCard
    _ ≤ (3 * z N / Real.log (z N)) / z N := by
      exact div_le_div_of_nonneg_right hcard hzNonneg
    _ = 3 / Real.log (z N) := by field_simp

theorem eventually_mediumPrimeReciprocalMass_le_quarter :
    ∀ᶠ N : ℝ in atTop,
      mediumPrimeReciprocalMass N ≤ 1 / 4 := by
  filter_upwards [eventually_mediumPrimeReciprocalMass_upper,
    log_z_tendsto.eventually_ge_atTop (12 : ℝ)] with N hmass hlog
  have hlogPos : 0 < Real.log (z N) := by linarith
  calc
    mediumPrimeReciprocalMass N ≤ 3 / Real.log (z N) := hmass
    _ ≤ 1 / 4 := (div_le_iff₀ hlogPos).mpr (by nlinarith)

theorem eventually_mediumPrimeReciprocalMass_lower :
    ∀ᶠ N : ℝ in atTop,
      (1 : ℝ) / (8 * Real.log (z N)) ≤ mediumPrimeReciprocalMass N := by
  filter_upwards [eventually_large_domain,
    eventually_mediumPrimeLogMass_ge_half_z,
    z_tendsto.eventually_ge_atTop (3 : ℝ)] with N hdom hlogMass hz3
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hzPos : 0 < z N := z_pos (zero_lt_one.trans hdom.1) hu
  have hlogzPos : 0 < Real.log (z N) := Real.log_pos (by linarith)
  have hlogTwoZPos : 0 < Real.log (2 * z N) :=
    Real.log_pos (by nlinarith)
  have hcardLog := mediumPrimeLogMass_le_card_mul_log_two_z hzPos
  have hcard : z N / (2 * Real.log (2 * z N)) ≤
      ((mediumPrimePool N).card : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hmass := mediumPrime_card_div_two_z_le_reciprocalMass hzPos
  have hbase : (1 : ℝ) / (4 * Real.log (2 * z N)) ≤
      mediumPrimeReciprocalMass N := by
    calc
      (1 : ℝ) / (4 * Real.log (2 * z N)) =
          (z N / (2 * Real.log (2 * z N))) / (2 * z N) := by
        field_simp
        ring
      _ ≤ ((mediumPrimePool N).card : ℝ) / (2 * z N) := by
        exact div_le_div_of_nonneg_right hcard (by positivity)
      _ ≤ mediumPrimeReciprocalMass N := hmass
  have hlogTwoZ : Real.log (2 * z N) ≤ 2 * Real.log (z N) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzPos.ne']
    have hlogTwoLe := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ z N)
    linarith
  have hden : 4 * Real.log (2 * z N) ≤ 8 * Real.log (z N) := by
    nlinarith
  exact (one_div_le_one_div_of_le (by positivity) hden).trans hbase

theorem one_quarter_lt_corridorMertensLowerConstant :
    (1 / 4 : ℝ) < corridorMertensLowerConstant := by
  have hgamma : Real.eulerMascheroniConstant < Real.log 2 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans (by
      have hlog := Real.log_two_gt_d9
      norm_num at hlog ⊢
      linarith)
  have hexp := Real.exp_lt_exp.mpr (neg_lt_neg hgamma)
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  unfold corridorMertensLowerConstant
  norm_num at hexp ⊢
  linarith

def corridorRoughDensityConstant : ℝ := 1 / 50

theorem corridorRoughDensityConstant_pos :
    0 < corridorRoughDensityConstant := by
  unfold corridorRoughDensityConstant
  norm_num

theorem eventually_bonferroni_coefficient_error_small :
    ∀ᶠ N : ℝ in atTop,
      2 * (ell N)⁻¹ ^ 200 ≤
        (1 : ℝ) / (400 * Real.log (z N) ^ 2) := by
  have hinv : Tendsto (fun N : ℝ => (ell N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ell_tendsto
  have hpow : Tendsto (fun N : ℝ => (ell N)⁻¹ ^ 198) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (198 : ℕ) ≠ 0)] using hinv.pow 198
  have hmargin : (0 : ℝ) < 1 / 800 := by norm_num
  filter_upwards [eventually_large_domain,
    hpow.eventually (Iio_mem_nhds hmargin)] with N hdom hsmall
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have huOne : 1 ≤ u N := by unfold u; nlinarith [hdom.2.2]
  have hlogz : Real.log (z N) = ell N / u N :=
    log_z (zero_lt_one.trans hdom.1) hu
  have hlogzPos : 0 < Real.log (z N) := by rw [hlogz]; positivity
  have hlogzLe : Real.log (z N) ≤ ell N := by
    rw [hlogz]
    exact (div_le_iff₀ hu).mpr (by nlinarith)
  have hlogSq := pow_le_pow_left₀ hlogzPos.le hlogzLe 2
  have heps : 0 ≤ (ell N)⁻¹ ^ 200 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hlogSq heps
  have hid : (ell N)⁻¹ ^ 200 * ell N ^ 2 = (ell N)⁻¹ ^ 198 := by
    field_simp
  have hscaledSmall :
      2 * ((ell N)⁻¹ ^ 200 * Real.log (z N) ^ 2) ≤
        (1 : ℝ) / 400 := by
    rw [show (1 : ℝ) / 400 = 2 * ((1 : ℝ) / 800) by ring]
    gcongr
    calc
      (ell N)⁻¹ ^ 200 * Real.log (z N) ^ 2 ≤
          (ell N)⁻¹ ^ 200 * ell N ^ 2 := hprod
      _ = (ell N)⁻¹ ^ 198 := hid
      _ ≤ (1 : ℝ) / 800 := hsmall.le
  calc
    2 * (ell N)⁻¹ ^ 200 ≤
        ((1 : ℝ) / 400) / Real.log (z N) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hlogzPos)).mpr (by
        nlinarith [hscaledSmall])
    _ = (1 : ℝ) / (400 * Real.log (z N) ^ 2) := by ring

theorem eventually_corridorRoughDensity_lower :
    ∀ᶠ N : ℝ in atTop,
      corridorRoughDensityConstant / Real.log (z N) ^ 2 ≤
        (corridorEulerProduct (smallPrimePool N) - (ell N)⁻¹ ^ 200) *
            mediumPrimeReciprocalMass N -
          (corridorEulerProduct (smallPrimePool N) + (ell N)⁻¹ ^ 200) *
            (mediumPrimeReciprocalMass N ^ 2 / 2) := by
  filter_upwards [eventually_large_domain,
    eventually_smallPrimePool_eulerProduct_lower,
    eventually_mediumPrimeReciprocalMass_lower,
    eventually_mediumPrimeReciprocalMass_le_quarter,
    eventually_bonferroni_coefficient_error_small] with
      N hdom hVLower hSLower hSUpper hepsSmall
  let V := corridorEulerProduct (smallPrimePool N)
  let eps := (ell N)⁻¹ ^ 200
  let S := mediumPrimeReciprocalMass N
  let logz := Real.log (z N)
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hlogzPos : 0 < logz := by
    dsimp [logz]
    rw [log_z (zero_lt_one.trans hdom.1) hu]
    exact div_pos (zero_lt_one.trans_le hdom.2.1) hu
  have hV : 0 ≤ V := by
    dsimp [V]
    exact smallPrimePool_eulerProduct_nonneg N
  have hS : 0 ≤ S := by
    dsimp [S, mediumPrimeReciprocalMass]
    positivity
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hVQuarter : (1 : ℝ) / (4 * logz) ≤ V := by
    have hc : (1 / 4 : ℝ) ≤ corridorMertensLowerConstant :=
      one_quarter_lt_corridorMertensLowerConstant.le
    have hdiv := div_le_div_of_nonneg_right hc hlogzPos.le
    calc
      (1 : ℝ) / (4 * logz) = ((1 : ℝ) / 4) / logz := by ring
      _ ≤ corridorMertensLowerConstant / logz := hdiv
      _ ≤ V := hVLower
  have hVS : (1 : ℝ) / (32 * logz ^ 2) ≤ V * S := by
    have hmul := mul_le_mul hVQuarter hSLower
      (by positivity : 0 ≤ (1 : ℝ) / (8 * logz))
      (by positivity : 0 ≤ V)
    dsimp [logz, V, S] at hmul ⊢
    convert hmul using 1 <;> field_simp <;> ring
  have hSsq : S ^ 2 ≤ S / 4 := by
    change S ≤ 1 / 4 at hSUpper
    nlinarith [mul_le_mul_of_nonneg_left hSUpper hS]
  have hVmain : 3 * (V * S) / 4 ≤ V * (S - S ^ 2 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hSsq hV]
  have hepsMain : eps * (S + S ^ 2 / 2) ≤ 2 * eps := by
    have hSOne : S ≤ 1 := by
      change S ≤ 1 / 4 at hSUpper
      linarith
    have hSsqOne : S ^ 2 ≤ 1 := by nlinarith [sq_nonneg (S - 1)]
    nlinarith [mul_le_mul_of_nonneg_left
      (show S + S ^ 2 / 2 ≤ 2 by nlinarith) heps]
  have hepsSmall' : 2 * eps ≤ (1 : ℝ) / (400 * logz ^ 2) := by
    convert hepsSmall using 1 <;>
      dsimp [eps, logz] <;> ring
  change ((1 : ℝ) / 50) / logz ^ 2 ≤
    (V - eps) * S - (V + eps) * (S ^ 2 / 2)
  have hVSmain : (3 : ℝ) / (128 * logz ^ 2) ≤ 3 * (V * S) / 4 := by
    calc
      (3 : ℝ) / (128 * logz ^ 2) =
          3 * ((1 : ℝ) / (32 * logz ^ 2)) / 4 := by ring
      _ ≤ 3 * (V * S) / 4 := by nlinarith
  calc
    ((1 : ℝ) / 50) / logz ^ 2 ≤
        (3 : ℝ) / (128 * logz ^ 2) -
          (1 : ℝ) / (400 * logz ^ 2) := by
      field_simp
      norm_num
    _ ≤ 3 * (V * S) / 4 - 2 * eps := sub_le_sub hVSmain hepsSmall'
    _ ≤ V * (S - S ^ 2 / 2) - eps * (S + S ^ 2 / 2) :=
      sub_le_sub hVmain hepsMain
    _ = (V - eps) * S - (V + eps) * (S ^ 2 / 2) := by ring

end

end Erdos1212Kernel.CorridorScale
