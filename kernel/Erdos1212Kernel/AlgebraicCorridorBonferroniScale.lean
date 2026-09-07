import Erdos1212Kernel.AlgebraicCorridorBonferroniTail
import Erdos1212Kernel.AlgebraicCorridorScales
import Erdos1212Kernel.IwaniecPaperACoarsePrimeTail
import Erdos1212Kernel.IwaniecPaperAStirlingTail

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def smallPrimePool (N : ℝ) : Finset ℕ :=
  (iwaniecStrictPrimePool (z N + 1)).filter fun p => (p : ℝ) ≤ z N

def bonferroniRank (N : ℝ) : ℕ :=
  Nat.ceil (50 * L N) + 1

@[simp]
theorem mem_smallPrimePool {N : ℝ} {p : ℕ} :
    p ∈ smallPrimePool N ↔ p.Prime ∧ (p : ℝ) ≤ z N := by
  simp only [smallPrimePool, Finset.mem_filter, mem_iwaniecStrictPrimePool]
  constructor
  · rintro ⟨⟨hp, _⟩, hpz⟩
    exact ⟨hp, hpz⟩
  · rintro ⟨hp, hpz⟩
    exact ⟨⟨hp, lt_of_le_of_lt hpz (lt_add_one _)⟩, hpz⟩

theorem smallPrimePool_reciprocalMass_le (N : ℝ) :
    corridorPrimeReciprocalMass (smallPrimePool N) ≤
      iwaniecStrictPrimeReciprocalSum (z N + 1) := by
  unfold corridorPrimeReciprocalMass iwaniecStrictPrimeReciprocalSum smallPrimePool
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => by positivity)

theorem eventually_z_add_one_le_self :
    ∀ᶠ N : ℝ in atTop, z N + 1 ≤ N := by
  filter_upwards [eventually_large_domain, eventually_ge_atTop (4 : ℝ)] with N hdom hN4
  have hN : 1 ≤ N := hdom.1.le
  have hL : 1 ≤ L N := hdom.2.2
  have hu : 0 < u N := by unfold u; positivity
  have hexponent : 1 / u N ≤ (1 / 2 : ℝ) := by
    unfold u
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * L N)]
    nlinarith
  have hzsqrt : z N ≤ Real.sqrt N := by
    unfold z
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN hexponent
  have hsqrt : Real.sqrt N ≤ N / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  linarith

theorem eventually_smallPrimePool_reciprocalMass_le_three_L :
    ∀ᶠ N : ℝ in atTop,
      corridorPrimeReciprocalMass (smallPrimePool N) ≤ 3 * L N := by
  filter_upwards [eventually_iwaniecStrictPrimeReciprocalSum_le_three_loglog,
    eventually_z_add_one_le_self] with N hM hz
  exact (smallPrimePool_reciprocalMass_le N).trans (hM (z N + 1) hz)

theorem eventually_bonferroni_tail_threshold :
    ∀ᶠ N : ℝ in atTop,
      2 * corridorPrimeReciprocalMass (smallPrimePool N) ≤
        (2 * bonferroniRank N + 1 : ℕ) := by
  filter_upwards [eventually_large_domain,
    eventually_smallPrimePool_reciprocalMass_le_three_L] with N hdom hmass
  have hceil : 50 * L N ≤ (Nat.ceil (50 * L N) : ℝ) := Nat.le_ceil _
  unfold bonferroniRank
  push_cast
  nlinarith

theorem eventually_smallPrimePool_tail_le_twice_first :
    ∀ᶠ N : ℝ in atTop,
      corridorPowersetTailMass (smallPrimePool N) (2 * bonferroniRank N) ≤
        2 * iwaniecFactorialTerm
          (corridorPrimeReciprocalMass (smallPrimePool N))
          (2 * bonferroniRank N) := by
  filter_upwards [eventually_bonferroni_tail_threshold] with N hthreshold
  exact corridorPowersetTailMass_le_twice_first
    (smallPrimePool N) (2 * bonferroniRank N) hthreshold

theorem eventually_two_tenth_pow_cutoff_le_ell_inv_pow :
    ∀ᶠ N : ℝ in atTop,
      2 * (1 / 10 : ℝ) ^ (2 * bonferroniRank N) ≤
        (ell N)⁻¹ ^ 200 := by
  let delta : ℝ := -Real.log (1 / 10 : ℝ) - 2
  have hexpTwo : Real.exp 2 < 10 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have hpos : 0 < (3 - Real.exp 1) * (3 + Real.exp 1) := by
      apply mul_pos
      · exact sub_pos.mpr Real.exp_one_lt_three
      · linarith [Real.exp_pos 1]
    nlinarith
  have hlogTen : 2 < Real.log 10 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 hexpTwo
  have hlogTenth : Real.log (1 / 10 : ℝ) = -Real.log 10 := by
    rw [show (1 / 10 : ℝ) = (10 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hdelta : 0 < delta := by
    dsimp [delta]
    rw [hlogTenth]
    linarith
  have hlarge := L_tendsto.eventually_ge_atTop
    (Real.log 2 / (100 * delta))
  filter_upwards [eventually_large_domain, hlarge] with N hdom hLlarge
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hcutoff : 100 * L N ≤ (2 * bonferroniRank N : ℕ) := by
    have hceil : 50 * L N ≤ (Nat.ceil (50 * L N) : ℝ) := Nat.le_ceil _
    unfold bonferroniRank
    push_cast
    linarith
  have habsorb : Real.log 2 ≤ 100 * delta * L N := by
    have hden : 0 < 100 * delta := by positivity
    have hscaled := (div_le_iff₀ hden).mp hLlarge
    nlinarith
  have hlogTenthNeg : Real.log (1 / 10 : ℝ) = -(2 + delta) := by
    dsimp [delta]
    ring
  have hexponent : Real.log 2 +
      (2 * bonferroniRank N : ℕ) * Real.log (1 / 10 : ℝ) ≤
        -200 * L N := by
    rw [hlogTenthNeg]
    have hscaled := mul_le_mul_of_nonneg_right hcutoff
      (by positivity : (0 : ℝ) ≤ 2 + delta)
    push_cast at hscaled
    nlinarith
  have hleft : 2 * (1 / 10 : ℝ) ^ (2 * bonferroniRank N) =
      Real.exp (Real.log 2 +
        (2 * bonferroniRank N : ℕ) * Real.log (1 / 10 : ℝ)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 10)]
  have hright : (ell N)⁻¹ ^ 200 = Real.exp (-200 * L N) := by
    calc
      (ell N)⁻¹ ^ 200 = Real.exp (-L N) ^ 200 := by
        rw [Real.exp_neg, exp_L hellPos]
      _ = Real.exp ((200 : ℝ) * (-L N)) :=
        (Real.exp_nat_mul (-L N) 200).symm
      _ = Real.exp (-200 * L N) := by congr 1; ring
  rw [hleft, hright]
  exact Real.exp_le_exp.mpr hexponent

theorem eventually_smallPrimePool_tail_le_ell_inv_pow :
    ∀ᶠ N : ℝ in atTop,
      corridorPowersetTailMass (smallPrimePool N) (2 * bonferroniRank N) ≤
        (ell N)⁻¹ ^ 200 := by
  filter_upwards [eventually_large_domain,
    eventually_smallPrimePool_reciprocalMass_le_three_L,
    eventually_smallPrimePool_tail_le_twice_first,
    eventually_two_tenth_pow_cutoff_le_ell_inv_pow] with N hdom hmass htail hpower
  let M := corridorPrimeReciprocalMass (smallPrimePool N)
  let K := 2 * bonferroniRank N
  have hM : 0 ≤ M := by
    dsimp [M, corridorPrimeReciprocalMass]
    positivity
  have hK : 0 < K := by dsimp [K, bonferroniRank]; omega
  have hceil : 50 * L N ≤ (Nat.ceil (50 * L N) : ℝ) := Nat.le_ceil _
  have hKlower : 100 * L N ≤ (K : ℝ) := by
    dsimp [K, bonferroniRank]
    push_cast
    linarith
  have heM : Real.exp 1 * M ≤ 9 * L N := by
    have hscaled := mul_le_mul_of_nonneg_left hmass (Real.exp_pos 1).le
    have he := Real.exp_one_lt_three.le
    nlinarith
  have hbase : Real.exp 1 * M / (K : ℝ) ≤ (1 / 10 : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast hK)).2
    nlinarith
  have hstirling := iwaniecFactorialTerm_le_stirling_power hM K hK
  have hbaseNonneg : 0 ≤ Real.exp 1 * M / (K : ℝ) := by positivity
  have hfirst : iwaniecFactorialTerm M K ≤ (1 / 10 : ℝ) ^ K :=
    hstirling.trans (pow_le_pow_left₀ hbaseNonneg hbase K)
  have htwice := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)
  exact htail.trans (htwice.trans hpower)

end

end Erdos1212Kernel.CorridorScale
