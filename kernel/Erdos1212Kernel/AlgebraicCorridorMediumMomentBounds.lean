import Erdos1212Kernel.AlgebraicCorridorMediumBonferroni

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open scoped BigOperators

def mediumPrimeReciprocalMass (N : ℝ) : ℝ :=
  ∑ q ∈ mediumPrimePool N, (q : ℝ)⁻¹

def mediumPrimePairReciprocalMass (N : ℝ) : ℝ :=
  ∑ pair ∈ (mediumPrimePool N).powersetCard 2,
    (((∏ q ∈ pair, q) : ℕ) : ℝ)⁻¹

theorem mediumPrimePairReciprocalMass_eq_elementary (N : ℝ) :
    mediumPrimePairReciprocalMass N =
      corridorElementaryMass (mediumPrimePool N) 2 := by
  unfold mediumPrimePairReciprocalMass corridorElementaryMass
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [one_div]

theorem mediumPrimePairReciprocalMass_le_half_square (N : ℝ) :
    mediumPrimePairReciprocalMass N ≤
      mediumPrimeReciprocalMass N ^ 2 / 2 := by
  rw [mediumPrimePairReciprocalMass_eq_elementary]
  have h := corridorElementaryMass_le_factorialTerm (mediumPrimePool N) 2
  simpa [mediumPrimeReciprocalMass, corridorPrimeReciprocalMass] using h

theorem smallPrimePool_all_prime (N : ℝ) :
    ∀ p ∈ smallPrimePool N, p.Prime := by
  intro p hp
  exact (mem_smallPrimePool.mp hp).1

theorem mediumPrimePool_all_prime (N : ℝ) :
    ∀ q ∈ mediumPrimePool N, q.Prime := by
  intro q hq
  exact prime_of_mem_mediumPrimePool hq

theorem corridorMediumFirstMoment_lower
    {N : ℝ} {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    (T : ℝ) * corridorTruncatedEulerMain
          (smallPrimePool N) (bonferroniRank N) *
          mediumPrimeReciprocalMass N -
        ((mediumPrimePool N).card : ℝ) *
          ((rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) ≤
      (corridorMediumFirstMoment (smallPrimePool N)
        (mediumPrimePool N) lower T : ℝ) := by
  classical
  have hterm : ∀ q ∈ mediumPrimePool N,
      (T : ℝ) / q * corridorTruncatedEulerMain
            (smallPrimePool N) (bonferroniRank N) -
          (rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card ≤
        corridorAh (smallPrimePool N) q lower T := by
    intro q hq
    exact corridorAh_lower_bound (smallPrimePool N)
      (smallPrimePool_all_prime N)
      (mediumPrime_coprime_smallPool hq)
      (bonferroniRank N) (prime_of_mem_mediumPrimePool hq).pos
      hlower T
  calc
    (T : ℝ) * corridorTruncatedEulerMain
          (smallPrimePool N) (bonferroniRank N) *
          mediumPrimeReciprocalMass N -
        ((mediumPrimePool N).card : ℝ) *
          ((rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) =
      ∑ q ∈ mediumPrimePool N,
        ((T : ℝ) / q * corridorTruncatedEulerMain
            (smallPrimePool N) (bonferroniRank N) -
          (rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card) := by
      unfold mediumPrimeReciprocalMass
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro q hq
        rw [div_eq_mul_inv]
        ring
      · ring
    _ ≤ ∑ q ∈ mediumPrimePool N,
        (corridorAh (smallPrimePool N) q lower T : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = (corridorMediumFirstMoment (smallPrimePool N)
          (mediumPrimePool N) lower T : ℝ) := by
      unfold corridorMediumFirstMoment
      push_cast
      rfl

theorem corridorMediumSecondMoment_upper
    {N : ℝ} {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    (corridorMediumSecondMoment (smallPrimePool N)
        (mediumPrimePool N) lower T : ℝ) ≤
      (T : ℝ) * corridorEvenTruncatedEulerMain
          (smallPrimePool N) (bonferroniRank N) *
          mediumPrimePairReciprocalMass N +
        (((mediumPrimePool N).powersetCard 2).card : ℝ) *
          ((corridorEvenTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) := by
  classical
  have hterm : ∀ pair ∈ (mediumPrimePool N).powersetCard 2,
      (corridorAh (smallPrimePool N) (∏ q ∈ pair, q) lower T : ℝ) ≤
        (T : ℝ) / (∏ q ∈ pair, q) *
            corridorEvenTruncatedEulerMain
              (smallPrimePool N) (bonferroniRank N) +
          (corridorEvenTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card := by
    intro pair hpair
    have hsubset : pair ⊆ mediumPrimePool N :=
      (Finset.mem_powersetCard.mp hpair).1
    have hprodPos : 0 < ∏ q ∈ pair, q :=
      Finset.prod_pos fun q hq =>
        (prime_of_mem_mediumPrimePool (hsubset hq)).pos
    exact corridorAh_upper_bound (smallPrimePool N)
      (smallPrimePool_all_prime N)
      (mediumPrimeSubsetProduct_coprime_smallPool hsubset)
      (bonferroniRank N) hprodPos hlower T
  calc
    (corridorMediumSecondMoment (smallPrimePool N)
        (mediumPrimePool N) lower T : ℝ) =
      ∑ pair ∈ (mediumPrimePool N).powersetCard 2,
        (corridorAh (smallPrimePool N) (∏ q ∈ pair, q) lower T : ℝ) := by
      unfold corridorMediumSecondMoment
      push_cast
      rfl
    _ ≤ ∑ pair ∈ (mediumPrimePool N).powersetCard 2,
        ((T : ℝ) / (∏ q ∈ pair, q) *
            corridorEvenTruncatedEulerMain
              (smallPrimePool N) (bonferroniRank N) +
          (corridorEvenTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact hterm pair hpair
    _ = (T : ℝ) * corridorEvenTruncatedEulerMain
          (smallPrimePool N) (bonferroniRank N) *
          mediumPrimePairReciprocalMass N +
        (((mediumPrimePool N).powersetCard 2).card : ℝ) *
          ((corridorEvenTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) := by
      unfold mediumPrimePairReciprocalMass
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro pair hpair
        push_cast
        rw [div_eq_mul_inv]
        ring
      · ring

/-- The finite quantitative core of the paper's rough-composite lemma after
substituting the `A_q` lower bounds and `A_{qq'}` upper bounds. -/
theorem corridorMediumCandidates_finite_lower
    {N : ℝ} {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    (T : ℝ) * corridorTruncatedEulerMain
          (smallPrimePool N) (bonferroniRank N) *
          mediumPrimeReciprocalMass N -
        ((mediumPrimePool N).card : ℝ) *
          ((rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) -
        ((T : ℝ) * corridorEvenTruncatedEulerMain
            (smallPrimePool N) (bonferroniRank N) *
            mediumPrimePairReciprocalMass N +
          (((mediumPrimePool N).powersetCard 2).card : ℝ) *
            ((corridorEvenTruncatedSubsets
              (smallPrimePool N) (bonferroniRank N)).card : ℝ)) ≤
      ((corridorMediumWitnessCandidates (smallPrimePool N)
        (mediumPrimePool N) lower T).card : ℝ) := by
  have hfirst := corridorMediumFirstMoment_lower (N := N) hlower T
  have hsecond := corridorMediumSecondMoment_upper (N := N) hlower T
  have hbonf :
      (corridorMediumFirstMoment (smallPrimePool N)
          (mediumPrimePool N) lower T : ℝ) -
        (corridorMediumSecondMoment (smallPrimePool N)
          (mediumPrimePool N) lower T : ℝ) ≤
        ((corridorMediumWitnessCandidates (smallPrimePool N)
          (mediumPrimePool N) lower T).card : ℝ) := by
    exact_mod_cast corridorMedium_two_term_bonferroni
      (smallPrimePool N) (mediumPrimePool N)
      (mediumPrimePool_all_prime N) lower T
  linarith

theorem smallPrimePool_eulerProduct_nonneg (N : ℝ) :
    0 ≤ corridorEulerProduct (smallPrimePool N) := by
  unfold corridorEulerProduct
  apply Finset.prod_nonneg
  intro p hp
  simpa [one_div] using (Erdos696.Mertens.one_sub_inv_prime_pos p
    (smallPrimePool_all_prime N p hp)).le

/-- The growing Bonferroni error is now inserted into the finite medium-prime
count.  This is the paper's main expression `TV(S-S²/2)`, with the two
coefficient errors retained explicitly and with all finite divisor-term
remainders still visible. -/
theorem eventually_corridorMediumCandidates_main_lower :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ (lower T : ℕ), 0 < lower →
      (T : ℝ) *
          (corridorEulerProduct (smallPrimePool N) - (ell N)⁻¹ ^ 200) *
          mediumPrimeReciprocalMass N -
        ((mediumPrimePool N).card : ℝ) *
          ((rosserTruncatedSubsets
            (smallPrimePool N) (bonferroniRank N)).card : ℝ) -
        ((T : ℝ) *
            (corridorEulerProduct (smallPrimePool N) + (ell N)⁻¹ ^ 200) *
            (mediumPrimeReciprocalMass N ^ 2 / 2) +
          (((mediumPrimePool N).powersetCard 2).card : ℝ) *
            ((corridorEvenTruncatedSubsets
              (smallPrimePool N) (bonferroniRank N)).card : ℝ)) ≤
      ((corridorMediumWitnessCandidates (smallPrimePool N)
        (mediumPrimePool N) lower T).card : ℝ) := by
  filter_upwards [eventually_large_domain,
    eventually_smallPrimePool_tail_le_ell_inv_pow] with N hdom htail
  intro lower T hlower
  let V := corridorEulerProduct (smallPrimePool N)
  let eps := (ell N)⁻¹ ^ 200
  let S := mediumPrimeReciprocalMass N
  let P := mediumPrimePairReciprocalMass N
  let oddMain := corridorTruncatedEulerMain
    (smallPrimePool N) (bonferroniRank N)
  let evenMain := corridorEvenTruncatedEulerMain
    (smallPrimePool N) (bonferroniRank N)
  have hoddErr := corridor_truncatedEulerMain_error_le_tailMass
    (smallPrimePool N) (smallPrimePool_all_prime N) (bonferroniRank N)
  have hevenErr := corridor_evenTruncatedEulerMain_error_le_tailMass
    (smallPrimePool N) (smallPrimePool_all_prime N) (bonferroniRank N)
  have hevenTail :
      corridorPowersetTailMass (smallPrimePool N)
          (2 * bonferroniRank N + 1) ≤ (ell N)⁻¹ ^ 200 :=
    (corridorPowersetTailMass_antitone (smallPrimePool N)
      (Nat.le_succ (2 * bonferroniRank N))).trans htail
  rw [abs_le] at hoddErr hevenErr
  have hodd : V - eps ≤ oddMain := by
    dsimp [V, eps, oddMain]
    linarith
  have heven : evenMain ≤ V + eps := by
    dsimp [V, eps, evenMain]
    linarith
  have hS : 0 ≤ S := by
    dsimp [S, mediumPrimeReciprocalMass]
    positivity
  have hP : 0 ≤ P := by
    dsimp [P, mediumPrimePairReciprocalMass]
    positivity
  have heps : 0 ≤ eps := by
    dsimp [eps]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    exact smallPrimePool_eulerProduct_nonneg N
  have hpair : P ≤ S ^ 2 / 2 := by
    dsimp [P, S]
    exact mediumPrimePairReciprocalMass_le_half_square N
  have hfirstMain : (T : ℝ) * (V - eps) * S ≤
      (T : ℝ) * oddMain * S := by
    have hcoef : 0 ≤ (T : ℝ) * S := mul_nonneg (Nat.cast_nonneg T) hS
    nlinarith [mul_le_mul_of_nonneg_left hodd hcoef]
  have hsecondMain : (T : ℝ) * evenMain * P ≤
      (T : ℝ) * (V + eps) * (S ^ 2 / 2) := by
    have hcoef₁ : 0 ≤ (T : ℝ) * P := mul_nonneg (Nat.cast_nonneg T) hP
    have hstep₁ := mul_le_mul_of_nonneg_left heven hcoef₁
    have hcoef₂ : 0 ≤ (T : ℝ) * (V + eps) :=
      mul_nonneg (Nat.cast_nonneg T) (add_nonneg hV heps)
    have hstep₂ := mul_le_mul_of_nonneg_left hpair hcoef₂
    nlinarith
  have hfinite := corridorMediumCandidates_finite_lower
    (N := N) hlower T
  dsimp [V, eps, S, P, oddMain, evenMain] at hfirstMain hsecondMain
  linarith

end

end Erdos1212Kernel.CorridorScale
