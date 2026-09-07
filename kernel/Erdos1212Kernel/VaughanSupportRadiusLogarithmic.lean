import Erdos1212Kernel.NthPrimeLogarithmic
import Erdos1212Kernel.VaughanPolynomialGapConsumer

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 900000

/-- Uniform source-faithful envelope for the horizontal support distance.
The exponent is cubic in the state size, with the fifth logarithm retained;
this is the strength required by the paper's `log(N)^11` support scale. -/
theorem exists_vaughan_support_product_cubic_log_bound :
    ∃ C : ℝ, ∃ c : ℕ, 0 < C ∧ ∀ (M : ℕ) (R : Finset ℕ),
      R.card ≤ M → (∀ q ∈ R, q.Prime) →
      ((Nat.nth Nat.Prime R.card * vaughanPolynomialPrimeStateGap R + 1 : ℕ) : ℝ) ≤
        C * (M + 1 : ℕ) * (M + c + 2 : ℕ) ^ 2 *
          Real.log (M + c + 2 : ℕ) ^ 5 := by
  obtain ⟨Cp, hCp, hpAll⟩ := exists_nthPrime_le_const_mul_succ_log
  let A := vaughanPolynomialGapParameters.1
  let Y := vaughanPolynomialGapParameters.2
  let c : ℕ := vaughanRankThreshold A + Nat.ceil (2 * Y) + 1
  let logTwo : ℝ := Real.log 2
  let Cmain : ℝ := 16 * Cp * Real.exp (2 * A)
  let Cunit : ℝ := 1 / (4 * logTwo ^ 5)
  let C : ℝ := Cmain + Cunit
  have hlogTwo : 0 < logTwo := by
    dsimp [logTwo]
    exact Real.log_pos (by norm_num)
  have hCmain : 0 < Cmain := by dsimp [Cmain]; positivity
  have hCunit : 0 < Cunit := by dsimp [Cunit]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, ?_⟩
  intro M R hcard hprime
  let rank := vaughanEffectiveRank A Y R
  let S : ℝ := (M + c + 2 : ℕ)
  let base : ℝ := (M + 1 : ℕ) * S ^ 2 * Real.log S ^ 5
  have hrankPos : 0 < rank :=
    (vaughanRankThreshold_data vaughanPolynomialGapParameters_spec.1
      (vaughanEffectiveRank_threshold A Y R)).1
  have hrank : rank ≤ M + c := by
    dsimp [rank, vaughanEffectiveRank, c]
    omega
  have hSgeTwo : (2 : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast (show 2 ≤ M + c + 2 by omega)
  have hSPos : 0 < S := zero_lt_two.trans_le hSgeTwo
  have hlogS : 0 < Real.log S := Real.log_pos (one_lt_two.trans_le hSgeTwo)
  have hrankS : (rank : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast (hrank.trans (show M + c ≤ M + c + 2 by omega))
  have hlogCard : Real.log (R.card + 2 : ℕ) ≤ Real.log S := by
    apply Real.log_le_log (by positivity)
    dsimp [S]
    exact_mod_cast (show R.card + 2 ≤ M + c + 2 by omega)
  have hpRaw := hpAll R.card
  have hp : (Nat.nth Nat.Prime R.card : ℝ) ≤
      Cp * (M + 1 : ℕ) * Real.log S := by
    have hfirst : ((R.card + 1 : ℕ) : ℝ) ≤ (M + 1 : ℕ) := by
      exact_mod_cast (show R.card + 1 ≤ M + 1 by omega)
    have hlogCardNonneg : 0 ≤ Real.log (R.card + 2 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ R.card + 2 by omega))
    have hstep := mul_le_mul hfirst hlogCard hlogCardNonneg (by positivity)
    have hscaled := mul_le_mul_of_nonneg_left hstep hCp.le
    exact hpRaw.trans (by simpa only [mul_assoc] using hscaled)
  have htwoRank : (2 : ℝ) * rank ≤ S ^ 2 := by
    have hr0 : (0 : ℝ) ≤ rank := by positivity
    have hstep := mul_le_mul_of_nonneg_left hrankS (by norm_num : (0 : ℝ) ≤ 2)
    have htwoS : 2 * S ≤ S ^ 2 := by nlinarith
    exact hstep.trans htwoS
  have hlogRank : Real.log (2 * (rank : ℝ)) ≤ 2 * Real.log S := by
    have hmono := Real.log_le_log (by positivity : (0 : ℝ) < 2 * rank) htwoRank
    rw [Real.log_pow] at hmono
    norm_num at hmono ⊢
    exact hmono
  have hlogRankNonneg : 0 ≤ Real.log (2 * (rank : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * rank by omega))
  have hlogPow := pow_le_pow_left₀ hlogRankNonneg hlogRank 4
  have hrankPow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ rank) hrankS 2
  have hJsource := vaughanPolynomialPrimeStateGap_upper R hprime
  have hJ : (vaughanPolynomialPrimeStateGap R : ℝ) ≤
      16 * Real.exp (2 * A) * S ^ 2 * Real.log S ^ 4 := by
    calc
      _ ≤ Real.exp (2 * A) * (rank : ℝ) ^ 2 *
          Real.log (2 * (rank : ℝ)) ^ 4 := hJsource
      _ ≤ Real.exp (2 * A) * S ^ 2 * (2 * Real.log S) ^ 4 := by
        gcongr
      _ = 16 * Real.exp (2 * A) * S ^ 2 * Real.log S ^ 4 := by ring
  have hproduct : (Nat.nth Nat.Prime R.card : ℝ) *
      (vaughanPolynomialPrimeStateGap R : ℝ) ≤ Cmain * base := by
    have hmul := mul_le_mul hp hJ (by positivity)
      (by positivity : (0 : ℝ) ≤ Cp * (M + 1 : ℕ) * Real.log S)
    dsimp [Cmain, base]
    calc
      _ ≤ (Cp * (M + 1 : ℕ) * Real.log S) *
          (16 * Real.exp (2 * A) * S ^ 2 * Real.log S ^ 4) := hmul
      _ = _ := by ring
  have hbaseLower : 4 * logTwo ^ 5 ≤ base := by
    have hlogTwoS : logTwo ≤ Real.log S := by
      dsimp [logTwo]
      exact Real.log_le_log (by norm_num) hSgeTwo
    have hlogPowLower := pow_le_pow_left₀ hlogTwo.le hlogTwoS 5
    have hMS : (4 : ℝ) ≤ (M + 1 : ℕ) * S ^ 2 := by
      have hMOne : (1 : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast (show 1 ≤ M + 1 by omega)
      nlinarith
    dsimp [base]
    nlinarith [mul_le_mul hMS hlogPowLower (pow_nonneg hlogTwo.le 5) (by positivity : (0 : ℝ) ≤ (M + 1 : ℕ) * S ^ 2)]
  have hone : (1 : ℝ) ≤ Cunit * base := by
    dsimp [Cunit]
    have hden : 0 < 4 * logTwo ^ 5 := by positivity
    calc
      (1 : ℝ) ≤ base / (4 * logTwo ^ 5) :=
        (le_div_iff₀ hden).2 (by simpa only [one_mul] using hbaseLower)
      _ = (1 / (4 * logTwo ^ 5)) * base := by field_simp [hden.ne']
  have hcast : ((Nat.nth Nat.Prime R.card *
      vaughanPolynomialPrimeStateGap R + 1 : ℕ) : ℝ) =
      (Nat.nth Nat.Prime R.card : ℝ) *
        (vaughanPolynomialPrimeStateGap R : ℝ) + 1 := by norm_num
  rw [hcast]
  have hsum := add_le_add hproduct hone
  dsimp [C] at hsum ⊢
  nlinarith

end

end Erdos1212Kernel
