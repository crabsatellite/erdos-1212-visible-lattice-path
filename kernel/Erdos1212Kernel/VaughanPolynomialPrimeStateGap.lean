import Erdos1212Kernel.VaughanEquationElevenAbsorption
import Erdos1212Kernel.StateJacobsthalCompositeSurvivor

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 800000

def vaughanEffectiveRank (A Y : Real) (Q : Finset Nat) : Nat :=
  max (vaughanRankThreshold A) (max Q.card (Nat.ceil (2 * Y)))

theorem vaughanEffectiveRank_threshold (A Y : Real) (Q : Finset Nat) :
    vaughanRankThreshold A ≤ vaughanEffectiveRank A Y Q :=
  le_max_left _ _

theorem vaughanEffectiveRank_card (A Y : Real) (Q : Finset Nat) :
    Q.card ≤ vaughanEffectiveRank A Y Q :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem vaughanEffectiveRank_level_large {A Y : Real} (hA : 192 ≤ A) (hY : 0 ≤ Y)
    (Q : Finset Nat) :
    Y ≤ (vaughanIntervalLength A (vaughanEffectiveRank A Y Q) : Real) := by
  let rank := vaughanEffectiveRank A Y Q
  obtain ⟨hr0, hu2, _hlogr, hscale⟩ :=
    vaughanRankThreshold_data hA (vaughanEffectiveRank_threshold A Y Q)
  have hceil : ((Nat.ceil (2 * Y) : Nat) : Real) ≤ (rank : Real) := by
    exact_mod_cast (show Nat.ceil (2 * Y) ≤ rank from
      (le_max_right Q.card (Nat.ceil (2 * Y))).trans (le_max_right _ _))
  have hYrank : 2 * Y ≤ (rank : Real) := (Nat.le_ceil (2 * Y)).trans hceil
  have hrOne : (1 : Real) ≤ rank := by exact_mod_cast (show 1 ≤ rank by omega)
  have hrSq : (rank : Real) ≤ (rank : Real) ^ 2 := by nlinarith only [hrOne]
  have he : (2 : Real) ≤ Real.exp (2 * A) := by
    have hh := Real.add_one_le_exp (2 * A)
    linarith only [hA, hh]
  have huPow : (1 : Real) ≤ Real.log (2 * (rank : Real)) ^ 4 :=
    one_le_pow₀ (by linarith only [hu2])
  have hH : 2 * (rank : Real) ^ 2 ≤ vaughanIntervalScale A rank := by
    unfold vaughanIntervalScale
    have hh : Real.exp (2 * A) * (rank : Real) ^ 2 ≤
        Real.exp (2 * A) * (rank : Real) ^ 2 * Real.log (2 * (rank : Real)) ^ 4 :=
      by
        have hmul := mul_le_mul_of_nonneg_left huPow
          (mul_nonneg (Real.exp_pos (2 * A)).le (sq_nonneg (rank : Real)))
        simpa only [mul_one] using hmul
    have heScaled := mul_le_mul_of_nonneg_right he (sq_nonneg (rank : Real))
    calc
      _ ≤ Real.exp (2 * A) * (rank : Real) ^ 2 := by simpa only [mul_comm] using heScaled
      _ ≤ _ := by simpa only [mul_assoc, mul_one] using hh
  have hhalf := vaughanIntervalLength_half_lower hscale
  calc
    Y ≤ (rank : Real) := by linarith only [hYrank, hY]
    _ ≤ (rank : Real) ^ 2 := hrSq
    _ ≤ vaughanIntervalScale A rank / 2 := by linarith only [hH]
    _ ≤ _ := hhalf

/-- The actual-state count is positive after the literal small-pool
lower bound and equation-(11) loss are combined at the uniform effective rank. -/
theorem exists_vaughanActualState_count_positive :
    ∃ A Y : Real, 192 ≤ A ∧ 1 < Y ∧ ∀ (Q : Finset Nat),
      (∀ q ∈ Q, Nat.Prime q) → ∀ lower : Nat,
      0 < (primeStateAvoidingIndices Q lower
        (vaughanIntervalLength A (vaughanEffectiveRank A Y Q))).card := by
  obtain ⟨A₀, Y, hA₀, hY, hsmall⟩ := exists_vaughanSieve_smallPool_count_lower
  let A := max A₀ 192
  have hAA₀ : A₀ ≤ A := le_max_left _ _
  have hA192 : 192 ≤ A := le_max_right _ _
  refine ⟨A, Y, hA192, hY, ?_⟩
  intro Q hprime lower
  let rank := vaughanEffectiveRank A Y Q
  let h := vaughanIntervalLength A rank
  let X := vaughanSieveCutoff A (h : Real)
  have hr : vaughanRankThreshold A ≤ rank := vaughanEffectiveRank_threshold A Y Q
  have hcard : Q.card ≤ rank := vaughanEffectiveRank_card A Y Q
  obtain ⟨_hr0, _hu2, _hlogr, hscale⟩ := vaughanRankThreshold_data hA192 hr
  have hh : 0 < h := vaughanIntervalLength_pos hscale
  have hhY : Y ≤ (h : Real) := vaughanEffectiveRank_level_large hA192 (zero_le_one.trans hY.le) Q
  have hlogs := vaughanIntervalLength_log_bounds hA192 hr
  have hS := hsmall A h lower hAA₀ hhY hlogs.1
  have hX : 0 < X := vaughanSieveCutoff_pos A (by exact_mod_cast hh)
  have hcompare := primeStateAvoiding_full_realCutoff_lower
    (Q := Q) (X := X) (lower := lower) (length := h) hprime hX
  have hlossRank := vaughanEquationEleven_loss_absorbed hA192 hr
  have hfactor : 0 ≤ (h : Real) / X + 1 := by positivity
  have hlossCard : (Q.card : Real) * ((h : Real) / X + 1) ≤
      A * (h : Real) / Real.log (h : Real) ^ 2 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hfactor).trans hlossRank
  have hpositive : (0 : Real) < (primeStateAvoidingIndices Q lower h).card := by
    change 2 * A * (h : Real) / Real.log (h : Real) ^ 2 <
      ((primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower h).card : Real) at hS
    change ((primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower h).card : Real) -
      (Q.card : Real) * ((h : Real) / X + 1) ≤
        ((primeStateAvoidingIndices Q lower h).card : Real) at hcompare
    have hremaining : A * (h : Real) / Real.log (h : Real) ^ 2 <
        ((primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower h).card : Real) -
          (Q.card : Real) * ((h : Real) / X + 1) := by
      apply (lt_sub_iff_add_lt).mpr
      have hpaid : A * (h : Real) / Real.log (h : Real) ^ 2 +
          (Q.card : Real) * ((h : Real) / X + 1) ≤
            A * (h : Real) / Real.log (h : Real) ^ 2 +
              A * (h : Real) / Real.log (h : Real) ^ 2 :=
        add_le_add le_rfl hlossCard
      have hpaid' : A * (h : Real) / Real.log (h : Real) ^ 2 +
          (Q.card : Real) * ((h : Real) / X + 1) ≤
            2 * A * (h : Real) / Real.log (h : Real) ^ 2 := by
        convert hpaid using 1 <;> ring
      exact hpaid'.trans_lt hS
    have hAterm : 0 < A * (h : Real) / Real.log (h : Real) ^ 2 := by
      have hlogpos : 0 < Real.log (h : Real) := by linarith only [hlogs.1, hA192]
      positivity
    exact hAterm.trans (hremaining.trans_le hcompare)
  exact_mod_cast hpositive

/-- Vaughan--Iwaniec polynomial every-interval bound for every literal
finite prime state. Bounded state sizes are handled by the effective rank,
not by a conditional or finite certificate. -/
theorem exists_vaughanPolynomial_primeStateCoprimeGapBound :
    ∃ A Y : Real, 192 ≤ A ∧ 1 < Y ∧ ∀ (Q : Finset Nat),
      (∀ q ∈ Q, Nat.Prime q) →
      let rank := vaughanEffectiveRank A Y Q
      let J := vaughanIntervalLength A rank
      PrimeStateCoprimeGapBound Q J ∧
        (J : Real) ≤ Real.exp (2 * A) * (rank : Real) ^ 2 *
          Real.log (2 * (rank : Real)) ^ 4 := by
  obtain ⟨A, Y, hA, hY, hcount⟩ := exists_vaughanActualState_count_positive
  refine ⟨A, Y, hA, hY, ?_⟩
  intro Q hprime
  let rank := vaughanEffectiveRank A Y Q
  let J := vaughanIntervalLength A rank
  have hr := vaughanEffectiveRank_threshold A Y Q
  have hscale := (vaughanRankThreshold_data hA hr).2.2.2
  have hJ : 0 < J := vaughanIntervalLength_pos hscale
  refine ⟨⟨hJ, ?_⟩, ?_⟩
  · intro lower
    have hcard := hcount Q hprime lower
    obtain ⟨index, hindex⟩ := Finset.card_pos.mp hcard
    have hdata := Finset.mem_filter.mp hindex
    let candidate := lower + 1 + index
    refine ⟨candidate, ?_, ?_, hdata.2⟩
    · dsimp [candidate]
      omega
    · have hindexLt := Finset.mem_range.mp hdata.1
      dsimp [candidate, J]
      omega
  · exact vaughanIntervalLength_upper A rank

end

end Erdos1212Kernel
