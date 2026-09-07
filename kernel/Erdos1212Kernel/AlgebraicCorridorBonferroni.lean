import Erdos1212Kernel.RosserTruncatedAlternating
import Erdos1212Kernel.RosserRestrictedPairing
import Erdos1212Kernel.VaughanIntervalLowerSieve

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

def evenTruncatedAlternatingChoose (m r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (min (2 * r + 1) (m + 1)),
    (-1 : ℤ) ^ k * m.choose k

/-- The complementary even Bonferroni truncation is an upper bound for the
zero-prime-factor indicator. -/
theorem indicator_le_evenTruncatedAlternatingChoose (m r : ℕ) :
    (if m = 0 then 1 else 0) ≤ evenTruncatedAlternatingChoose m r := by
  by_cases hm : m < 2 * r + 1
  · have hmin : min (2 * r + 1) (m + 1) = m + 1 := min_eq_right (by omega)
    rw [evenTruncatedAlternatingChoose, hmin,
      Int.alternating_sum_range_choose]
  · have hmLower : 2 * r + 1 ≤ m := by omega
    have hmPos : 0 < m := by omega
    let t := 2 * r
    have htSucc : t + 1 = 2 * r + 1 := by rfl
    have htEven : Even t := by
      refine ⟨r, ?_⟩
      dsimp [t]
      omega
    have hmEq : m = (m - 1) + 1 := by omega
    have hmin : min (2 * r + 1) (m + 1) = 2 * r + 1 :=
      min_eq_left (by omega)
    rw [evenTruncatedAlternatingChoose, hmin, ← htSucc, hmEq,
      Int.alternating_sum_range_choose_eq_choose, htEven.neg_one_pow]
    simp

theorem sum_choose_mul_evenTruncated_eq (m r : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
      m.choose k •
        (if k < 2 * r + 1 then (-1 : ℤ) ^ k else 0)) =
      evenTruncatedAlternatingChoose m r := by
  simp only [nsmul_eq_mul', ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hset :
      (Finset.range (m + 1)).filter (fun k => k < 2 * r + 1) =
        Finset.range (min (2 * r + 1) (m + 1)) := by
    ext k
    simp [and_comm]
  rw [hset]
  unfold evenTruncatedAlternatingChoose
  apply Finset.sum_congr rfl
  intro k hk
  ring

def corridorEvenTruncatedSubsets
    {α : Type*} [DecidableEq α] (factors : Finset α) (r : ℕ) :
    Finset (Finset α) :=
  factors.powerset.filter fun subset => subset.card < 2 * r + 1

theorem corridorEvenTruncated_alternatingSum_eq
    {α : Type*} [DecidableEq α] (factors : Finset α) (r : ℕ) :
    (∑ subset ∈ corridorEvenTruncatedSubsets factors r,
      (-1 : ℤ) ^ subset.card) =
      evenTruncatedAlternatingChoose factors.card r := by
  unfold corridorEvenTruncatedSubsets
  rw [Finset.sum_filter]
  calc
    (∑ subset ∈ factors.powerset,
        if subset.card < 2 * r + 1 then (-1 : ℤ) ^ subset.card else 0) =
      ∑ k ∈ Finset.range (factors.card + 1),
        factors.card.choose k •
          (if k < 2 * r + 1 then (-1 : ℤ) ^ k else 0) := by
      exact Finset.sum_powerset_apply_card
        (fun k => if k < 2 * r + 1 then (-1 : ℤ) ^ k else 0)
    _ = _ := sum_choose_mul_evenTruncated_eq _ _

def corridorAvoidsPrimeState (Q : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q ∈ Q, ¬q ∣ n

noncomputable def corridorActivePrimeFactors (Q : Finset ℕ) (n : ℕ) : Finset ℕ :=
  Q.filter (fun q => q ∣ n)

def corridorLowerBonferroniWeight (Q : Finset ℕ) (r n : ℕ) : ℤ :=
  oddTruncatedAlternatingChoose (corridorActivePrimeFactors Q n).card r

def corridorUpperBonferroniWeight (Q : Finset ℕ) (r n : ℕ) : ℤ :=
  evenTruncatedAlternatingChoose (corridorActivePrimeFactors Q n).card r

noncomputable def corridorAvoidsIndicator (Q : Finset ℕ) (n : ℕ) : ℤ := by
  classical
  exact if corridorAvoidsPrimeState Q n then 1 else 0

theorem corridorActivePrimeFactors_card_eq_zero_iff
    (Q : Finset ℕ) (n : ℕ) :
    (corridorActivePrimeFactors Q n).card = 0 ↔ corridorAvoidsPrimeState Q n := by
  classical
  rw [Finset.card_eq_zero]
  simp [corridorActivePrimeFactors, corridorAvoidsPrimeState]

theorem corridorLowerBonferroniWeight_le_indicator
    (Q : Finset ℕ) (r n : ℕ) :
    corridorLowerBonferroniWeight Q r n ≤
      corridorAvoidsIndicator Q n := by
  classical
  unfold corridorAvoidsIndicator
  unfold corridorLowerBonferroniWeight
  rw [← corridorActivePrimeFactors_card_eq_zero_iff]
  have hbase := oddTruncatedAlternatingChoose_le_indicator
    (corridorActivePrimeFactors Q n).card r
  by_cases hzero : (corridorActivePrimeFactors Q n).card = 0
  · simpa [hzero] using hbase
  · simpa [hzero] using hbase

theorem corridor_indicator_le_UpperBonferroniWeight
    (Q : Finset ℕ) (r n : ℕ) :
    corridorAvoidsIndicator Q n ≤
      corridorUpperBonferroniWeight Q r n := by
  classical
  unfold corridorAvoidsIndicator
  unfold corridorUpperBonferroniWeight
  rw [← corridorActivePrimeFactors_card_eq_zero_iff]
  have hbase := indicator_le_evenTruncatedAlternatingChoose
    (corridorActivePrimeFactors Q n).card r
  by_cases hzero : (corridorActivePrimeFactors Q n).card = 0
  · simpa [hzero] using hbase
  · simpa [hzero] using hbase

noncomputable def corridorInterval (lower T : ℕ) : Finset ℕ :=
  (Finset.range T).image (fun i => lower + i)

noncomputable def corridorPrimeStateAvoidingInterval
    (Q : Finset ℕ) (lower T : ℕ) : Finset ℕ := by
  classical
  exact (corridorInterval lower T).filter (corridorAvoidsPrimeState Q)

theorem corridor_lowerBonferroni_sum_le_avoiding_card
    (Q : Finset ℕ) (r lower T : ℕ) :
    (∑ n ∈ corridorInterval lower T,
      corridorLowerBonferroniWeight Q r n) ≤
      (corridorPrimeStateAvoidingInterval Q lower T).card := by
  classical
  rw [corridorPrimeStateAvoidingInterval, Finset.card_filter,
    Nat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  simpa [corridorAvoidsIndicator] using
    corridorLowerBonferroniWeight_le_indicator Q r n

theorem corridor_avoiding_card_le_upperBonferroni_sum
    (Q : Finset ℕ) (r lower T : ℕ) :
    ((corridorPrimeStateAvoidingInterval Q lower T).card : ℤ) ≤
      ∑ n ∈ corridorInterval lower T,
        corridorUpperBonferroniWeight Q r n := by
  classical
  rw [corridorPrimeStateAvoidingInterval, Finset.card_filter,
    Nat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  simpa [corridorAvoidsIndicator] using
    corridor_indicator_le_UpperBonferroniWeight Q r n

def corridorSubsetDivides (subset : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q ∈ subset, q ∣ n

noncomputable def corridorDividingTruncatedSubsets
    (Q : Finset ℕ) (r n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (rosserTruncatedSubsets Q r).filter (fun subset =>
    corridorSubsetDivides subset n)

noncomputable def corridorDividingEvenTruncatedSubsets
    (Q : Finset ℕ) (r n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (corridorEvenTruncatedSubsets Q r).filter (fun subset =>
    corridorSubsetDivides subset n)

theorem corridorDividingTruncatedSubsets_eq
    (Q : Finset ℕ) (r n : ℕ) :
    corridorDividingTruncatedSubsets Q r n =
      rosserTruncatedSubsets (corridorActivePrimeFactors Q n) r := by
  classical
  ext subset
  simp only [corridorDividingTruncatedSubsets, Finset.mem_filter,
    rosserTruncatedSubsets, Finset.mem_powerset,
    corridorActivePrimeFactors, corridorSubsetDivides]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hdiv⟩
    refine ⟨?_, hcard⟩
    intro q hq
    exact Finset.mem_filter.mpr ⟨hsub hq, hdiv q hq⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro q hq
      exact (Finset.mem_filter.mp (hsub hq)).1
    · intro q hq
      exact (Finset.mem_filter.mp (hsub hq)).2

theorem corridorDividingEvenTruncatedSubsets_eq
    (Q : Finset ℕ) (r n : ℕ) :
    corridorDividingEvenTruncatedSubsets Q r n =
      corridorEvenTruncatedSubsets (corridorActivePrimeFactors Q n) r := by
  classical
  ext subset
  simp only [corridorDividingEvenTruncatedSubsets, Finset.mem_filter,
    corridorEvenTruncatedSubsets, Finset.mem_powerset,
    corridorActivePrimeFactors, corridorSubsetDivides]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hdiv⟩
    refine ⟨?_, hcard⟩
    intro q hq
    exact Finset.mem_filter.mpr ⟨hsub hq, hdiv q hq⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro q hq
      exact (Finset.mem_filter.mp (hsub hq)).1
    · intro q hq
      exact (Finset.mem_filter.mp (hsub hq)).2

theorem corridorLowerBonferroniWeight_eq_subset_sum
    (Q : Finset ℕ) (r n : ℕ) :
    corridorLowerBonferroniWeight Q r n =
      ∑ subset ∈ corridorDividingTruncatedSubsets Q r n,
        (-1 : ℤ) ^ subset.card := by
  unfold corridorLowerBonferroniWeight
  rw [corridorDividingTruncatedSubsets_eq,
    rosserTruncated_alternatingSum_eq_oddTruncated]

theorem corridorUpperBonferroniWeight_eq_subset_sum
    (Q : Finset ℕ) (r n : ℕ) :
    corridorUpperBonferroniWeight Q r n =
      ∑ subset ∈ corridorDividingEvenTruncatedSubsets Q r n,
        (-1 : ℤ) ^ subset.card := by
  unfold corridorUpperBonferroniWeight
  rw [corridorDividingEvenTruncatedSubsets_eq,
    corridorEvenTruncated_alternatingSum_eq]

noncomputable def corridorSubsetMultipleCount
    (subset : Finset ℕ) (lower T : ℕ) : ℕ := by
  classical
  exact ((corridorInterval lower T).filter (corridorSubsetDivides subset)).card

theorem corridor_lowerBonferroni_sum_eq_subset_multiple_sum
    (Q : Finset ℕ) (r lower T : ℕ) :
    (∑ n ∈ corridorInterval lower T,
      corridorLowerBonferroniWeight Q r n) =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        (-1 : ℤ) ^ subset.card * corridorSubsetMultipleCount subset lower T := by
  classical
  simp_rw [corridorLowerBonferroniWeight_eq_subset_sum,
    corridorDividingTruncatedSubsets, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro subset hsubset
  unfold corridorSubsetMultipleCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hdiv : corridorSubsetDivides subset n
  · simp [hdiv]
  · simp [hdiv]

theorem corridor_upperBonferroni_sum_eq_subset_multiple_sum
    (Q : Finset ℕ) (r lower T : ℕ) :
    (∑ n ∈ corridorInterval lower T,
      corridorUpperBonferroniWeight Q r n) =
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        (-1 : ℤ) ^ subset.card * corridorSubsetMultipleCount subset lower T := by
  classical
  simp_rw [corridorUpperBonferroniWeight_eq_subset_sum,
    corridorDividingEvenTruncatedSubsets, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro subset hsubset
  unfold corridorSubsetMultipleCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hdiv : corridorSubsetDivides subset n
  · simp [hdiv]
  · simp [hdiv]

theorem corridorSubsetDivides_iff_prod_dvd
    {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hprime : ∀ q ∈ Q, q.Prime) (n : ℕ) :
    corridorSubsetDivides subset n ↔ (∏ q ∈ subset, q) ∣ n := by
  classical
  constructor
  · intro hdiv
    induction subset using Finset.induction_on with
    | empty => simp
    | @insert p subset hpnot ih =>
        rw [Finset.prod_insert hpnot]
        have hpQ : p ∈ Q := hsubset (Finset.mem_insert_self p subset)
        have hsQ : subset ⊆ Q := fun q hq => hsubset (Finset.mem_insert_of_mem hq)
        have hpPrime := hprime p hpQ
        have hcop : Nat.Coprime p (∏ q ∈ subset, q) := by
          rw [Nat.coprime_prod_right_iff]
          intro q hq
          have hqPrime := hprime q (hsQ hq)
          apply (Nat.coprime_primes hpPrime hqPrime).2
          intro hpq
          apply hpnot
          simpa [hpq] using hq
        apply hcop.mul_dvd_of_dvd_of_dvd
        · exact hdiv p (Finset.mem_insert_self _ _)
        · apply ih hsQ
          intro q hq
          exact hdiv q (Finset.mem_insert_of_mem hq)
  · intro hprod q hq
    exact (Finset.dvd_prod_of_mem (fun x => x) hq).trans hprod

theorem corridorInterval_eq_Ico (lower T : ℕ) :
    corridorInterval lower T = Finset.Ico lower (lower + T) := by
  classical
  ext n
  simp only [corridorInterval, Finset.mem_image, Finset.mem_range,
    Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩
  · rintro ⟨hnLower, hnUpper⟩
    exact ⟨n - lower, by omega, by omega⟩

theorem corridorSubsetMultipleCount_eq_dvd
    {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hprime : ∀ q ∈ Q, q.Prime) (lower T : ℕ) :
    corridorSubsetMultipleCount subset lower T =
      ((Finset.Ico lower (lower + T)).filter
        (fun n => (∏ q ∈ subset, q) ∣ n)).card := by
  classical
  unfold corridorSubsetMultipleCount
  rw [corridorInterval_eq_Ico]
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => corridorSubsetDivides_iff_prod_dvd hsubset hprime n)

theorem corridorSubsetMultipleCount_error
    {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hprime : ∀ q ∈ Q, q.Prime) {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    |(corridorSubsetMultipleCount subset lower T : ℝ) -
        (T : ℝ) / ((∏ q ∈ subset, q) : ℕ)| ≤ 1 := by
  classical
  let d : ℕ := ∏ q ∈ subset, q
  let lowerBase := lower - 1
  have hdPos : 0 < d := by
    dsimp [d]
    exact Finset.prod_pos fun q hq => (hprime q (hsubset hq)).pos
  have hd : d ≠ 0 := hdPos.ne'
  have hinterval : Finset.Ico lower (lower + T) =
      Finset.Ioc lowerBase (lowerBase + T) := by
    ext n
    dsimp [lowerBase]
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [corridorSubsetMultipleCount_eq_dvd hsubset hprime, hinterval,
    card_Ioc_filter_dvd_eq_div_sub d lowerBase (lowerBase + T) (by omega)]
  have hrem := vaughanIntervalSieve_abs_rem_le_one
    Q lowerBase T d hprime hd
  rw [vaughanIntervalSieve_rem_eq Q lowerBase T d hprime hd] at hrem
  dsimp [d] at hrem ⊢
  convert hrem using 1 <;> field_simp [hd] <;> ring

noncomputable def corridorTruncatedEulerMain
    (Q : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ subset ∈ rosserTruncatedSubsets Q r,
    (-1 : ℝ) ^ subset.card / (((∏ q ∈ subset, q) : ℕ) : ℝ)

noncomputable def corridorEvenTruncatedEulerMain
    (Q : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
    (-1 : ℝ) ^ subset.card / (((∏ q ∈ subset, q) : ℕ) : ℝ)

noncomputable def corridorEulerProduct (Q : Finset ℕ) : ℝ :=
  ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)

theorem corridorEulerProduct_eq_powerset_sum (Q : Finset ℕ) :
    corridorEulerProduct Q =
      ∑ subset ∈ Q.powerset,
        (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ) := by
  classical
  unfold corridorEulerProduct
  rw [show (∏ q ∈ Q, (1 - (q : ℝ)⁻¹)) =
      ∏ q ∈ Q, (1 + (-(q : ℝ)⁻¹)) by
        apply Finset.prod_congr rfl
        intro q hq
        ring]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro subset hsubset
  rw [Finset.prod_neg]
  simp only [Finset.prod_inv_distrib, Nat.cast_prod]
  ring

noncomputable def corridorPowersetTail
    (Q : Finset ℕ) (K : ℕ) : Finset (Finset ℕ) := by
  classical
  exact Q.powerset.filter (fun subset => K ≤ subset.card)

noncomputable def corridorPowersetTailMass
    (Q : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ subset ∈ corridorPowersetTail Q K,
    (1 : ℝ) / (((∏ q ∈ subset, q) : ℕ) : ℝ)

theorem corridorEulerProduct_eq_truncated_add_tail
    (Q : Finset ℕ) (r : ℕ) :
    corridorEulerProduct Q = corridorTruncatedEulerMain Q r +
      ∑ subset ∈ corridorPowersetTail Q (2 * r),
        (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ) := by
  classical
  rw [corridorEulerProduct_eq_powerset_sum]
  unfold corridorTruncatedEulerMain corridorPowersetTail rosserTruncatedSubsets
  have hsplit := Finset.sum_filter_add_sum_filter_not Q.powerset
    (fun subset : Finset ℕ => subset.card < 2 * r)
    (fun subset => (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ))
  simpa only [not_lt] using hsplit.symm

theorem corridorEulerProduct_eq_evenTruncated_add_tail
    (Q : Finset ℕ) (r : ℕ) :
    corridorEulerProduct Q = corridorEvenTruncatedEulerMain Q r +
      ∑ subset ∈ corridorPowersetTail Q (2 * r + 1),
        (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ) := by
  classical
  rw [corridorEulerProduct_eq_powerset_sum]
  unfold corridorEvenTruncatedEulerMain corridorPowersetTail
    corridorEvenTruncatedSubsets
  have hsplit := Finset.sum_filter_add_sum_filter_not Q.powerset
    (fun subset : Finset ℕ => subset.card < 2 * r + 1)
    (fun subset => (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ))
  simpa only [not_lt] using hsplit.symm

theorem corridor_truncatedEulerMain_error_le_tailMass
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) (r : ℕ) :
    |corridorEulerProduct Q - corridorTruncatedEulerMain Q r| ≤
      corridorPowersetTailMass Q (2 * r) := by
  rw [corridorEulerProduct_eq_truncated_add_tail, add_sub_cancel_left]
  unfold corridorPowersetTailMass
  calc
    |∑ subset ∈ corridorPowersetTail Q (2 * r),
        (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ)| ≤
      ∑ subset ∈ corridorPowersetTail Q (2 * r),
        |(-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ subset ∈ corridorPowersetTail Q (2 * r),
        (1 : ℝ) / (((∏ q ∈ subset, q) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro subset hsubset
      have hsubQ : subset ⊆ Q := by
        exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
      have hprodPos : (0 : ℝ) < ((∏ q ∈ subset, q) : ℕ) := by
        exact_mod_cast Finset.prod_pos (fun q hq => (hprime q (hsubQ hq)).pos)
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hprodPos]

theorem corridor_evenTruncatedEulerMain_error_le_tailMass
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) (r : ℕ) :
    |corridorEulerProduct Q - corridorEvenTruncatedEulerMain Q r| ≤
      corridorPowersetTailMass Q (2 * r + 1) := by
  rw [corridorEulerProduct_eq_evenTruncated_add_tail, add_sub_cancel_left]
  unfold corridorPowersetTailMass
  calc
    |∑ subset ∈ corridorPowersetTail Q (2 * r + 1),
        (-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ)| ≤
      ∑ subset ∈ corridorPowersetTail Q (2 * r + 1),
        |(-1 : ℝ) ^ subset.card / ((∏ q ∈ subset, q) : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ subset ∈ corridorPowersetTail Q (2 * r + 1),
        (1 : ℝ) / (((∏ q ∈ subset, q) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro subset hsubset
      have hsubQ : subset ⊆ Q := by
        exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
      have hprodPos : (0 : ℝ) < ((∏ q ∈ subset, q) : ℕ) := by
        exact_mod_cast Finset.prod_pos (fun q hq => (hprime q (hsubQ hq)).pos)
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hprodPos]

theorem corridor_lowerBonferroni_main_sub_card_le
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (r : ℕ) {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    (T : ℝ) * corridorTruncatedEulerMain Q r -
        (rosserTruncatedSubsets Q r).card ≤
      ((∑ n ∈ corridorInterval lower T,
        corridorLowerBonferroniWeight Q r n : ℤ) : ℝ) := by
  classical
  have hsum := corridor_lowerBonferroni_sum_eq_subset_multiple_sum Q r lower T
  have hsumR := congrArg (fun z : ℤ => (z : ℝ)) hsum
  push_cast at hsumR
  have hcast : ((∑ n ∈ corridorInterval lower T,
      corridorLowerBonferroniWeight Q r n : ℤ) : ℝ) =
      ∑ n ∈ corridorInterval lower T,
        (corridorLowerBonferroniWeight Q r n : ℝ) := by push_cast; rfl
  rw [hcast, hsumR]
  have hterm : ∀ subset ∈ rosserTruncatedSubsets Q r,
      (-1 : ℝ) ^ subset.card *
          ((T : ℝ) / ((∏ q ∈ subset, q) : ℕ)) - 1 ≤
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCount subset lower T := by
    intro subset hsubset
    have hsubQ : subset ⊆ Q := by
      exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
    have herr := corridorSubsetMultipleCount_error hsubQ hprime hlower T
    rw [abs_le] at herr
    rcases Nat.even_or_odd subset.card with heven | hodd
    · rw [heven.neg_one_pow]
      norm_num at herr ⊢
      linarith
    · rw [hodd.neg_one_pow]
      norm_num at herr ⊢
      linarith
  calc
    (T : ℝ) * corridorTruncatedEulerMain Q r -
        (rosserTruncatedSubsets Q r).card =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        ((-1 : ℝ) ^ subset.card *
          ((T : ℝ) / ((∏ q ∈ subset, q) : ℕ)) - 1) := by
      unfold corridorTruncatedEulerMain
      rw [Finset.mul_sum]
      have hones : ((rosserTruncatedSubsets Q r).card : ℝ) =
          ∑ _subset ∈ rosserTruncatedSubsets Q r, (1 : ℝ) := by simp
      rw [hones, ← Finset.sum_sub_distrib]
      push_cast
      apply Finset.sum_congr rfl
      intro subset hsubset
      ring
    _ ≤ ∑ subset ∈ rosserTruncatedSubsets Q r,
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCount subset lower T := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact hterm subset hsubset

theorem corridor_upperBonferroni_le_main_add_card
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (r : ℕ) {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    ((∑ n ∈ corridorInterval lower T,
        corridorUpperBonferroniWeight Q r n : ℤ) : ℝ) ≤
      (T : ℝ) * corridorEvenTruncatedEulerMain Q r +
        (corridorEvenTruncatedSubsets Q r).card := by
  classical
  have hsum := corridor_upperBonferroni_sum_eq_subset_multiple_sum Q r lower T
  have hsumR := congrArg (fun z : ℤ => (z : ℝ)) hsum
  push_cast at hsumR
  have hcast : ((∑ n ∈ corridorInterval lower T,
      corridorUpperBonferroniWeight Q r n : ℤ) : ℝ) =
      ∑ n ∈ corridorInterval lower T,
        (corridorUpperBonferroniWeight Q r n : ℝ) := by push_cast; rfl
  rw [hcast, hsumR]
  have hterm : ∀ subset ∈ corridorEvenTruncatedSubsets Q r,
      (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCount subset lower T ≤
        (-1 : ℝ) ^ subset.card *
          ((T : ℝ) / ((∏ q ∈ subset, q) : ℕ)) + 1 := by
    intro subset hsubset
    have hsubQ : subset ⊆ Q := by
      exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
    have herr := corridorSubsetMultipleCount_error hsubQ hprime hlower T
    rw [abs_le] at herr
    rcases Nat.even_or_odd subset.card with heven | hodd
    · rw [heven.neg_one_pow]
      norm_num at herr ⊢
      linarith
    · rw [hodd.neg_one_pow]
      norm_num at herr ⊢
      linarith
  calc
    (∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCount subset lower T) ≤
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        ((-1 : ℝ) ^ subset.card *
          ((T : ℝ) / ((∏ q ∈ subset, q) : ℕ)) + 1) := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact hterm subset hsubset
    _ = (T : ℝ) * corridorEvenTruncatedEulerMain Q r +
        (corridorEvenTruncatedSubsets Q r).card := by
      unfold corridorEvenTruncatedEulerMain
      rw [Finset.mul_sum]
      have hones : ((corridorEvenTruncatedSubsets Q r).card : ℝ) =
          ∑ _subset ∈ corridorEvenTruncatedSubsets Q r, (1 : ℝ) := by simp
      rw [hones, ← Finset.sum_add_distrib]
      push_cast
      apply Finset.sum_congr rfl
      intro subset hsubset
      ring

end

end Erdos1212Kernel
