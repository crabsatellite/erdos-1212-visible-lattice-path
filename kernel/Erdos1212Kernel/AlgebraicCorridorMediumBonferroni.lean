import Erdos1212Kernel.AlgebraicCorridorMediumPrime

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

noncomputable def corridorMediumWitnessCandidates
    (small medium : Finset ℕ) (lower T : ℕ) : Finset ℕ := by
  classical
  exact (corridorInterval lower T).filter fun n =>
    corridorAvoidsPrimeState small n ∧ ∃ q ∈ medium, q ∣ n

noncomputable def corridorMediumFirstMoment
    (small medium : Finset ℕ) (lower T : ℕ) : ℤ :=
  ∑ q ∈ medium, corridorAh small q lower T

noncomputable def corridorMediumSecondMoment
    (small medium : Finset ℕ) (lower T : ℕ) : ℤ :=
  ∑ pair ∈ medium.powersetCard 2,
    corridorAh small (∏ q ∈ pair, q) lower T

noncomputable def corridorMediumNonzeroIndicator
    (medium : Finset ℕ) (n : ℕ) : ℤ := by
  classical
  exact if (corridorActivePrimeFactors medium n).card = 0 then 0 else 1

noncomputable def corridorDividingPairs
    (medium : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (medium.powersetCard 2).filter fun pair =>
    corridorSubsetDivides pair n

theorem natCast_sub_choose_two_le_nonzeroIndicator (m : ℕ) :
    (m : ℤ) - (m.choose 2 : ℤ) ≤ if m = 0 then 0 else 1 := by
  by_cases hm0 : m = 0
  · simp [hm0]
  by_cases hm1 : m = 1
  · simp [hm1]
  have hm2 : 2 ≤ m := by omega
  have hchoose : m ≤ m.choose 2 + 1 := by
    induction m with
    | zero => omega
    | succ m ih =>
        by_cases hm : m = 0
        · omega
        rw [Nat.choose_succ_succ]
        simp
  simp [hm0]
  have hchoose' : m ≤ 1 + m.choose 2 := by omega
  exact_mod_cast hchoose'

theorem corridorMediumFirstMoment_eq_active_sum
    (small medium : Finset ℕ) (lower T : ℕ) :
    corridorMediumFirstMoment small medium lower T =
      ∑ n ∈ corridorInterval lower T,
        corridorAvoidsIndicator small n *
          ((corridorActivePrimeFactors medium n).card : ℤ) := by
  classical
  unfold corridorMediumFirstMoment corridorAh
  simp_rw [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases havoid : corridorAvoidsPrimeState small n
  · simp only [havoid, and_true]
    rw [show corridorAvoidsIndicator small n = 1 by
      simp [corridorAvoidsIndicator, havoid], one_mul]
    unfold corridorActivePrimeFactors
    rw [Finset.card_filter, Nat.cast_sum]
  · simp [havoid, corridorAvoidsIndicator]

theorem corridor_pairSubsets_filter_eq_active_powersetCard
    (medium : Finset ℕ) (n : ℕ) :
    corridorDividingPairs medium n =
        (corridorActivePrimeFactors medium n).powersetCard 2 := by
  classical
  ext pair
  simp only [corridorDividingPairs, Finset.mem_filter,
    Finset.mem_powersetCard, corridorActivePrimeFactors,
    corridorSubsetDivides]
  constructor
  · rintro ⟨⟨hpair, hcard⟩, hdiv⟩
    refine ⟨?_, hcard⟩
    intro q hq
    exact Finset.mem_filter.mpr ⟨hpair hq, hdiv q hq⟩
  · rintro ⟨hpair, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro q hq
      exact (Finset.mem_filter.mp (hpair hq)).1
    · intro q hq
      exact (Finset.mem_filter.mp (hpair hq)).2

theorem corridorMediumSecondMoment_eq_active_choose_sum
    (small medium : Finset ℕ)
    (hprime : ∀ q ∈ medium, q.Prime) (lower T : ℕ) :
    corridorMediumSecondMoment small medium lower T =
      ∑ n ∈ corridorInterval lower T,
        corridorAvoidsIndicator small n *
          ((corridorActivePrimeFactors medium n).card.choose 2 : ℤ) := by
  classical
  unfold corridorMediumSecondMoment corridorAh
  simp_rw [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases havoid : corridorAvoidsPrimeState small n
  · simp only [havoid, and_true]
    rw [show corridorAvoidsIndicator small n = 1 by
      simp [corridorAvoidsIndicator, havoid], one_mul]
    rw [← Finset.card_powersetCard,
      ← corridor_pairSubsets_filter_eq_active_powersetCard medium n]
    unfold corridorDividingPairs
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hsubset : pair ⊆ medium := (Finset.mem_powersetCard.mp hpair).1
    rw [corridorSubsetDivides_iff_prod_dvd hsubset hprime]
    by_cases hdiv : (∏ q ∈ pair, q) ∣ n <;> simp [hdiv]
  · simp [havoid, corridorAvoidsIndicator]

theorem corridorMediumWitnessCandidates_card_eq_indicator_sum
    (small medium : Finset ℕ) (lower T : ℕ) :
    ((corridorMediumWitnessCandidates small medium lower T).card : ℤ) =
      ∑ n ∈ corridorInterval lower T,
        corridorAvoidsIndicator small n *
          corridorMediumNonzeroIndicator medium n := by
  classical
  unfold corridorMediumWitnessCandidates
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hactive : (corridorActivePrimeFactors medium n).card = 0
  · have hnone : ¬∃ q ∈ medium, q ∣ n := by
      intro hex
      rcases hex with ⟨q, hq, hdiv⟩
      have : q ∈ corridorActivePrimeFactors medium n := by
        simp [corridorActivePrimeFactors, hq, hdiv]
      have hempty := Finset.card_eq_zero.mp hactive
      simpa [hempty] using this
    simp [hactive, hnone, corridorMediumNonzeroIndicator]
  · have hsome : ∃ q ∈ medium, q ∣ n := by
      have hne : (corridorActivePrimeFactors medium n).Nonempty :=
        Finset.card_ne_zero.mp hactive
      obtain ⟨q, hq⟩ := hne
      exact ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
    by_cases havoid : corridorAvoidsPrimeState small n <;>
      simp [hactive, hsome, havoid, corridorAvoidsIndicator,
        corridorMediumNonzeroIndicator]

/-- The paper's two-term inclusion-exclusion step, indexed by literal
unordered two-element subsets of the medium-prime pool. -/
theorem corridorMedium_two_term_bonferroni
    (small medium : Finset ℕ)
    (hprime : ∀ q ∈ medium, q.Prime) (lower T : ℕ) :
    corridorMediumFirstMoment small medium lower T -
        corridorMediumSecondMoment small medium lower T ≤
      (corridorMediumWitnessCandidates small medium lower T).card := by
  rw [corridorMediumFirstMoment_eq_active_sum,
    corridorMediumSecondMoment_eq_active_choose_sum small medium hprime,
    corridorMediumWitnessCandidates_card_eq_indicator_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases havoid : corridorAvoidsPrimeState small n
  · rw [show corridorAvoidsIndicator small n = 1 by
      simp [corridorAvoidsIndicator, havoid]]
    simp only [one_mul]
    unfold corridorMediumNonzeroIndicator
    exact natCast_sub_choose_two_le_nonzeroIndicator _
  · rw [show corridorAvoidsIndicator small n = 0 by
      simp [corridorAvoidsIndicator, havoid]]
    simp

end

end Erdos1212Kernel
