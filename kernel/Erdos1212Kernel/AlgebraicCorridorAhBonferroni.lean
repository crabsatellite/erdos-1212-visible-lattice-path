import Erdos1212Kernel.AlgebraicCorridorBonferroniScale

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

noncomputable def corridorAh
    (Q : Finset ℕ) (h lower T : ℕ) : ℕ := by
  classical
  exact ((corridorInterval lower T).filter fun n =>
    h ∣ n ∧ corridorAvoidsPrimeState Q n).card

noncomputable def corridorLowerAhSum
    (Q : Finset ℕ) (r h lower T : ℕ) : ℤ := by
  classical
  exact ∑ n ∈ corridorInterval lower T,
    if h ∣ n then corridorLowerBonferroniWeight Q r n else 0

noncomputable def corridorUpperAhSum
    (Q : Finset ℕ) (r h lower T : ℕ) : ℤ := by
  classical
  exact ∑ n ∈ corridorInterval lower T,
    if h ∣ n then corridorUpperBonferroniWeight Q r n else 0

theorem corridorLowerAhSum_le_card
    (Q : Finset ℕ) (r h lower T : ℕ) :
    corridorLowerAhSum Q r h lower T ≤ corridorAh Q h lower T := by
  classical
  unfold corridorLowerAhSum corridorAh
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hh : h ∣ n
  · by_cases havoid : corridorAvoidsPrimeState Q n
    · simpa [hh, havoid, corridorAvoidsIndicator] using
        corridorLowerBonferroniWeight_le_indicator Q r n
    · simpa [hh, havoid, corridorAvoidsIndicator] using
        corridorLowerBonferroniWeight_le_indicator Q r n
  · simp [hh]

theorem corridorAh_card_le_UpperAhSum
    (Q : Finset ℕ) (r h lower T : ℕ) :
    (corridorAh Q h lower T : ℤ) ≤ corridorUpperAhSum Q r h lower T := by
  classical
  unfold corridorUpperAhSum corridorAh
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hh : h ∣ n
  · by_cases havoid : corridorAvoidsPrimeState Q n
    · simpa [hh, havoid, corridorAvoidsIndicator] using
        corridor_indicator_le_UpperBonferroniWeight Q r n
    · simpa [hh, havoid, corridorAvoidsIndicator] using
        corridor_indicator_le_UpperBonferroniWeight Q r n
  · simp [hh]

noncomputable def corridorSubsetMultipleCountWith
    (h : ℕ) (subset : Finset ℕ) (lower T : ℕ) : ℕ := by
  classical
  exact ((corridorInterval lower T).filter fun n =>
    h ∣ n ∧ corridorSubsetDivides subset n).card

theorem corridorLowerAhSum_eq_subset_multiple_sum
    (Q : Finset ℕ) (r h lower T : ℕ) :
    corridorLowerAhSum Q r h lower T =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        (-1 : ℤ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T := by
  classical
  unfold corridorLowerAhSum
  simp_rw [corridorLowerBonferroniWeight_eq_subset_sum,
    corridorDividingTruncatedSubsets, Finset.sum_filter]
  have hdistrib : ∀ n,
      (if h ∣ n then
        ∑ subset ∈ rosserTruncatedSubsets Q r,
          if corridorSubsetDivides subset n then (-1 : ℤ) ^ subset.card else 0
        else 0) =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        if h ∣ n then
          (if corridorSubsetDivides subset n then (-1 : ℤ) ^ subset.card else 0)
        else 0 := by
    intro n
    by_cases hh : h ∣ n <;> simp [hh]
  simp_rw [hdistrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro subset hsubset
  unfold corridorSubsetMultipleCountWith
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hh : h ∣ n <;>
    by_cases hdiv : corridorSubsetDivides subset n <;> simp [hh, hdiv]

theorem corridorUpperAhSum_eq_subset_multiple_sum
    (Q : Finset ℕ) (r h lower T : ℕ) :
    corridorUpperAhSum Q r h lower T =
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        (-1 : ℤ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T := by
  classical
  unfold corridorUpperAhSum
  simp_rw [corridorUpperBonferroniWeight_eq_subset_sum,
    corridorDividingEvenTruncatedSubsets, Finset.sum_filter]
  have hdistrib : ∀ n,
      (if h ∣ n then
        ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
          if corridorSubsetDivides subset n then (-1 : ℤ) ^ subset.card else 0
        else 0) =
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        if h ∣ n then
          (if corridorSubsetDivides subset n then (-1 : ℤ) ^ subset.card else 0)
        else 0 := by
    intro n
    by_cases hh : h ∣ n <;> simp [hh]
  simp_rw [hdistrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro subset hsubset
  unfold corridorSubsetMultipleCountWith
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hh : h ∣ n <;>
    by_cases hdiv : corridorSubsetDivides subset n <;> simp [hh, hdiv]

theorem corridor_h_coprime_subsetProduct
    {h : ℕ} {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q) :
    Nat.Coprime h (∏ q ∈ subset, q) := by
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  exact hcop q (hsubset hq)

theorem corridor_h_mul_subsetProduct_dvd_iff
    {h : ℕ} {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q) (n : ℕ) :
    h * (∏ q ∈ subset, q) ∣ n ↔
      h ∣ n ∧ corridorSubsetDivides subset n := by
  rw [corridorSubsetDivides_iff_prod_dvd hsubset hprime]
  constructor
  · intro hd
    exact ⟨(dvd_mul_right h _).trans hd, (dvd_mul_left _ _).trans hd⟩
  · rintro ⟨hh, hs⟩
    exact (corridor_h_coprime_subsetProduct hsubset hcop).mul_dvd_of_dvd_of_dvd hh hs

theorem corridorSubsetMultipleCountWith_error
    {h : ℕ} {Q subset : Finset ℕ} (hsubset : subset ⊆ Q)
    (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q)
    (hh : 0 < h) {lower : ℕ} (hlower : 0 < lower) (T : ℕ) :
    |(corridorSubsetMultipleCountWith h subset lower T : ℝ) -
        (T : ℝ) / (h * (∏ q ∈ subset, q) : ℕ)| ≤ 1 := by
  classical
  let d := h * (∏ q ∈ subset, q)
  let lowerBase := lower - 1
  have hdPos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos hh (Finset.prod_pos fun q hq => (hprime q (hsubset hq)).pos)
  have hd : d ≠ 0 := hdPos.ne'
  have hinterval : Finset.Ico lower (lower + T) =
      Finset.Ioc lowerBase (lowerBase + T) := by
    ext n
    dsimp [lowerBase]
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold corridorSubsetMultipleCountWith
  rw [corridorInterval_eq_Ico, hinterval]
  have hfilter :
      ((Finset.Ioc lowerBase (lowerBase + T)).filter fun n =>
        h ∣ n ∧ corridorSubsetDivides subset n) =
      ((Finset.Ioc lowerBase (lowerBase + T)).filter fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      (corridor_h_mul_subsetProduct_dvd_iff hsubset hprime hcop n).symm)
  rw [hfilter, card_Ioc_filter_dvd_eq_div_sub d lowerBase (lowerBase + T) (by omega)]
  have hrem := vaughanIntervalSieve_abs_rem_le_one Q lowerBase T d hprime hd
  rw [vaughanIntervalSieve_rem_eq Q lowerBase T d hprime hd] at hrem
  dsimp [d] at hrem ⊢
  convert hrem using 1 <;> field_simp [hd] <;> ring

theorem corridorLowerAh_main_sub_card_le
    {h lower : ℕ} (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q)
    (r : ℕ) (hh : 0 < h) (hlower : 0 < lower) (T : ℕ) :
    (T : ℝ) / h * corridorTruncatedEulerMain Q r -
        (rosserTruncatedSubsets Q r).card ≤
      (corridorLowerAhSum Q r h lower T : ℝ) := by
  classical
  have hsum := corridorLowerAhSum_eq_subset_multiple_sum Q r h lower T
  have hsumR := congrArg (fun z : ℤ => (z : ℝ)) hsum
  push_cast at hsumR
  have hcast : (corridorLowerAhSum Q r h lower T : ℝ) =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T := by
    exact hsumR
  rw [hcast]
  have hterm : ∀ subset ∈ rosserTruncatedSubsets Q r,
      (-1 : ℝ) ^ subset.card *
          ((T : ℝ) / (h * (∏ q ∈ subset, q) : ℕ)) - 1 ≤
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T := by
    intro subset hsubset
    have hsubQ : subset ⊆ Q := by
      exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
    have herr := corridorSubsetMultipleCountWith_error
      hsubQ hprime hcop hh hlower T
    rw [abs_le] at herr
    rcases Nat.even_or_odd subset.card with heven | hodd
    · rw [heven.neg_one_pow]
      norm_num at herr ⊢
      linarith
    · rw [hodd.neg_one_pow]
      norm_num at herr ⊢
      linarith
  calc
    (T : ℝ) / h * corridorTruncatedEulerMain Q r -
        (rosserTruncatedSubsets Q r).card =
      ∑ subset ∈ rosserTruncatedSubsets Q r,
        ((-1 : ℝ) ^ subset.card *
          ((T : ℝ) / (h * (∏ q ∈ subset, q) : ℕ)) - 1) := by
      unfold corridorTruncatedEulerMain
      rw [Finset.mul_sum]
      have hones : ((rosserTruncatedSubsets Q r).card : ℝ) =
          ∑ _subset ∈ rosserTruncatedSubsets Q r, (1 : ℝ) := by simp
      rw [hones, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro subset hsubset
      have hprodPos : (0 : ℝ) < ((∏ q ∈ subset, q) : ℕ) := by
        have hsubQ : subset ⊆ Q :=
          (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
        exact_mod_cast Finset.prod_pos (fun q hq => (hprime q (hsubQ hq)).pos)
      rw [Nat.cast_mul]
      field_simp [show (h : ℝ) ≠ 0 by exact_mod_cast hh.ne', hprodPos.ne']
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact hterm subset hsubset

theorem corridorUpperAh_le_main_add_card
    {h lower : ℕ} (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q)
    (r : ℕ) (hh : 0 < h) (hlower : 0 < lower) (T : ℕ) :
    (corridorUpperAhSum Q r h lower T : ℝ) ≤
      (T : ℝ) / h * corridorEvenTruncatedEulerMain Q r +
        (corridorEvenTruncatedSubsets Q r).card := by
  classical
  have hsum := corridorUpperAhSum_eq_subset_multiple_sum Q r h lower T
  have hsumR := congrArg (fun z : ℤ => (z : ℝ)) hsum
  push_cast at hsumR
  have hcast : (corridorUpperAhSum Q r h lower T : ℝ) =
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T := hsumR
  rw [hcast]
  have hterm : ∀ subset ∈ corridorEvenTruncatedSubsets Q r,
      (-1 : ℝ) ^ subset.card *
          corridorSubsetMultipleCountWith h subset lower T ≤
        (-1 : ℝ) ^ subset.card *
          ((T : ℝ) / (h * (∏ q ∈ subset, q) : ℕ)) + 1 := by
    intro subset hsubset
    have hsubQ : subset ⊆ Q := by
      exact (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
    have herr := corridorSubsetMultipleCountWith_error
      hsubQ hprime hcop hh hlower T
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
          corridorSubsetMultipleCountWith h subset lower T) ≤
      ∑ subset ∈ corridorEvenTruncatedSubsets Q r,
        ((-1 : ℝ) ^ subset.card *
          ((T : ℝ) / (h * (∏ q ∈ subset, q) : ℕ)) + 1) := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact hterm subset hsubset
    _ = (T : ℝ) / h * corridorEvenTruncatedEulerMain Q r +
        (corridorEvenTruncatedSubsets Q r).card := by
      unfold corridorEvenTruncatedEulerMain
      rw [Finset.mul_sum]
      have hones : ((corridorEvenTruncatedSubsets Q r).card : ℝ) =
          ∑ _subset ∈ corridorEvenTruncatedSubsets Q r, (1 : ℝ) := by simp
      rw [hones, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro subset hsubset
      have hprodPos : (0 : ℝ) < ((∏ q ∈ subset, q) : ℕ) := by
        have hsubQ : subset ⊆ Q :=
          (Finset.mem_filter.mp hsubset).1 |> Finset.mem_powerset.mp
        exact_mod_cast Finset.prod_pos (fun q hq => (hprime q (hsubQ hq)).pos)
      rw [Nat.cast_mul]
      field_simp [show (h : ℝ) ≠ 0 by exact_mod_cast hh.ne', hprodPos.ne']

theorem corridorAh_lower_bound
    {h lower : ℕ} (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q)
    (r : ℕ) (hh : 0 < h) (hlower : 0 < lower) (T : ℕ) :
    (T : ℝ) / h * corridorTruncatedEulerMain Q r -
        (rosserTruncatedSubsets Q r).card ≤ corridorAh Q h lower T := by
  exact (corridorLowerAh_main_sub_card_le Q hprime hcop r hh hlower T).trans
    (by exact_mod_cast corridorLowerAhSum_le_card Q r h lower T)

theorem corridorAh_upper_bound
    {h lower : ℕ} (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hcop : ∀ q ∈ Q, Nat.Coprime h q)
    (r : ℕ) (hh : 0 < h) (hlower : 0 < lower) (T : ℕ) :
    (corridorAh Q h lower T : ℝ) ≤
      (T : ℝ) / h * corridorEvenTruncatedEulerMain Q r +
        (corridorEvenTruncatedSubsets Q r).card := by
  have hcard : (corridorAh Q h lower T : ℝ) ≤
      (corridorUpperAhSum Q r h lower T : ℝ) := by
    exact_mod_cast corridorAh_card_le_UpperAhSum Q r h lower T
  exact hcard.trans
    (corridorUpperAh_le_main_add_card Q hprime hcop r hh hlower T)

end

end Erdos1212Kernel
