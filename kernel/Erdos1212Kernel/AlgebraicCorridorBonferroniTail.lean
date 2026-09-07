import Erdos1212Kernel.AlgebraicCorridorBonferroni
import Erdos1212Kernel.JointFiniteBoxPhaseLift
import Erdos1212Kernel.IwaniecPaperAFactorialTail

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators NNReal

noncomputable def corridorElementaryMass (Q : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ subset ∈ Q.powersetCard k,
    (1 : ℝ) / (((∏ q ∈ subset, q) : ℕ) : ℝ)

noncomputable def corridorPrimeReciprocalMass (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

theorem corridorPowersetTailMass_antitone
    (Q : Finset ℕ) {K L : ℕ} (hKL : K ≤ L) :
    corridorPowersetTailMass Q L ≤ corridorPowersetTailMass Q K := by
  classical
  unfold corridorPowersetTailMass corridorPowersetTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro subset hsubset
    rw [Finset.mem_filter] at hsubset ⊢
    exact ⟨hsubset.1, hKL.trans hsubset.2⟩
  · intro subset hsubset hnot
    positivity

theorem corridorPowersetTailMass_eq_sum_elementary
    (Q : Finset ℕ) (K : ℕ) :
    corridorPowersetTailMass Q K =
      ∑ k ∈ Finset.Ico K (Q.card + 1), corridorElementaryMass Q k := by
  classical
  unfold corridorPowersetTailMass
  let tail := corridorPowersetTail Q K
  have hmaps : ∀ subset ∈ tail,
      subset.card ∈ Finset.Ico K (Q.card + 1) := by
    intro subset hsubset
    have hs := Finset.mem_filter.mp hsubset
    have hsubQ := Finset.mem_powerset.mp hs.1
    exact Finset.mem_Ico.mpr ⟨hs.2, Nat.lt_succ_of_le (Finset.card_le_card hsubQ)⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun subset : Finset ℕ =>
      (1 : ℝ) / (((∏ q ∈ subset, q) : ℕ) : ℝ))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro k hk
  unfold corridorElementaryMass
  apply Finset.sum_congr
  · ext subset
    simp only [tail, corridorPowersetTail, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, hK⟩, hcard⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      have hkLower := (Finset.mem_Ico.mp hk).1
      exact ⟨⟨hsub, by omega⟩, hcard⟩
  · intro subset hsubset
    rfl

noncomputable def corridorReciprocalWeightNN (q : ℕ) : NNReal :=
  (q : NNReal)⁻¹

theorem corridorElementaryMass_le_factorialTerm
    (Q : Finset ℕ) (k : ℕ) :
    corridorElementaryMass Q k ≤
      corridorPrimeReciprocalMass Q ^ k / (k.factorial : ℝ) := by
  have hnn := finiteDistinctNNActivity_le_pow_div_factorial
    corridorReciprocalWeightNN Q k
  have hleft : (finiteDistinctNNActivity corridorReciprocalWeightNN Q k : ℝ) =
      corridorElementaryMass Q k := by
    unfold corridorElementaryMass finiteDistinctNNActivity corridorReciprocalWeightNN
    push_cast
    apply Finset.sum_congr rfl
    intro subset hsubset
    rw [Finset.prod_inv_distrib]
    rw [one_div]
  have hsum : ((∑ label ∈ Q, corridorReciprocalWeightNN label : NNReal) : ℝ) =
      corridorPrimeReciprocalMass Q := by
    unfold corridorPrimeReciprocalMass corridorReciprocalWeightNN
    simp only [NNReal.coe_sum, NNReal.coe_inv, NNReal.coe_natCast]
  have hnnR : (finiteDistinctNNActivity corridorReciprocalWeightNN Q k : ℝ) ≤
      (((∑ label ∈ Q, corridorReciprocalWeightNN label) ^ k /
        (k.factorial : NNReal) : NNReal) : ℝ) := by
    exact_mod_cast hnn
  rw [hleft, NNReal.coe_div, NNReal.coe_pow, hsum,
    NNReal.coe_natCast] at hnnR
  exact hnnR

theorem corridorPowersetTailMass_le_factorialTail
    (Q : Finset ℕ) (K : ℕ) :
    corridorPowersetTailMass Q K ≤
      ∑ k ∈ Finset.Ico K (Q.card + 1),
        iwaniecFactorialTerm (corridorPrimeReciprocalMass Q) k := by
  rw [corridorPowersetTailMass_eq_sum_elementary]
  apply Finset.sum_le_sum
  intro k hk
  exact corridorElementaryMass_le_factorialTerm Q k

theorem corridorPowersetTailMass_le_twice_first
    (Q : Finset ℕ) (K : ℕ)
    (hthreshold : 2 * corridorPrimeReciprocalMass Q ≤ (K + 1 : ℕ)) :
    corridorPowersetTailMass Q K ≤
      2 * iwaniecFactorialTerm (corridorPrimeReciprocalMass Q) K := by
  have hmass : 0 ≤ corridorPrimeReciprocalMass Q := by
    unfold corridorPrimeReciprocalMass
    positivity
  exact (corridorPowersetTailMass_le_factorialTail Q K).trans
    (iwaniecFactorialTerm_sum_tail_le hmass K (Q.card + 1) hthreshold)

end

end Erdos1212Kernel
