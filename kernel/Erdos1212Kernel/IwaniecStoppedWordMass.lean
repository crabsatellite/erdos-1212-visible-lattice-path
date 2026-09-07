import Erdos1212Kernel.IwaniecStoppedWordProduct

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def iwaniecStoppedWordMass (offset : Nat) (level : Real) (factors : List Nat) (k : Nat) : Real :=
  ((factors.sublistsLen k).map (iwaniecStoppedWordWeight offset level)).sum

@[simp] theorem iwaniecStoppedWordMass_zero (offset : Nat) (level : Real) (factors : List Nat) :
    iwaniecStoppedWordMass offset level factors 0 = 0 := by simp [iwaniecStoppedWordMass]

theorem iwaniecStoppedWordMass_succ_cons (offset : Nat) (level : Real) (p : Nat) (factors : List Nat) (k : Nat) :
    iwaniecStoppedWordMass offset level (p :: factors) (k + 1) =
      iwaniecStoppedWordMass offset level factors (k + 1) +
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecStoppedWordMass (offset + 1) (level / p) factors k
        else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0 := by
  unfold iwaniecStoppedWordMass
  rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append]
  apply congrArg (fun x : Real => ((factors.sublistsLen (k + 1)).map (iwaniecStoppedWordWeight offset level)).sum + x)
  rw [List.map_map]
  by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
  · simp only [Function.comp_def, iwaniecStoppedWordWeight, if_pos hc, List.sum_map_mul_left_real]
  · rw [if_neg hc]
    by_cases hk : k = 0
    · subst k
      simp [iwaniecStoppedWordWeight, hc]
    · rw [if_neg hk]
      apply List.sum_eq_zero
      intro value hv
      obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hv
      have hne : word ≠ [] := by
        intro hz
        have hlen := List.length_of_sublistsLen hword
        rw [hz, List.length_nil] at hlen
        exact hk hlen.symm
      change iwaniecStoppedWordWeight offset level (p :: word) = 0
      rw [iwaniecStoppedWordWeight, if_neg hc, if_neg hne]

theorem iwaniecStoppedWordMass_first_factor (offset : Nat) (level : Real) (factors : List Nat) (k : Nat) :
    iwaniecStoppedWordMass offset level factors (k + 1) =
      ∑ i : Fin factors.length,
        if Even offset ∨ (factors[i] : Real) ^ 3 < level then
          (factors[i] : Real)⁻¹ * iwaniecStoppedWordMass (offset + 1) (level / factors[i])
            (factors.drop (i.val + 1)) k
        else if k = 0 then (factors[i] : Real)⁻¹ * iwaniecPaperR (factors[i] : Real) else 0 := by
  induction factors with
  | nil => simp [iwaniecStoppedWordMass]
  | cons p factors ih =>
      rw [iwaniecStoppedWordMass_succ_cons, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero,
        List.getElem_cons_zero, zero_add, List.drop_succ_cons, List.drop_zero,
        Fin.val_succ, List.getElem_cons_succ]
      exact add_comm _ _

theorem iwaniecStoppedWordMass_first_prime (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecStoppedWordMass offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (k + 1) =
      ∑ p ∈ iwaniecStrictPrimePool z,
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecStoppedWordMass (offset + 1) (level / p)
            (iwaniecDescendingFactors (iwaniecStrictPrimePool (p : Real))) k
        else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0 := by
  classical
  rw [iwaniecStoppedWordMass_first_factor]
  calc
    _ = ∑ i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length,
        if Even offset ∨ ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) ^ 3 < level then
          ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real)⁻¹ *
            iwaniecStoppedWordMass (offset + 1) (level / (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i])
              (iwaniecDescendingFactors (iwaniecStrictPrimePool
                ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real))) k
        else if k = 0 then ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real)⁻¹ *
          iwaniecPaperR ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iwaniecStrictPrimeSuffix z i]
    _ = _ := iwaniecSum_descendingFactors_real (iwaniecStrictPrimePool z)
      (fun p : Nat => if Even offset ∨ (p : Real) ^ 3 < level then
        (p : Real)⁻¹ * iwaniecStoppedWordMass (offset + 1) (level / p)
          (iwaniecDescendingFactors (iwaniecStrictPrimePool (p : Real))) k
       else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0)

/-- The original stopped layer is exactly the ordered tuple-weight sum. -/
theorem iwaniecPaperStoppedLayer_eq_wordMass (k offset : Nat) (level z : Real) :
    iwaniecPaperStoppedLayer offset level z k =
      iwaniecStoppedWordMass offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) k := by
  induction k generalizing offset level z with
  | zero => simp
  | succ k ih =>
      rw [iwaniecPaperStoppedLayer_first_prime, iwaniecStoppedWordMass_first_prime]
      apply Finset.sum_congr rfl
      intro p hp
      rw [ih (offset + 1) (level / p) p]

end

end Erdos1212Kernel
