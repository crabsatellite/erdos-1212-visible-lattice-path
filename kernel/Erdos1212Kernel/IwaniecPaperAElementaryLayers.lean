import Erdos1212Kernel.IwaniecPaperSupportCount
import Erdos1212Kernel.IwaniecTerminalElementaryBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecElementaryMass_eq_sublistsLen_sum
    {α : Type*} (weight : α → Real) (factors : List α) (k : Nat) :
    iwaniecElementaryMass weight k factors =
      ((factors.sublistsLen k).map fun extension =>
        (extension.map fun p => |weight p|).prod).sum := by
  induction factors generalizing k with
  | nil => cases k <;> simp [iwaniecElementaryMass]
  | cons p factors ih =>
      cases k with
      | zero => simp [iwaniecElementaryMass]
      | succ k =>
          rw [iwaniecElementaryMass, List.sublistsLen_succ_cons,
            List.map_append, List.sum_append, ih (k + 1), ih k]
          simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
          rw [List.sum_map_mul_left_real]

theorem iwaniecFilteredCount_le_weightedSum
    {α : Type*} (values : List α) (pred : α → Bool) (weight : α → Real)
    (hnonneg : ∀ a ∈ values, 0 ≤ weight a)
    (hselected : ∀ a ∈ values, pred a = true → 1 ≤ weight a) :
    ((values.filter pred).length : Real) ≤ (values.map weight).sum := by
  induction values with
  | nil => simp
  | cons a values ih =>
      have htail := ih (fun b hb => hnonneg b (by simp [hb]))
        (fun b hb => hselected b (by simp [hb]))
      cases hpa : pred a with
      | true =>
          have ha := hselected a (by simp) hpa
          simp [List.filter_cons, hpa]
          linarith
      | false =>
          have ha := hnonneg a (by simp)
          simp [List.filter_cons, hpa]
          linarith

theorem iwaniecReciprocalListProduct (factors : List Nat) :
    (factors.map (fun p : Nat => (p : Real)⁻¹)).prod = (factors.prod : Real)⁻¹ := by
  induction factors with
  | nil => simp
  | cons p factors ih => simp [ih, Nat.cast_mul, mul_comm]

theorem iwaniecCubicRealProductCount_le_choose
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat) :
    iwaniecCubicRealProductCount offset level factors k ≤ factors.length.choose k := by
  classical
  unfold iwaniecCubicRealProductCount
  simpa only [List.length_sublistsLen] using
    List.length_filter_le
      (fun extension => decide (iwaniecCubicRealAdmissible offset level extension ∧
        (extension.prod : Real) < level)) (factors.sublistsLen k)

/-- Long-tuple estimate from the paper's strict product bound, retaining the
full reciprocal product rather than counting arbitrary prime choices. -/
theorem iwaniecCubicRealProductCount_le_level_elementary
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat)
    (hlevel : 0 ≤ level) (hpositive : ∀ p ∈ factors, 0 < p) :
    (iwaniecCubicRealProductCount offset level factors k : Real) ≤
      level * iwaniecElementaryMass (fun p : Nat => (p : Real)⁻¹) k factors := by
  classical
  let values := factors.sublistsLen k
  let pred := fun extension : List Nat =>
    decide (iwaniecCubicRealAdmissible offset level extension ∧
      (extension.prod : Real) < level)
  let weight := fun extension : List Nat => level * (extension.prod : Real)⁻¹
  have hbound : ((values.filter pred).length : Real) ≤ (values.map weight).sum := by
    apply iwaniecFilteredCount_le_weightedSum
    · intro extension hext
      dsimp [weight]
      positivity
    · intro extension hext hpred
      have hlt : (extension.prod : Real) < level := (of_decide_eq_true hpred).2
      have hsub := (List.mem_sublistsLen.mp hext).1
      have hprod : 0 < extension.prod := List.prod_pos (fun p hp =>
        hpositive p (hsub.subset hp))
      have hprodReal : (0 : Real) < extension.prod := by exact_mod_cast hprod
      dsimp [weight]
      rw [← div_eq_mul_inv, le_div_iff₀ hprodReal, one_mul]
      exact hlt.le
  change (iwaniecCubicRealProductCount offset level factors k : Real) ≤ _ at hbound
  rw [iwaniecElementaryMass_eq_sublistsLen_sum]
  simp only [abs_inv, Nat.abs_cast, iwaniecReciprocalListProduct]
  dsimp [weight, values] at hbound
  rwa [List.sum_map_mul_left_real] at hbound

theorem factorial_mul_iwaniecCubicRealProductCount_le
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat)
    (hlevel : 0 ≤ level) (hpositive : ∀ p ∈ factors, 0 < p) :
    (k.factorial : Real) * iwaniecCubicRealProductCount offset level factors k ≤
      level * (factors.map (fun p : Nat => (p : Real)⁻¹)).sum ^ k := by
  have hcount := iwaniecCubicRealProductCount_le_level_elementary
    offset level factors k hlevel hpositive
  have hscaled := mul_le_mul_of_nonneg_left hcount
    (by positivity : (0 : Real) ≤ k.factorial)
  have helementary := factorial_mul_iwaniecElementaryMass_le_sum_pow
    (fun p : Nat => (p : Real)⁻¹) k factors
  simp only [abs_inv, Nat.abs_cast] at helementary
  have hweighted := mul_le_mul_of_nonneg_left helementary hlevel
  nlinarith

/-- The actual paper count, including all constraints, has the reciprocal
factorial bound used in its long-layer tail. -/
theorem iwaniecCubicRealProductCount_le_reciprocal_factorial
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat)
    (hlevel : 0 ≤ level) (hpositive : ∀ p ∈ factors, 0 < p) :
    (iwaniecCubicRealProductCount offset level factors k : Real) ≤
      level * (factors.map (fun p : Nat => (p : Real)⁻¹)).sum ^ k / k.factorial := by
  rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos k : (0 : Real) < k.factorial)]
  simpa only [mul_comm] using factorial_mul_iwaniecCubicRealProductCount_le
    offset level factors k hlevel hpositive

end

end Erdos1212Kernel
