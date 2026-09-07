import Erdos1212Kernel.IwaniecCubicPaperCount

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

theorem iwaniecWeightedContinuationTerm_eq_sign_prod_of_admissible
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected extension : List α)
    (hadmissible : iwaniecAdmissibleExtension r evenRestriction
      selected extension) :
    iwaniecWeightedContinuationTerm r evenRestriction factorWeight
        selected extension =
      (((-1 : Int) ^ extension.length : Int) : Real) *
        (extension.map factorWeight).prod := by
  induction extension generalizing selected with
  | nil => simp [iwaniecWeightedContinuationTerm]
  | cons factor tail ih =>
      rw [iwaniecAdmissibleExtension] at hadmissible
      rw [iwaniecWeightedContinuationTerm,
        if_pos ⟨hadmissible.1, hadmissible.2.1⟩,
        ih (selected ++ [factor]) hadmissible.2.2]
      simp only [List.length_cons, pow_succ, Int.cast_mul, Int.cast_neg,
        Int.cast_one, List.map_cons, List.prod_cons]
      ring

theorem iwaniecWeightedContinuationTerm_eq_zero_of_not_admissible
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected extension : List α)
    (hnot : ¬iwaniecAdmissibleExtension r evenRestriction selected extension) :
    iwaniecWeightedContinuationTerm r evenRestriction factorWeight
      selected extension = 0 := by
  induction extension generalizing selected with
  | nil => exact (hnot (by trivial)).elim
  | cons factor tail ih =>
      rw [iwaniecWeightedContinuationTerm]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [if_pos hselect]
        have htail : ¬iwaniecAdmissibleExtension r evenRestriction
            (selected ++ [factor]) tail := by
          intro hadmissible
          exact hnot ⟨hselect.1, hselect.2, hadmissible⟩
        rw [ih (selected ++ [factor]) htail]
        ring
      · rw [if_neg hselect]

theorem iwaniecWeightedContinuationTerm_eq_admissibleIte
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected extension : List α) :
    iwaniecWeightedContinuationTerm r evenRestriction factorWeight
        selected extension =
      if iwaniecAdmissibleExtensionBool r evenRestriction selected extension then
        (((-1 : Int) ^ extension.length : Int) : Real) *
          (extension.map factorWeight).prod
      else 0 := by
  by_cases hadmissible : iwaniecAdmissibleExtension r evenRestriction
      selected extension
  · have hbool := (iwaniecAdmissibleExtensionBool_eq_true_iff
      r evenRestriction selected extension).mpr hadmissible
    rw [if_pos hbool]
    exact iwaniecWeightedContinuationTerm_eq_sign_prod_of_admissible
      r evenRestriction factorWeight selected extension hadmissible
  · have hbool : iwaniecAdmissibleExtensionBool r evenRestriction
        selected extension = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hadmissible ((iwaniecAdmissibleExtensionBool_eq_true_iff
        r evenRestriction selected extension).mp htrue)
    rw [if_neg (by simpa using hbool)]
    exact iwaniecWeightedContinuationTerm_eq_zero_of_not_admissible
      r evenRestriction factorWeight selected extension hadmissible

noncomputable def iwaniecAdmissibleExtensionMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) (k : Nat) : Real :=
  by
    classical
    exact ((tail.sublistsLen k).map fun extension =>
      if iwaniecAdmissibleExtensionBool r evenRestriction selected extension then
        (extension.map factorWeight).prod
      else 0).sum

@[simp]
theorem iwaniecAdmissibleExtensionMass_zero
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
      selected tail 0 = 1 := by
  classical
  simp [iwaniecAdmissibleExtensionMass,
    iwaniecAdmissibleExtensionBool]

theorem sum_map_cons_admissibleMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected : List α) (factor : α)
    (values : List (List α)) :
    ((values.map (List.cons factor)).map fun extension =>
        if iwaniecAdmissibleExtensionBool r evenRestriction selected extension then
          (extension.map factorWeight).prod
        else 0).sum =
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        factorWeight factor *
          ((values.map fun extension =>
            if iwaniecAdmissibleExtensionBool r evenRestriction
                (selected ++ [factor]) extension then
              (extension.map factorWeight).prod
            else 0).sum)
      else 0 := by
  classical
  induction values with
  | nil => simp
  | cons extension values ih =>
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · have hbool : iwaniecSelectionAllowedBool r evenRestriction
            selected factor = true := by
          simp [iwaniecSelectionAllowedBool, hselect]
        rw [if_pos hselect] at ih
        rw [List.map_map] at ih
        rw [List.map, List.map, iwaniecAdmissibleExtensionBool, hbool,
          Bool.true_and]
        rw [if_pos hselect]
        cases hchild : iwaniecAdmissibleExtensionBool r evenRestriction
            (selected ++ [factor]) extension
        · simp only [hchild, Bool.false_eq_true, if_false,
            List.map_cons, List.prod_cons, List.sum_cons, zero_add]
          rw [List.map_map]
          exact ih
        · simp only [hchild, if_true, List.map_cons, List.prod_cons,
            List.sum_cons]
          rw [List.map_map]
          rw [ih]
          ring
      · have hbool : iwaniecSelectionAllowedBool r evenRestriction
            selected factor = false := by
          simp [iwaniecSelectionAllowedBool, hselect]
        rw [if_neg hselect] at ih
        rw [List.map_map] at ih
        simpa [iwaniecAdmissibleExtensionBool, hbool, hselect] using ih

/-- Exact reciprocal-mass skip/select recursion. -/
theorem iwaniecAdmissibleExtensionMass_succ_cons
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected : List α) (factor : α)
    (tail : List α) (k : Nat) :
    iwaniecAdmissibleExtensionMass r evenRestriction factorWeight selected
        (factor :: tail) (k + 1) =
      iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
          selected tail (k + 1) +
        if selected.length + 1 < 2 * r ∧
            (Even selected.length ∨ evenRestriction selected factor) then
          factorWeight factor *
            iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
              (selected ++ [factor]) tail k
        else 0 := by
  classical
  unfold iwaniecAdmissibleExtensionMass
  rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append,
    sum_map_cons_admissibleMass]

theorem iwaniecAdmissibleExtensionMass_nonneg
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real)
    (hweight : ∀ factor, 0 ≤ factorWeight factor)
    (selected tail : List α) (k : Nat) :
    0 ≤ iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
      selected tail k := by
  classical
  unfold iwaniecAdmissibleExtensionMass
  apply List.sum_nonneg
  intro value hvalue
  simp only [List.mem_map] at hvalue
  obtain ⟨extension, _hextension, rfl⟩ := hvalue
  split
  · apply List.prod_nonneg
    intro weight hweightMem
    obtain ⟨factor, _hfactor, rfl⟩ := List.mem_map.mp hweightMem
    exact hweight factor
  · exact le_rfl

theorem iwaniecAdmissibleExtensionMass_eq_zero_of_depth
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) (k : Nat)
    (hselected : selected.length < 2 * r)
    (hdepth : 2 * r ≤ selected.length + k) :
    iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
      selected tail k = 0 := by
  classical
  unfold iwaniecAdmissibleExtensionMass
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨extension, hExtension, rfl⟩ := List.mem_map.mp hvalue
  have hlength := List.length_of_sublistsLen hExtension
  have hnot : iwaniecAdmissibleExtensionBool r evenRestriction
      selected extension = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hadmissible := (iwaniecAdmissibleExtensionBool_eq_true_iff
      r evenRestriction selected extension).mp htrue
    have hlt := iwaniecAdmissibleExtension_length_lt
      hselected hadmissible
    omega
  rw [if_neg (by simpa using hnot)]

theorem List.sum_map_flatMap_eq_sum_map_sum
    {α β γ : Type*} [AddCommMonoid γ]
    (outer : List α) (inner : α → List β) (weight : β → γ) :
    ((outer.flatMap inner).map weight).sum =
      (outer.map fun value => ((inner value).map weight).sum).sum := by
  induction outer with
  | nil => simp
  | cons value outer ih =>
      simp [List.flatMap, List.map_append, List.sum_append, ih,
        Function.comp_def]

theorem List.sum_map_mul_left_real
    {α : Type*} (values : List α) (constant : Real)
    (weight : α → Real) :
    (values.map fun value => constant * weight value).sum =
      constant * (values.map weight).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, mul_add]

theorem List.range_map_sum_eq_finset_sum
    (n : Nat) (weight : Nat → Real) :
    ((List.range n).map weight).sum =
      ∑ k ∈ Finset.range n, weight k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      simp

theorem iwaniecWeightedContinuationLayer_eq_sign_mul_mass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) (k : Nat) :
    ((tail.sublistsLen k).map fun extension =>
        iwaniecWeightedContinuationTerm r evenRestriction factorWeight
          selected extension).sum =
      (((-1 : Int) ^ k : Int) : Real) *
        iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
          selected tail k := by
  classical
  unfold iwaniecAdmissibleExtensionMass
  rw [← List.sum_map_mul_left_real]
  apply congrArg List.sum
  apply List.map_congr_left
  intro extension hExtension
  have hlength := List.length_of_sublistsLen hExtension
  rw [iwaniecWeightedContinuationTerm_eq_admissibleIte]
  split
  · rw [hlength]
  · ring

/-- The full weighted Iwaniec expansion is the alternating sum of the exact
paper masses at each tuple depth. -/
theorem iwaniecWeightedExpansionSum_eq_alternatingPaperMass
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α) :
    iwaniecWeightedExpansionSum r evenRestriction factorWeight selected tail =
      ∑ k ∈ Finset.range (tail.length + 1),
        (((-1 : Int) ^ k : Int) : Real) *
          iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
            selected tail k := by
  unfold iwaniecWeightedExpansionSum
  let weight := fun extension : List α =>
    iwaniecWeightedContinuationTerm r evenRestriction factorWeight
      selected extension
  calc
    (tail.sublists.map weight).sum =
        (tail.sublists'.map weight).sum :=
      (List.sublists_perm_sublists' tail).map weight |>.sum_eq
    _ = (((List.range (tail.length + 1)).flatMap fun k =>
          tail.sublistsLen k).map weight).sum :=
      ((List.range_bind_sublistsLen_perm tail).map weight).sum_eq.symm
    _ = ((List.range (tail.length + 1)).map fun k =>
          ((tail.sublistsLen k).map weight).sum).sum :=
      List.sum_map_flatMap_eq_sum_map_sum _ _ _
    _ = ((List.range (tail.length + 1)).map fun k =>
          (((-1 : Int) ^ k : Int) : Real) *
            iwaniecAdmissibleExtensionMass r evenRestriction factorWeight
              selected tail k).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro k _hk
      exact iwaniecWeightedContinuationLayer_eq_sign_mul_mass
        r evenRestriction factorWeight selected tail k
    _ = _ := List.range_map_sum_eq_finset_sum _ _

theorem iwaniecCubicWeightedMainExpansion_eq_alternatingPaperMass
    (r y : Nat) (factors : Finset Nat) :
    iwaniecCubicWeightedMainExpansion r y factors =
      ∑ k ∈ Finset.range (factors.card + 1),
        (((-1 : Int) ^ k : Int) : Real) *
          iwaniecAdmissibleExtensionMass r (iwaniecCubicEvenRestriction y)
            iwaniecReciprocalFactorWeight []
            (iwaniecDescendingFactors factors) k := by
  unfold iwaniecCubicWeightedMainExpansion
  rw [iwaniecWeightedExpansionSum_eq_alternatingPaperMass]
  simp [iwaniecDescendingFactors]

end

end Erdos1212Kernel
