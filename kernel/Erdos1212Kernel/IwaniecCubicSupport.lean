import Erdos1212Kernel.IwaniecCubicLowerMoebius

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators
open Finset Nat

set_option maxHeartbeats 1400000

/-- The exact parity-sensitive invariant carried by Iwaniec's cubic tree.
At odd depth the selected product is already below `y`.  At positive even
depth the square of the last selected factor is retained as slack for the
next unrestricted odd selection. -/
def iwaniecCubicPrefixInvariant
    (y : Nat) (selected : List Nat) (previous : Nat) : Prop :=
  (Even selected.length ∧
      (selected = [] ∨ selected.prod * previous ^ 2 < y)) ∨
    (Odd selected.length ∧ selected.prod < y)

theorem iwaniecCubicPrefixInvariant_nil (y previous : Nat) :
    iwaniecCubicPrefixInvariant y [] previous := by
  exact Or.inl ⟨by simp, Or.inl rfl⟩

theorem iwaniecCubicPrefixInvariant_extend
    {r y previous factor : Nat} {selected : List Nat}
    (hpreviousPos : 0 < previous) (hpreviousLt : previous < y)
    (_hfactorPos : 0 < factor) (hfactorLe : factor ≤ previous)
    (hinvariant : iwaniecCubicPrefixInvariant y selected previous)
    (hselect : selected.length + 1 < 2 * r ∧
      (Even selected.length ∨
        iwaniecCubicEvenRestriction y selected factor)) :
    iwaniecCubicPrefixInvariant y (selected ++ [factor]) factor := by
  rcases hinvariant with ⟨heven, hempty | hslack⟩ | ⟨hodd, hproduct⟩
  · right
    constructor
    · simpa using heven.add_one
    · subst selected
      simpa using hfactorLe.trans_lt hpreviousLt
  · right
    constructor
    · simpa using heven.add_one
    · have hfactorLeSq : factor ≤ previous ^ 2 := by
        calc
          factor ≤ previous := hfactorLe
          _ ≤ previous ^ 2 := by nlinarith
      simp only [List.prod_append, List.prod_singleton]
      exact (Nat.mul_le_mul_left selected.prod hfactorLeSq).trans_lt hslack
  · left
    constructor
    · simpa using hodd.add_one
    · right
      have hnotEven : ¬Even selected.length :=
        Nat.not_even_iff_odd.mpr hodd
      have hrestriction :
          iwaniecCubicEvenRestriction y selected factor = true := by
        rcases hselect.2 with heven | hrestriction
        · exact (hnotEven heven).elim
        · exact hrestriction
      have hcubic : factor ^ 3 * selected.prod < y := by
        simpa [iwaniecCubicEvenRestriction] using hrestriction
      simp only [List.prod_append, List.prod_singleton]
      nlinarith [hcubic]

/-- A nonzero continuation term ends with product below the cubic level.
`previous` is an upper bound for the first available factor; decreasing order
then supplies the bound recursively. -/
theorem iwaniecLowerContinuationTerm_ne_zero_prod_lt
    (r y previous : Nat) (selected extension : List Nat)
    (hy : 1 < y) (hpreviousPos : 0 < previous)
    (hpreviousLt : previous < y)
    (hinvariant : iwaniecCubicPrefixInvariant y selected previous)
    (hpositive : ∀ factor ∈ extension, 0 < factor)
    (hbound : ∀ factor ∈ extension, factor ≤ previous)
    (hordered : extension.Pairwise fun left right => right ≤ left)
    (hterm : iwaniecLowerContinuationTerm r
      (iwaniecCubicEvenRestriction y) selected extension ≠ 0) :
    (selected ++ extension).prod < y := by
  induction extension generalizing selected previous with
  | nil =>
      simp only [List.append_nil]
      rcases hinvariant with ⟨_heven, hempty | hslack⟩ |
        ⟨_hodd, hproduct⟩
      · subst selected
        simpa using hy
      · exact (Nat.le_mul_of_pos_right selected.prod
          (by positivity : 0 < previous ^ 2)).trans_lt hslack
      · exact hproduct
  | cons factor extension ih =>
      have hfactorPos := hpositive factor (by simp)
      have hfactorLe := hbound factor (by simp)
      have hfactorLt : factor < y := hfactorLe.trans_lt hpreviousLt
      have hpair := List.pairwise_cons.mp hordered
      rw [iwaniecLowerContinuationTerm] at hterm
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨
            iwaniecCubicEvenRestriction y selected factor)
      · rw [if_pos hselect] at hterm
        have hchild :
            iwaniecLowerContinuationTerm r
              (iwaniecCubicEvenRestriction y)
              (selected ++ [factor]) extension ≠ 0 := by
          simpa using hterm
        have hresult := ih (selected := selected ++ [factor])
          (previous := factor) hfactorPos hfactorLt
          (iwaniecCubicPrefixInvariant_extend hpreviousPos
            hpreviousLt hfactorPos hfactorLe hinvariant hselect
          ) (by
            intro next hnext
            exact hpositive next (by simp [hnext])) (by
            intro next hnext
            exact hpair.1 next hnext) hpair.2 hchild
        simpa [List.append_assoc] using hresult
      · rw [if_neg hselect] at hterm
        exact (hterm rfl).elim

theorem iwaniecDescendingFactors_positive
    (factors : Finset Nat) (hprime : ∀ p ∈ factors, Nat.Prime p) :
    ∀ p ∈ iwaniecDescendingFactors factors, 0 < p := by
  intro p hp
  have hpMem : p ∈ factors := by
    simpa [iwaniecDescendingFactors] using hp
  exact (hprime p hpMem).pos

theorem iwaniecDescendingFactors_prod
    (factors : Finset Nat) :
    (iwaniecDescendingFactors factors).prod = ∏ p ∈ factors, p := by
  calc
    (iwaniecDescendingFactors factors).prod =
        (↑(iwaniecDescendingFactors factors) : Multiset Nat).prod := rfl
    _ = factors.val.prod := congrArg Multiset.prod
      (Finset.sort_eq factors (fun left right : Nat => right ≤ left))
    _ = ∏ p ∈ factors, p := Finset.prod_val factors

/-- Cubic support of the literal Iwaniec coefficient. -/
theorem iwaniecCubicLowerMoebiusInt_ne_zero_imp_lt
    {r y n : Nat} (hy : 1 < y)
    (hfactorLt : ∀ p ∈ n.primeFactors, p < y)
    (hcoeff : iwaniecCubicLowerMoebiusInt r y n ≠ 0) :
    n < y := by
  by_cases hn1 : n = 1
  · simpa [hn1] using hy
  have hsquare : Squarefree n := by
    by_contra hnotSquare
    exact hcoeff (by simp [iwaniecCubicLowerMoebiusInt, hnotSquare])
  have hfactorNonempty : n.primeFactors.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hprod : n = 1 := by
      rw [← Nat.prod_primeFactors_of_squarefree hsquare, hzero]
      simp
    exact hn1 hprod
  let ordered := iwaniecDescendingFactors n.primeFactors
  have horderedNonempty : ordered ≠ [] := by
    intro hnil
    have hsets := congrArg List.toFinset hnil
    have htoFinset : ordered.toFinset = n.primeFactors := by
      simp [ordered, iwaniecDescendingFactors]
    rw [htoFinset] at hsets
    exact hfactorNonempty.ne_empty hsets
  obtain ⟨first, tail, horderedEq⟩ := List.exists_cons_of_ne_nil horderedNonempty
  have hfirstMem : first ∈ ordered := by
    rw [horderedEq]
    simp
  have hfirstLt : first < y := by
    apply hfactorLt first
    simpa [ordered, iwaniecDescendingFactors] using hfirstMem
  have hpositive : ∀ p ∈ ordered, 0 < p := by
    apply iwaniecDescendingFactors_positive
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hbound : ∀ p ∈ ordered, p ≤ first := by
    intro p hp
    have hpair : ordered.Pairwise (fun left right : Nat => right ≤ left) := by
      exact Finset.pairwise_sort n.primeFactors
        (fun left right : Nat => right ≤ left)
    rw [horderedEq] at hp hpair
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · exact (List.pairwise_cons.mp hpair).1 p hp
  have hterm :
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        ordered ≠ 0 := by
    simpa [iwaniecCubicLowerMoebiusInt, hsquare, ordered] using hcoeff
  have hprodLt := iwaniecLowerContinuationTerm_ne_zero_prod_lt
    r y first [] ordered hy (hpositive first hfirstMem) hfirstLt
    (iwaniecCubicPrefixInvariant_nil y first) hpositive hbound
    (Finset.pairwise_sort n.primeFactors
      (fun left right : Nat => right ≤ left)) hterm
  rw [List.nil_append, iwaniecDescendingFactors_prod,
    Nat.prod_primeFactors_of_squarefree hsquare] at hprodLt
  exact hprodLt

theorem iwaniecCubicLowerMoebius_ne_zero_imp_lt
    {r y n : Nat} (hy : 1 < y)
    (hfactorLt : ∀ p ∈ n.primeFactors, p < y)
    (hcoeff : iwaniecCubicLowerMoebius r y n ≠ 0) :
    n < y := by
  have hcoeffInt : iwaniecCubicLowerMoebiusInt r y n ≠ 0 := by
    intro hzero
    apply hcoeff
    simp [iwaniecCubicLowerMoebius, hzero]
  exact iwaniecCubicLowerMoebiusInt_ne_zero_imp_lt hy hfactorLt
    hcoeffInt

end

end Erdos1212Kernel
