import Erdos1212Kernel.IwaniecCubicFirstPrimeRecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Literal real-valued level recursion `y_(i+1)=y_i/p_(i+1)` from page 6.
The offset records whether the next cubic constraint is active. -/
def iwaniecCubicRealAdmissible : Nat → Real → List Nat → Prop
  | _offset, _level, [] => True
  | offset, level, p :: tail =>
      (Even offset ∨ (p : Real) ^ 3 < level) ∧
        iwaniecCubicRealAdmissible (offset + 1) (level / p) tail

theorem iwaniecCubicRestriction_iff_realLevel
    (y p : Nat) (selected : List Nat) (hprod : 0 < selected.prod) :
    iwaniecCubicEvenRestriction y selected p = true ↔
      (p : Real) ^ 3 < (y : Real) / selected.prod := by
  simp only [iwaniecCubicEvenRestriction, decide_eq_true_eq]
  rw [lt_div_iff₀ (by exact_mod_cast hprod : (0 : Real) < selected.prod)]
  norm_cast

theorem iwaniecCubicRealLevel_append_singleton
    (y : Real) (selected : List Nat) (p : Nat) :
    (y / (selected.prod : Real)) / (p : Real) =
      y / ((selected ++ [p]).prod : Real) := by
  simp [List.prod_append, Nat.cast_mul, div_div]

/-- Exact transport from the existing natural polynomial carrier to the
paper's real levels.  The rank bound is exposed, not absorbed into the
analytic predicate; all selected factors must be positive. -/
theorem iwaniecAdmissibleExtension_iff_realLevel
    (r y : Nat) (selected extension : List Nat)
    (hselected : selected.length < 2 * r)
    (hprod : 0 < selected.prod)
    (hpositive : ∀ p ∈ extension, 0 < p) :
    iwaniecAdmissibleExtension r (iwaniecCubicEvenRestriction y)
        selected extension ↔
      selected.length + extension.length < 2 * r ∧
        iwaniecCubicRealAdmissible selected.length
          ((y : Real) / selected.prod) extension := by
  induction extension generalizing selected with
  | nil => simp [iwaniecAdmissibleExtension, iwaniecCubicRealAdmissible, hselected]
  | cons p tail ih =>
      have hp : 0 < p := hpositive p (by simp)
      have htail : ∀ q ∈ tail, 0 < q := fun q hq => hpositive q (by simp [hq])
      have hchildProd : 0 < (selected ++ [p]).prod := by
        simpa using Nat.mul_pos hprod hp
      have hlength : (selected ++ [p]).length = selected.length + 1 := by simp
      have hscale := iwaniecCubicRealLevel_append_singleton (y : Real) selected p
      have hcondition :
          (Even selected.length ∨ iwaniecCubicEvenRestriction y selected p) ↔
          (Even selected.length ∨ (p : Real) ^ 3 < (y : Real) / selected.prod) := by
        rw [iwaniecCubicRestriction_iff_realLevel y p selected hprod]
      constructor
      · intro h
        obtain ⟨hdepth, hallow, hchild⟩ := h
        obtain ⟨hfull, hreal⟩ := (ih (selected ++ [p])
          (by simpa only [hlength] using hdepth) hchildProd htail).1 hchild
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons, hlength] at hfull ⊢
          omega
        · refine ⟨hcondition.1 hallow, ?_⟩
          rw [hscale]
          simpa only [hlength] using hreal
      · rintro ⟨hfull, hreal⟩
        have hdepth : (selected ++ [p]).length < 2 * r := by
          simp only [List.length_cons] at hfull
          rw [hlength]
          omega
        refine ⟨by simpa only [hlength] using hdepth, hcondition.2 hreal.1, ?_⟩
        apply (ih (selected ++ [p]) hdepth hchildProd htail).2
        constructor
        · simp only [List.length_cons] at hfull
          rw [hlength]
          omega
        · rw [hlength, ← hscale]
          exact hreal.2

theorem iwaniecCubicAdmissibleOrdered_iff_realLevel
    {r : Nat} (hr : 0 < r) (y : Nat) (ordered : List Nat)
    (hpositive : ∀ p ∈ ordered, 0 < p) :
    iwaniecCubicAdmissibleOrdered r y ordered ↔
      ordered.length < 2 * r ∧ iwaniecCubicRealAdmissible 0 y ordered := by
  simpa [iwaniecCubicAdmissibleOrdered] using
    iwaniecAdmissibleExtension_iff_realLevel r y [] ordered
      (by simp; omega) (by simp) hpositive

/-- Removing the first reference prime changes the level to the exact real
quotient and flips the constrained parity.  There is no rounded quotient. -/
theorem iwaniecCubicAdmissibleOrdered_cons_iff_realLevel
    {r : Nat} (hr : 0 < r) (y p : Nat) (tail : List Nat)
    (hp : 0 < p) (hpositive : ∀ q ∈ tail, 0 < q) :
    iwaniecCubicAdmissibleOrdered r y (p :: tail) ↔
      tail.length + 1 < 2 * r ∧
        iwaniecCubicRealAdmissible 1 ((y : Real) / p) tail := by
  rw [iwaniecCubicAdmissibleOrdered_iff_realLevel hr y (p :: tail)]
  · simp [iwaniecCubicRealAdmissible]
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hpositive q hq

end

end Erdos1212Kernel
