import Erdos1212Kernel.IwaniecCubicRealTotalCount

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Product cutoff in the two real-level phases.  The unrestricted phase
needs the literal initial cutoff `p < y`; the cubic-first phase supplies its
own slack.  This discharges the `d < y` condition in the paper's counts. -/
theorem iwaniecCubicRealAdmissible_product_bounds
    (ordered : List Nat) (hpositive : ∀ p ∈ ordered, 0 < p)
    (hordered : ordered.Pairwise fun p q => q ≤ p)
    (level : Real) (hlevel : 1 < level) :
    (iwaniecCubicRealAdmissible 0 level ordered →
      (∀ p ∈ ordered, (p : Real) < level) → (ordered.prod : Real) < level) ∧
    (iwaniecCubicRealAdmissible 1 level ordered → (ordered.prod : Real) < level) := by
  induction ordered generalizing level with
  | nil => simp [hlevel]
  | cons p tail ih =>
      have hp : 0 < p := hpositive p (by simp)
      have hpReal : (0 : Real) < p := by exact_mod_cast hp
      have hpOne : (1 : Real) ≤ p := by exact_mod_cast hp
      have htailPos : ∀ q ∈ tail, 0 < q := fun q hq => hpositive q (by simp [hq])
      have htailOrdered := (List.pairwise_cons.mp hordered).2
      have htailBound := (List.pairwise_cons.mp hordered).1
      constructor
      · intro hreal hbound
        have hpLt : (p : Real) < level := hbound p (by simp)
        have hchildLevel : 1 < level / p := by
          rw [lt_div_iff₀ hpReal, one_mul]
          exact hpLt
        have hchild : iwaniecCubicRealAdmissible 1 (level / p) tail := hreal.2
        have hprod := (ih htailPos htailOrdered (level / p) hchildLevel).2 hchild
        have hmul := (lt_div_iff₀ hpReal).1 hprod
        simpa [List.prod_cons, Nat.cast_mul, mul_comm] using hmul
      · intro hreal
        have hcubic : (p : Real) ^ 3 < level := by
          simpa [iwaniecCubicRealAdmissible] using hreal.1
        have hpSquare : (p : Real) ^ 2 ≤ (p : Real) ^ 3 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hpOne) (sq_nonneg (p : Real))]
        have hpSqLower : (p : Real) ≤ (p : Real) ^ 2 := by nlinarith
        have hpLt : (p : Real) < level := hpSqLower.trans_lt (hpSquare.trans_lt hcubic)
        have hchildLevel : 1 < level / p := by
          rw [lt_div_iff₀ hpReal, one_mul]
          exact hpLt
        have hpChild : (p : Real) < level / p := by
          rw [lt_div_iff₀ hpReal]
          nlinarith [hpSquare.trans_lt hcubic]
        have hchild : iwaniecCubicRealAdmissible 0 (level / p) tail := by
          exact (iwaniecCubicRealAdmissible_add_two 0 (level / p) tail).1 hreal.2
        have hprod := (ih htailPos htailOrdered (level / p) hchildLevel).1 hchild
          (fun q hq => (show (q : Real) ≤ p by
            exact_mod_cast htailBound q hq).trans_lt hpChild)
        have hmul := (lt_div_iff₀ hpReal).1 hprod
        simpa [List.prod_cons, Nat.cast_mul, mul_comm] using hmul

def iwaniecCubicRealProductCount (offset : Nat) (level : Real)
    (factors : List Nat) (k : Nat) : Nat := by
  classical
  exact ((factors.sublistsLen k).filter fun extension =>
    decide (iwaniecCubicRealAdmissible offset level extension ∧
      (extension.prod : Real) < level)).length

theorem iwaniecCubicRealProductCount_eq_of_cutoff
    (level : Real) (factors : List Nat) (k : Nat) (hlevel : 1 < level)
    (hpositive : ∀ p ∈ factors, 0 < p)
    (hordered : factors.Pairwise fun p q => q ≤ p)
    (hcutoff : ∀ p ∈ factors, (p : Real) < level) :
    iwaniecCubicRealProductCount 0 level factors k =
      iwaniecCubicRealCount 0 level factors k := by
  classical
  unfold iwaniecCubicRealProductCount iwaniecCubicRealCount
  apply congrArg List.length
  apply List.filter_congr
  intro extension hext
  have hsub := (List.mem_sublistsLen.mp hext).1
  have hpos := fun p hp => hpositive p (hsub.subset hp)
  have hord := hordered.sublist hsub
  have hbound := fun p hp => hcutoff p (hsub.subset hp)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h,
    (iwaniecCubicRealAdmissible_product_bounds extension hpos hord level hlevel).1 h hbound⟩⟩

theorem iwaniecCubicRealProductCount_eq_cubicFirst
    (level : Real) (factors : List Nat) (k : Nat) (hlevel : 1 < level)
    (hpositive : ∀ p ∈ factors, 0 < p)
    (hordered : factors.Pairwise fun p q => q ≤ p) :
    iwaniecCubicRealProductCount 1 level factors k =
      iwaniecCubicRealCount 1 level factors k := by
  classical
  unfold iwaniecCubicRealProductCount iwaniecCubicRealCount
  apply congrArg List.length
  apply List.filter_congr
  intro extension hext
  have hsub := (List.mem_sublistsLen.mp hext).1
  have hpos := fun p hp => hpositive p (hsub.subset hp)
  have hord := hordered.sublist hsub
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h,
    (iwaniecCubicRealAdmissible_product_bounds extension hpos hord level hlevel).2 h⟩⟩

end

end Erdos1212Kernel
