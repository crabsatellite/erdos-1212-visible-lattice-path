import Erdos1212Kernel.RosserRestrictedLowerMoebius

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- The literal lower-sieve recursion in Iwaniec (1971), Lemma 1, equation
`(2.2)`.  `selected` stores the already selected factors in decreasing order and
`tail` the still available smaller factors.  Odd-numbered selections are
unrestricted.  An even-numbered selection is retained precisely when
`evenRestriction prefix factor` holds.  The depth cut `length < 2 * r` is the
odd Bonferroni truncation appearing in `(2.2)` and `(2.6)`. -/
def iwaniecLowerTreeSum
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool) :
    List α → List α → Int
  | _selected, [] => 1
  | selected, factor :: tail =>
      let skipped := iwaniecLowerTreeSum r evenRestriction selected tail
      if selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor) then
        skipped -
          iwaniecLowerTreeSum r evenRestriction
            (selected ++ [factor]) tail
      else
        skipped

/-- The two complementary sign invariants behind Iwaniec's lower sieve.

* At odd depth the continuation sum is nonnegative.
* At even depth, provided that an available factor remains, the continuation
  sum is nonpositive.

The proof is the paper's recursion rather than a cardinality surrogate.  The
smallest remaining factor supplies the terminal cancellation in the even
case; at odd depth an even child with a nonempty tail is already nonpositive.
-/
theorem iwaniecLowerTreeSum_parity_bounds
    {α : Type*} (r : Nat)
    (evenRestriction : List α → α → Bool) (tail : List α) :
    (∀ selected : List α,
        selected.length < 2 * r → Odd selected.length →
          0 ≤ iwaniecLowerTreeSum r evenRestriction selected tail) ∧
      (∀ selected : List α,
        selected.length < 2 * r → Even selected.length → tail ≠ [] →
          iwaniecLowerTreeSum r evenRestriction selected tail ≤ 0) := by
  induction tail with
  | nil =>
      constructor
      · intro selected _hdepth _hodd
        simp [iwaniecLowerTreeSum]
      · intro selected _hdepth _heven htail
        exact (htail rfl).elim
  | cons factor tail ih =>
      rcases ih with ⟨ihOdd, ihEven⟩
      constructor
      · intro selected hdepth hodd
        rw [iwaniecLowerTreeSum]
        by_cases hselect :
            selected.length + 1 < 2 * r ∧
              (Even selected.length ∨ evenRestriction selected factor)
        · rw [if_pos hselect]
          have hskip :
              0 ≤ iwaniecLowerTreeSum r evenRestriction selected tail :=
            ihOdd selected hdepth hodd
          by_cases htail : tail = []
          · subst tail
            simp [iwaniecLowerTreeSum]
          · have hchild :
                iwaniecLowerTreeSum r evenRestriction
                    (selected ++ [factor]) tail ≤ 0 := by
              apply ihEven
              · simpa using hselect.1
              · simpa using hodd.add_one
              · exact htail
            omega
        · rw [if_neg hselect]
          exact ihOdd selected hdepth hodd
      · intro selected hdepth heven _htail
        rw [iwaniecLowerTreeSum]
        have hnextDepth : selected.length + 1 < 2 * r := by
          obtain ⟨k, hk⟩ := heven
          omega
        have hselect :
            selected.length + 1 < 2 * r ∧
              (Even selected.length ∨ evenRestriction selected factor) :=
          ⟨hnextDepth, Or.inl heven⟩
        rw [if_pos hselect]
        by_cases htail : tail = []
        · subst tail
          simp [iwaniecLowerTreeSum]
        · have hskip :
              iwaniecLowerTreeSum r evenRestriction selected tail ≤ 0 :=
            ihEven selected hdepth heven htail
          have hchild :
              0 ≤ iwaniecLowerTreeSum r evenRestriction
                  (selected ++ [factor]) tail := by
            apply ihOdd
            · simpa using hnextDepth
            · simpa using heven.add_one
          omega

/-- Root form of Iwaniec's lower Bonferroni inequality.  It is uniform in the
actual even-position restriction, so the later cubic prefix cutoff can be
substituted without adding a new combinatorial premise. -/
theorem iwaniecLowerTreeSum_root_nonpos
    {α : Type*} (r : Nat) (hr : 0 < r)
    (evenRestriction : List α → α → Bool) (factors : List α)
    (hfactors : factors ≠ []) :
    iwaniecLowerTreeSum r evenRestriction [] factors ≤ 0 := by
  exact (iwaniecLowerTreeSum_parity_bounds
    r evenRestriction factors).2 [] (by simp [hr]) (by simp) hfactors

end

end Erdos1212Kernel
