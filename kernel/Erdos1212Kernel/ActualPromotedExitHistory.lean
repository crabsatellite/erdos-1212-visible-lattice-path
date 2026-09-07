import Erdos1212Kernel.ActualPromotedComponentConfinement
import Erdos1212Kernel.PrimeCorridorOuterBoundaryAnchor

namespace Erdos1212Kernel

/-!
# Without-replacement first-exit histories on an actual trace

This file formalizes the monotone promoted-component exhaustion used by the
terminal route.  A trace vertex is either an actual prime--prime site, an
already paid divisor site, or the first site carrying one new least common
prime label.  In the last case that label is inserted once and the unchanged
trace is resumed.  The resulting label word is squarefree as a word: no
phase can be recruited twice.

After the final insertion every vertex of the original trace belongs to one
actual promoted star component.  Consequently the complete trace receives
one final component window, rather than a product of intermediate component
marks.
-/

/-- The exact first-exit scan of a vertex list.  `oldLabel` retains an
already paid phase; `freshLabel` inserts the least common prime at its first
occurrence and continues with the enlarged state. -/
inductive ActualPromotedExitHistory :
    Finset Nat → List LatticePoint → List Nat → Prop
  | nil (R : Finset Nat) : ActualPromotedExitHistory R [] []
  | primePair
      {R : Finset Nat} {point : LatticePoint}
      {points : List LatticePoint} {labels : List Nat}
      (hpoint : PrimePair point)
      (htail : ActualPromotedExitHistory R points labels) :
      ActualPromotedExitHistory R (point :: points) labels
  | oldLabel
      {R : Finset Nat} {point : LatticePoint}
      {points : List LatticePoint} {labels : List Nat}
      (hpoint : ¬ Visible point)
      (hnotAnchor : ¬ PrimePair point)
      (hpaid : commonPrimeLabel point ∈ R)
      (htail : ActualPromotedExitHistory R points labels) :
      ActualPromotedExitHistory R (point :: points) labels
  | freshLabel
      {R : Finset Nat} {point : LatticePoint}
      {points : List LatticePoint} {labels : List Nat}
      (hpoint : ¬ Visible point)
      (hnotAnchor : ¬ PrimePair point)
      (hfresh : commonPrimeLabel point ∉ R)
      (htail : ActualPromotedExitHistory
        (insert (commonPrimeLabel point) R) points labels) :
      ActualPromotedExitHistory R (point :: points)
        (commonPrimeLabel point :: labels)

/-- Every finite list of actual deleted vertices admits the exact first-exit
scan from an arbitrary initial paid state. -/
theorem exists_actualPromotedExitHistory
    (R : Finset Nat) (points : List LatticePoint)
    (hdeleted : ∀ point ∈ points,
      PrimePair point ∨ ¬ Visible point) :
    ∃ labels, ActualPromotedExitHistory R points labels := by
  classical
  induction points generalizing R with
  | nil =>
      exact ⟨[], ActualPromotedExitHistory.nil R⟩
  | cons point points ih =>
      have hhead : PrimePair point ∨ ¬ Visible point :=
        hdeleted point (by simp)
      have htailDeleted : ∀ other ∈ points,
          PrimePair other ∨ ¬ Visible other := by
        intro other hother
        exact hdeleted other (by simp [hother])
      by_cases hprimePair : PrimePair point
      · obtain ⟨labels, hhistory⟩ := ih R htailDeleted
        exact ⟨labels,
          ActualPromotedExitHistory.primePair hprimePair hhistory⟩
      · have hnotVisible : ¬ Visible point := hhead.resolve_left hprimePair
        by_cases hpaid : commonPrimeLabel point ∈ R
        · obtain ⟨labels, hhistory⟩ := ih R htailDeleted
          exact ⟨labels,
            ActualPromotedExitHistory.oldLabel
              hnotVisible hprimePair hpaid hhistory⟩
        · obtain ⟨labels, hhistory⟩ :=
            ih (insert (commonPrimeLabel point) R) htailDeleted
          exact ⟨commonPrimeLabel point :: labels,
            ActualPromotedExitHistory.freshLabel
              hnotVisible hprimePair hpaid hhistory⟩

theorem ActualPromotedExitHistory.labels_fresh_from_initial
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    ∀ q ∈ labels, q ∉ R := by
  induction hhistory with
  | nil => simp
  | primePair _ _ ih => exact ih
  | oldLabel _ _ _ _ ih => exact ih
  | freshLabel hpoint hnotAnchor hfresh htail ih =>
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hfresh
      · exact fun hqR ↦ ih q hq (Finset.mem_insert_of_mem hqR)

theorem ActualPromotedExitHistory.labels_prime
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    ∀ q ∈ labels, Nat.Prime q := by
  induction hhistory with
  | nil => simp
  | primePair _ _ ih => exact ih
  | oldLabel _ _ _ _ ih => exact ih
  | freshLabel hpoint _ _ _ ih =>
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact (commonPrimeLabel_spec_of_not_visible hpoint).1
      · exact ih q hq

/-- Every recruited label is tied to the literal trace vertex at which its
least common prime was first exposed. -/
theorem ActualPromotedExitHistory.labels_witnessed
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    ∀ q ∈ labels,
      ∃ point ∈ points,
        ¬ PrimePair point ∧ ¬ Visible point ∧
          q = commonPrimeLabel point := by
  induction hhistory with
  | nil => simp
  | @primePair R point points labels hpoint htail ih =>
      intro q hq
      obtain ⟨witness, hwitness, hnotAnchor, hnotVisible, hlabel⟩ := ih q hq
      exact ⟨witness, by simp [hwitness], hnotAnchor, hnotVisible, hlabel⟩
  | @oldLabel R point points labels hpoint hnotAnchor hpaid htail ih =>
      intro q hq
      obtain ⟨witness, hwitness, hnotAnchor, hnotVisible, hlabel⟩ := ih q hq
      exact ⟨witness, by simp [hwitness], hnotAnchor, hnotVisible, hlabel⟩
  | @freshLabel R point points labels hpoint hnotAnchor hfresh htail ih =>
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨point, by simp, hnotAnchor, hpoint, rfl⟩
      · obtain ⟨witness, hwitness, hnotAnchor', hnotVisible, hlabel⟩ := ih q hq
        exact ⟨witness, by simp [hwitness], hnotAnchor', hnotVisible, hlabel⟩

/-- Every non-anchor divisor vertex on the unchanged trace carries either an
initially paid label or one of the labels recruited by the canonical scan. -/
theorem ActualPromotedExitHistory.divisor_label_paid_or_recruited
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    ∀ point ∈ points,
      ¬ PrimePair point → ¬ Visible point →
        commonPrimeLabel point ∈ R ∨
          commonPrimeLabel point ∈ labels := by
  induction hhistory with
  | nil => simp
  | @primePair R point points labels hpoint htail ih =>
      intro other hother hnotAnchor hnotVisible
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact (hnotAnchor hpoint).elim
      · exact ih other hother hnotAnchor hnotVisible
  | @oldLabel R point points labels hpoint hnotAnchor hpaid htail ih =>
      intro other hother hotherNotAnchor hotherNotVisible
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact Or.inl hpaid
      · exact ih other hother hotherNotAnchor hotherNotVisible
  | @freshLabel R point points labels hpoint hnotAnchor hfresh htail ih =>
      intro other hother hotherNotAnchor hotherNotVisible
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact Or.inr (by simp)
      · rcases ih other hother hotherNotAnchor hotherNotVisible with
          hpaid | hrecruited
        · rcases Finset.mem_insert.mp hpaid with hsame | hpaid
          · exact Or.inr (by simp [hsame])
          · exact Or.inl hpaid
        · exact Or.inr (by simp [hrecruited])

/-- Exact no-recharge accounting: the recruited word is precisely the set of
least common-prime labels occurring at non-anchor divisor vertices and not
already present in the incoming paid state. -/
theorem ActualPromotedExitHistory.label_mem_iff
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) (q : Nat) :
    q ∈ labels ↔
      q ∉ R ∧
        ∃ point ∈ points,
          ¬ PrimePair point ∧ ¬ Visible point ∧
            q = commonPrimeLabel point := by
  constructor
  · intro hq
    exact ⟨hhistory.labels_fresh_from_initial q hq,
      hhistory.labels_witnessed q hq⟩
  · rintro ⟨hqFresh, point, hpoint, hnotAnchor, hnotVisible, hlabel⟩
    have hpaid := hhistory.divisor_label_paid_or_recruited
      point hpoint hnotAnchor hnotVisible
    rw [← hlabel] at hpaid
    exact hpaid.resolve_left hqFresh

theorem ActualPromotedExitHistory.label_nodup
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    labels.Nodup := by
  induction hhistory with
  | nil => simp
  | primePair _ _ ih => exact ih
  | oldLabel _ _ _ _ ih => exact ih
  | @freshLabel R point points labels hpoint hnotAnchor hfresh htail ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih⟩
      intro hhead
      have htailFresh :=
        htail.labels_fresh_from_initial
          (commonPrimeLabel point) hhead
      exact htailFresh (Finset.mem_insert_self _ _)

/-- The final paid state attached to an exit history. -/
def promotedExitFinalLabels (R : Finset Nat) (labels : List Nat) :
    Finset Nat :=
  R ∪ labels.toFinset

/-- Every scanned vertex is genuinely present in the one final promoted
state. -/
theorem ActualPromotedExitHistory.promoted_of_mem
    {R : Finset Nat} {points : List LatticePoint} {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R points labels) :
    ∀ point ∈ points,
      ActualPromotedUnsafe (promotedExitFinalLabels R labels) point := by
  induction hhistory with
  | nil => simp
  | @primePair R point points labels hpoint htail ih =>
      intro other hother
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact Or.inl hpoint
      · exact ih other hother
  | @oldLabel R point points labels hpoint hnotAnchor hpaid htail ih =>
      intro other hother
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact Or.inr ⟨hpoint, Finset.mem_union_left _ hpaid⟩
      · exact ih other hother
  | @freshLabel R point points labels hpoint hnotAnchor hfresh htail ih =>
      let q := commonPrimeLabel point
      have hstate :
          promotedExitFinalLabels (insert q R) labels =
            promotedExitFinalLabels R (q :: labels) := by
        ext x
        simp only [promotedExitFinalLabels, Finset.mem_union,
          Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
        aesop
      intro other hother
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact Or.inr ⟨hpoint, by
          simp [promotedExitFinalLabels, q]⟩
      · rw [← hstate]
        exact ih other hother

/-- Every point of a promoted walk is reachable from its first point by the
corresponding prefix of the unchanged walk. -/
theorem actualPromotedStarReachable_of_mem_support
    {R : Finset Nat} {anchor finish point : LatticePoint}
    (walk : starLatticeGraph.Walk anchor finish)
    (hpromoted : ∀ other ∈ walk.support,
      ActualPromotedUnsafe R other)
    (hpoint : point ∈ walk.support) :
    ActualPromotedStarReachable R anchor point := by
  refine ⟨walk.takeUntil point hpoint, ?_⟩
  intro other hother
  exact hpromoted other (walk.support_takeUntil_subset hpoint hother)

/-- An actual deleted star trace has a canonical without-replacement label
history, and the complete unchanged trace lies in its one final promoted
component. -/
theorem exists_withoutReplacement_actualPromotedTraceHistory
    {R : Finset Nat} {anchor finish : LatticePoint}
    (walk : starLatticeGraph.Walk anchor finish)
    (hdeleted : ∀ point ∈ walk.support,
      PrimePair point ∨ ¬ Visible point) :
    ∃ labels,
      ActualPromotedExitHistory R walk.support labels ∧
      labels.Nodup ∧
      (∀ q ∈ labels, Nat.Prime q) ∧
      (∀ point ∈ walk.support,
        ActualPromotedStarReachable
          (promotedExitFinalLabels R labels) anchor point) := by
  obtain ⟨labels, hhistory⟩ :=
    exists_actualPromotedExitHistory R walk.support hdeleted
  have hpromoted := hhistory.promoted_of_mem
  refine ⟨labels, hhistory, hhistory.label_nodup,
    hhistory.labels_prime, ?_⟩
  intro point hpoint
  exact actualPromotedStarReachable_of_mem_support
    walk hpromoted hpoint

/-- The one-final-window consequence.  Its radius depends on the initial
paid-state size plus the number of genuinely new first exits, with no product
of intermediate component marks. -/
theorem ActualPromotedExitHistory.trace_mem_one_final_window
    {R : Finset Nat} {anchor finish : LatticePoint}
    {walk : starLatticeGraph.Walk anchor finish}
    {labels : List Nat}
    (hhistory : ActualPromotedExitHistory R walk.support labels)
    (hRPrime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime (R.card + labels.length) +
          uniformCompositeSurvivorGap (R.card + labels.length) + 1 ≤
        anchor.x)
    (hyLarge :
      Nat.nth Nat.Prime (R.card + labels.length) +
          uniformCompositeSurvivorGap (R.card + labels.length) + 1 ≤
        anchor.y) :
    ∀ point ∈ walk.support,
      point ∈ latticeWindow anchor
        (uniformCompositeSurvivorGap (R.card + labels.length)) := by
  let finalR := promotedExitFinalLabels R labels
  have hcard : finalR.card ≤ R.card + labels.length := by
    dsimp [finalR, promotedExitFinalLabels]
    exact (Finset.card_union_le R labels.toFinset).trans
      (Nat.add_le_add_left (List.toFinset_card_le labels) R.card)
  have hfinalPrime : ∀ q ∈ finalR, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqR | hqLabels
    · exact hRPrime q hqR
    · exact hhistory.labels_prime q (List.mem_toFinset.mp hqLabels)
  have hpromoted : ∀ point ∈ walk.support,
      ActualPromotedUnsafe finalR point := by
    simpa [finalR] using hhistory.promoted_of_mem
  intro point hpoint
  have hreachable : ActualPromotedStarReachable finalR anchor point :=
    actualPromotedStarReachable_of_mem_support walk hpromoted hpoint
  exact actualPromotedStarReachable_mem_latticeWindow
    hcard hfinalPrime hxLarge hyLarge hreachable

end Erdos1212Kernel
