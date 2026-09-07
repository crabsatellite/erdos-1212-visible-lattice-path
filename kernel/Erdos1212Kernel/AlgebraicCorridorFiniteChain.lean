import Erdos1212Kernel.AlgebraicCorridorAdjacentProduction
import Erdos1212Kernel.AlgebraicCorridorHeightGrid

namespace Erdos1212Kernel
noncomputable section

/-- Concatenate the actual crossing-to-crossing connections, reversing only
the supplied horizontal crossing to match its right endpoint. -/
theorem corridor_finite_crossing_chain (P : LatticePoint → Prop)
    (a b : ℕ → LatticePoint) (crossing : ∀ i, CorridorSafeWalk (a i) (b i))
    (hc : ∀ i p, p ∈ (crossing i).walk.support → P p)
    (hlink : ∀ i, ∃ v : CorridorSafeWalk (a i) (b (i + 1)),
      ∀ p ∈ v.walk.support, P p) :
    ∀ n, ∃ v : CorridorSafeWalk (b 0) (b n), ∀ p ∈ v.walk.support, P p := by
  intro n
  induction n with
  | zero =>
      refine ⟨⟨SimpleGraph.Walk.nil, ?_⟩, ?_⟩
      · intro p hp
        have he : p = b 0 := by simpa using hp
        subst p
        exact (crossing 0).safe _ (crossing 0).walk.end_mem_support
      · intro p hp
        have he : p = b 0 := by simpa using hp
        subst p
        exact hc 0 _ (crossing 0).walk.end_mem_support
  | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨link, hlink⟩ := hlink n
      let w := (v.walk.append (crossing n).walk.reverse).append link.walk
      have hmem : ∀ p ∈ w.support,
          p ∈ v.walk.support ∨ p ∈ (crossing n).walk.support ∨ p ∈ link.walk.support := by
        intro p hp
        simp only [w, SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
        tauto
      have hsafe : ∀ p ∈ w.support, SafePoint p := by
        intro p hp
        rcases hmem p hp with hp | hp | hp
        · exact v.safe p hp
        · exact (crossing n).safe p hp
        · exact link.safe p hp
      refine ⟨⟨w, hsafe⟩, ?_⟩
      intro p hp
      rcases hmem p hp with hp | hp | hp
      · exact hv p hp
      · exact hc n p hp
      · exact hlink p hp

namespace CorridorScale

/-- Every finite prefix of the paper's selected-height crossings is connected
inside the same direction corridor. In particular take heightGridLast to
reach the added endpoint at height 2N. -/
theorem eventually_heightGrid_crossings_connected :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ M : ℕ, (M : ℝ) = N →
      ∀ (a b : ℕ → LatticePoint) (crossing : ∀ i, CorridorSafeWalk (a i) (b i)),
      (∀ i, (a i).x = (corridorSquare N α (heightGrid M (squareStep N) i)).left) →
      (∀ i, (b i).x = (corridorSquare N α (heightGrid M (squareStep N) i)).right) →
      (∀ i p, p ∈ (crossing i).walk.support →
        (corridorSquare N α (heightGrid M (squareStep N) i)).Contains p) →
      ∀ n, ∃ v : CorridorSafeWalk (b 0) (b n),
        ∀ p ∈ v.walk.support, directionCorridor N α p := by
  filter_upwards [eventually_adjacent_crossings_connected,
    eventually_corridorSquare_contained] with N hconnect hcont
  intro α hα havoid M hM a b crossing ha hb hc
  have hlow (i : ℕ) : N ≤ (heightGrid M (squareStep N) i : ℝ) := by
    conv_lhs => rw [← hM]
    exact_mod_cast (heightGrid_bounds M (squareStep N) i).1
  have hhigh (i : ℕ) : (heightGrid M (squareStep N) i : ℝ) ≤ 2 * N := by
    conv_rhs => rw [← hM]
    exact_mod_cast (heightGrid_bounds M (squareStep N) i).2
  apply corridor_finite_crossing_chain (directionCorridor N α) a b crossing
  · intro i p hp
    exact (hcont α hα _ (hlow i) (hhigh i) p (hc i p hp)).1
  · intro i
    obtain ⟨hmono, hstep⟩ := heightGrid_step M (squareStep N) i
    exact hconnect α hα havoid _ _ (hlow i) (hhigh (i + 1)) hmono hstep
      (crossing i) (crossing (i + 1)) (ha i) (hb i) (ha (i + 1)) (hb (i + 1))
      (hc i) (hc (i + 1))

theorem eventually_heightGrid_safe_chain :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ M : ℕ, (M : ℝ) = N →
      ∃ (a b : ℕ → LatticePoint) (crossing : ∀ i, CorridorSafeWalk (a i) (b i)),
      (∀ i, (a i).x = (corridorSquare N α (heightGrid M (squareStep N) i)).left) ∧
      (∀ i, (b i).x = (corridorSquare N α (heightGrid M (squareStep N) i)).right) ∧
      (∀ i p, p ∈ (crossing i).walk.support →
        (corridorSquare N α (heightGrid M (squareStep N) i)).Contains p) ∧
      ∀ n, ∃ v : CorridorSafeWalk (b 0) (b n),
        ∀ p ∈ v.walk.support, directionCorridor N α p := by
  filter_upwards [eventually_heightGrid_crossings_connected,
    eventually_corridorSquare_safe_horizontal] with N hchain hprod
  intro α hα havoid M hM
  have hex (i : ℕ) :
      (corridorSquare N α (heightGrid M (squareStep N) i)).SafeHorizontalCrossing := by
    apply hprod α hα havoid
    · conv_lhs => rw [← hM]
      exact_mod_cast (heightGrid_bounds M (squareStep N) i).1
    · conv_rhs => rw [← hM]
      exact_mod_cast (heightGrid_bounds M (squareStep N) i).2
  choose a b ha hb w hw using hex
  let crossing (i : ℕ) : CorridorSafeWalk (a i) (b i) :=
    ⟨w i, fun p hp => (hw i p hp).2⟩
  have hc : ∀ i p, p ∈ (crossing i).walk.support →
      (corridorSquare N α (heightGrid M (squareStep N) i)).Contains p :=
    fun i p hp => (hw i p hp).1
  exact ⟨a, b, crossing, ha, hb, hc,
    hchain α hα havoid M hM a b crossing ha hb hc⟩

end CorridorScale
end
end Erdos1212Kernel
