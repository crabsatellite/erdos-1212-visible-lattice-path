import Erdos1212Kernel.AlgebraicCorridorConstrainedPrefixes

namespace Erdos1212Kernel
noncomputable section

/-- Loop erasure and Koenig extraction preserve both the vertex carrier and
the actual walked edges. No induced-graph enlargement is used. -/
theorem corridor_ray_of_arbitrarily_far_constrained_walks
    (start : LatticePoint) (S : LatticePoint → Prop)
    (E : LatticePoint → LatticePoint → Prop)
    (hfar : ∀ bound, ∃ finish : LatticePoint,
      (bound ≤ finish.x ∨ bound ≤ finish.y) ∧
      ∃ w : latticeGraph.Walk start finish,
        (∀ p ∈ w.support, SafePoint p ∧ S p) ∧
        (∀ p q, w.toSubgraph.Adj p q → E p q)) :
    ∃ P : ℕ → LatticePoint, Function.Injective P ∧
      (∀ t, SafePoint (P t)) ∧ (∀ t, Adjacent (P t) (P (t + 1))) ∧
      (∀ t, S (P t)) ∧ (∀ t, E (P t) (P (t + 1))) := by
  classical
  apply corridor_ray_of_arbitrarily_far_constrained_codes start S E
  intro bound
  obtain ⟨finish, hf, walk, hw, he⟩ := hfar bound
  let path : latticeGraph.Walk start finish := walk.toPath
  have hpath : path.IsPath := walk.toPath.property
  have hsupport : path.support ⊆ walk.support := walk.support_toPath_subset
  have hedges {p q : LatticePoint} (h : path.toSubgraph.Adj p q) :
      walk.toSubgraph.Adj p q := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] at h ⊢
    exact walk.edges_toPath_subset h
  let code := walkCode path
  have hget (t : ℕ) (ht : t ≤ path.length) : codedPoint start code t = path.getVert t :=
    codedPoint_walkCode path t ht
  refine ⟨path.length, code, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro t ht
    rw [hget t ht]
    exact (hw _ (hsupport (path.getVert_mem_support t))).1
  · intro s t hs ht hst heq
    apply hst
    apply hpath.getVert_injOn hs ht
    rwa [← hget s hs, ← hget t ht]
  · intro t ht
    rw [hget t ht]
    exact (hw _ (hsupport (path.getVert_mem_support t))).2
  · intro t ht
    rw [hget t ht.le, hget (t + 1) (by omega)]
    exact he _ _ (hedges (path.toSubgraph_adj_getVert ht))
  · simpa [hget path.length le_rfl] using hf

end
end Erdos1212Kernel
