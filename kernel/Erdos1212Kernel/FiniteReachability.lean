import Mathlib.Combinatorics.SimpleGraph.Paths
import Erdos1212Kernel.FinitePrefixCertificate

namespace Erdos1212Kernel

theorem adjacent_symm {p q : LatticePoint} : Adjacent p q -> Adjacent q p := by
  intro h
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl ⟨h.1, h.2.symm⟩)
  · exact Or.inl ⟨h.1, h.2.symm⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.symm⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.symm⟩))

theorem adjacent_irrefl (p : LatticePoint) : ¬ Adjacent p p := by
  intro h
  rcases h with h | h | h | h <;> omega

def latticeGraph : SimpleGraph LatticePoint where
  Adj := Adjacent
  symm := fun _ _ => adjacent_symm
  loopless := { irrefl := fun p => adjacent_irrefl p }

theorem exists_gridDirection_of_adjacent {p q : LatticePoint}
    (h : Adjacent p q) : exists direction, gridStep p direction = q := by
  rcases h with h | h | h | h
  · refine ⟨.east, ?_⟩
    exact LatticePoint.ext (by simpa [gridStep] using h.1.symm)
      (by simpa [gridStep] using h.2.symm)
  · refine ⟨.west, ?_⟩
    apply LatticePoint.ext
    · simp [gridStep]
      omega
    · simpa [gridStep] using h.2.symm
  · refine ⟨.north, ?_⟩
    exact LatticePoint.ext (by simpa [gridStep] using h.2.symm)
      (by simpa [gridStep] using h.1.symm)
  · refine ⟨.south, ?_⟩
    apply LatticePoint.ext
    · simpa [gridStep] using h.2.symm
    · simp [gridStep]
      omega

noncomputable def gridDirectionOfAdjacent {p q : LatticePoint}
    (h : Adjacent p q) : GridDirection :=
  (exists_gridDirection_of_adjacent h).choose

theorem gridDirectionOfAdjacent_spec {p q : LatticePoint}
    (h : Adjacent p q) :
    gridStep p (gridDirectionOfAdjacent h) = q :=
  (exists_gridDirection_of_adjacent h).choose_spec

noncomputable def walkCode {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish) :
    Fin walk.length -> GridDirection :=
  fun t => gridDirectionOfAdjacent (walk.adj_getVert_succ t.isLt)

theorem codedPoint_walkCode {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish) (t : Nat)
    (ht : t <= walk.length) :
    codedPoint start (walkCode walk) t = walk.getVert t := by
  induction t with
  | zero => simp [codedPoint]
  | succ t ih =>
      have hstep : t < walk.length := by omega
      rw [codedPoint_succ start (walkCode walk) hstep, ih (by omega)]
      exact gridDirectionOfAdjacent_spec (walk.adj_getVert_succ hstep)

def ArbitrarilyFarSafeReachable (start : LatticePoint) : Prop :=
  forall bound, exists finish : LatticePoint,
    (bound <= finish.x \/ bound <= finish.y) /\
    exists walk : latticeGraph.Walk start finish,
      forall p, p ∈ walk.support -> SafePoint p

theorem fullClose_of_arbitrarily_far_safe_reachable
    (start : LatticePoint) (hreached : ArbitrarilyFarSafeReachable start) :
    Erdos1212FullClose := by
  apply fullClose_of_arbitrarily_far_simple_safe_codes start
  intro bound
  obtain ⟨finish, hfar, walk, hwalkSafe⟩ := hreached bound
  let path : latticeGraph.Walk start finish := walk.toPath
  have pathIsPath : path.IsPath := by
    exact walk.toPath.property
  have pathSupport : path.support ⊆ walk.support := by
    exact walk.support_toPath_subset
  let code : Fin path.length -> GridDirection := walkCode path
  refine ⟨path.length, code, ?_, ?_⟩
  · constructor
    · intro t ht
      rw [show codedPoint start code t = path.getVert t by
        exact codedPoint_walkCode path t ht]
      exact hwalkSafe _ (pathSupport (path.getVert_mem_support t))
    · intro s t hs ht hst heq
      apply hst
      apply pathIsPath.getVert_injOn hs ht
      rw [← codedPoint_walkCode path s hs,
        ← codedPoint_walkCode path t ht]
      exact heq
  · simpa [code, path, codedPoint_walkCode path path.length (Nat.le_refl _)]
      using hfar

end Erdos1212Kernel
