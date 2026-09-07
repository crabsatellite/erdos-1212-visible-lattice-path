import Erdos1212Kernel.FiniteReachability

namespace Erdos1212Kernel

/-! The existing finite-simple-prefix Koenig argument, retaining its actual
injectivity proof and the carrier/edge constraints required by the paper. -/
theorem corridor_ray_of_finite_simple_prefix_system
    (S : LatticePoint → Prop) (E : LatticePoint → LatticePoint → Prop)
    {Prefix : Nat -> Type*}
    [Finite (Prefix 0)] [forall n, Nonempty (Prefix n)]
    (project : {i j : Nat} -> i <= j -> Prefix j -> Prefix i)
    (project_refl : forall {i} (pfx : Prefix i),
      project (Nat.le_refl i) pfx = pfx)
    (project_trans : forall {i j k} (hij : i <= j) (hjk : j <= k)
      (pfx : Prefix k),
      project hij (project hjk pfx) = project (hij.trans hjk) pfx)
    (finite_fibres : forall i (pfx : Prefix i),
      Set.Finite {longer : Prefix (i + 1) |
        project (Nat.le_add_right i 1) longer = pfx})
    (point : forall n, Prefix n -> Nat -> LatticePoint)
    (point_project : forall {i j} (hij : i <= j) (pfx : Prefix j)
      (t : Nat), t <= i ->
      point i (project hij pfx) t = point j pfx t)
    (safe : forall n (pfx : Prefix n) (t : Nat), t <= n ->
      SafePoint (point n pfx t))
    (adjacent : forall n (pfx : Prefix n) (t : Nat), t < n ->
      Adjacent (point n pfx t) (point n pfx (t + 1)))
    (simple : forall n (pfx : Prefix n) (s t : Nat),
      s <= n -> t <= n -> s ≠ t ->
      point n pfx s ≠ point n pfx t) :
    (∀ n (pfx : Prefix n) t, t ≤ n → S (point n pfx t)) →
    (∀ n (pfx : Prefix n) t, t < n → E (point n pfx t) (point n pfx (t + 1))) →
    ∃ path : ℕ → LatticePoint, Function.Injective path ∧
      (∀ t, SafePoint (path t)) ∧ (∀ t, Adjacent (path t) (path (t + 1))) ∧
      (∀ t, S (path t)) ∧ (∀ t, E (path t) (path (t + 1))) := by
  intro hS hE
  let projection : {i j : Nat} -> i <= j -> Prefix j -> Prefix i :=
    fun hij pfx => project hij pfx
  have projection_refl : forall {i} (pfx : Prefix i),
      projection (by rfl) pfx = pfx := by
    intro i pfx
    simpa [projection] using project_refl pfx
  have projection_trans : forall {i j k} (hij : i <= j) (hjk : j <= k)
      (pfx : Prefix k),
      projection hij (projection hjk pfx) =
        projection (hij.trans hjk) pfx := by
    intro i j k hij hjk pfx
    simpa [projection] using project_trans hij hjk pfx
  have projection_finite : forall i (pfx : Prefix i),
      Set.Finite {longer : Prefix (i + 1) |
        projection (Nat.le_add_right i 1) longer = pfx} := by
    intro i pfx
    simpa [projection] using finite_fibres i pfx
  have hsections : exists chosen : (i : Nat) -> Prefix i,
      forall {i j} (hij : i <= j),
        projection hij (chosen j) = chosen i := by
    apply exists_seq_forall_proj_of_forall_finite projection
    · intro i pfx
      exact projection_refl pfx
    · intro i j k hij hjk pfx
      exact projection_trans hij hjk pfx
    · intro i pfx
      exact projection_finite i pfx
  obtain ⟨chosen, coherent⟩ := hsections
  let path : Nat -> LatticePoint := fun t => point t (chosen t) t
  have path_eq_later (i j : Nat) (hij : i <= j) :
      path i = point j (chosen j) i := by
    have hpoint := point_project hij (chosen j) i (Nat.le_refl i)
    have hcoherent : project hij (chosen j) = chosen i := by
      simpa [projection] using coherent hij
    rw [hcoherent] at hpoint
    simpa [path] using hpoint
  have path_safe : forall t, SafePoint (path t) := by
    intro t
    exact safe t (chosen t) t (Nat.le_refl t)
  have path_adjacent : forall t, Adjacent (path t) (path (t + 1)) := by
    intro t
    have hstep := adjacent (t + 1) (chosen (t + 1)) t (by omega)
    rw [path_eq_later t (t + 1) (by omega)]
    simpa [path] using hstep
  have path_injective : Function.Injective path := by
    intro i j hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hdistinct := simple j (chosen j) i j
        (Nat.le_of_lt hlt) (Nat.le_refl j) hne
      exact hdistinct <| by
        rw [← path_eq_later i j (Nat.le_of_lt hlt)]
        simpa [path] using hij
    · have hji : j ≠ i := fun h => hne h.symm
      have hdistinct := simple i (chosen i) j i
        (Nat.le_of_lt hgt) (Nat.le_refl i) hji
      exact hdistinct <| by
        rw [← path_eq_later j i (Nat.le_of_lt hgt)]
        simpa [path] using hij.symm
  refine ⟨path, path_injective, path_safe, path_adjacent, ?_, ?_⟩
  · intro t
    exact hS t (chosen t) t (Nat.le_refl t)
  · intro t
    have hstep := hE (t + 1) (chosen (t + 1)) t (by omega)
    rw [path_eq_later t (t + 1) (by omega)]
    simpa [path] using hstep

end Erdos1212Kernel

