import Mathlib
import Erdos1212Kernel.Target

namespace Erdos1212Kernel

@[ext]
theorem LatticePoint.ext {p q : LatticePoint}
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  simp_all

/-!
Kőnig extraction at the original theorem boundary.

An element of `Prefix n` represents a simple safe walk with `n` steps from
one fixed root.  The projection maps forget the final steps.  If such a
prefix exists at every depth and every one-step projection fibre is finite,
Kőnig's lemma selects compatible prefixes.  Their diagonal points form an
actual infinite path.  Simplicity forces that path to leave every finite
lattice box.
-/
theorem fullClose_of_finite_simple_prefix_system
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
    Erdos1212FullClose := by
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
  have path_escape : GoesToInfinity path := by
    intro bound
    by_contra hbounded
    push Not at hbounded
    let intoBox : Fin (bound * bound + 1) -> Fin bound × Fin bound :=
      fun t =>
        (⟨(path t.val).x, (hbounded t.val).1⟩,
          ⟨(path t.val).y, (hbounded t.val).2⟩)
    have intoBox_injective : Function.Injective intoBox := by
      intro left right heq
      apply Fin.ext
      apply path_injective
      exact LatticePoint.ext
        (congr_arg (fun value => value.1.val) heq)
        (congr_arg (fun value => value.2.val) heq)
    have hcard := Fintype.card_le_of_injective intoBox intoBox_injective
    simp only [Fintype.card_fin, Fintype.card_prod] at hcard
    omega
  exact ⟨path, path_safe, path_adjacent, path_escape⟩

end Erdos1212Kernel
