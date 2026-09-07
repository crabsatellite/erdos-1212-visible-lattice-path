import Erdos1212Kernel.AlgebraicCorridorRayExtraction

namespace Erdos1212Kernel
noncomputable section

def CorridorConstrainedCode (start : LatticePoint)
    (S : LatticePoint → Prop) (E : LatticePoint → LatticePoint → Prop)
    {n : ℕ} (code : Fin n → GridDirection) : Prop :=
  SimpleSafeCode start code ∧
    (∀ t, t ≤ n → S (codedPoint start code t)) ∧
    (∀ t, t < n → E (codedPoint start code t) (codedPoint start code (t + 1)))

theorem corridorConstrainedCode_restrict (start : LatticePoint)
    (S : LatticePoint → Prop) (E : LatticePoint → LatticePoint → Prop)
    {i j : ℕ} (hij : i ≤ j) (code : Fin j → GridDirection)
    (h : CorridorConstrainedCode start S E code) :
    CorridorConstrainedCode start S E (restrictCode hij code) := by
  refine ⟨simpleSafeCode_restrict start hij code h.1, ?_, ?_⟩
  · intro t ht
    rw [codedPoint_restrict start hij code t ht]
    exact h.2.1 t (ht.trans hij)
  · intro t ht
    rw [codedPoint_restrict start hij code t ht.le,
      codedPoint_restrict start hij code (t + 1) (by omega)]
    exact h.2.2 t (lt_of_lt_of_le ht hij)

def CorridorConstrainedPrefix (start : LatticePoint)
    (S : LatticePoint → Prop) (E : LatticePoint → LatticePoint → Prop) (n : ℕ) :=
  {code : Fin n → GridDirection // CorridorConstrainedCode start S E code}

def corridorConstrainedProject (start : LatticePoint)
    (S : LatticePoint → Prop) (E : LatticePoint → LatticePoint → Prop)
    {i j : ℕ} (hij : i ≤ j) (p : CorridorConstrainedPrefix start S E j) :
    CorridorConstrainedPrefix start S E i :=
  ⟨restrictCode hij p.val, corridorConstrainedCode_restrict start S E hij p.val p.property⟩

theorem corridor_ray_of_arbitrarily_long_constrained_codes
    (start : LatticePoint) (S : LatticePoint → Prop)
    (E : LatticePoint → LatticePoint → Prop)
    (hlong : ∀ n, ∃ code : Fin n → GridDirection, CorridorConstrainedCode start S E code) :
    ∃ P : ℕ → LatticePoint, Function.Injective P ∧
      (∀ t, SafePoint (P t)) ∧ (∀ t, Adjacent (P t) (P (t + 1))) ∧
      (∀ t, S (P t)) ∧ (∀ t, E (P t) (P (t + 1))) := by
  classical
  let Prefix := CorridorConstrainedPrefix start S E
  letI : ∀ n, Nonempty (Prefix n) := fun n =>
    ⟨⟨(hlong n).choose, (hlong n).choose_spec⟩⟩
  letI : ∀ n, Finite (Prefix n) := fun n =>
    Finite.of_injective Subtype.val Subtype.val_injective
  apply corridor_ray_of_finite_simple_prefix_system S E
    (Prefix := Prefix) (project := fun hij p => corridorConstrainedProject start S E hij p)
    (point := fun _ p t => codedPoint start p.val t)
  · intro i p
    apply Subtype.ext
    funext t
    rfl
  · intro i j k hij hjk p
    apply Subtype.ext
    funext t
    rfl
  · intro i p
    exact Set.toFinite _
  · intro i j hij p t ht
    exact codedPoint_restrict start hij p.val t ht
  · intro n p t ht
    exact p.property.1.1 t ht
  · intro n p t ht
    rw [codedPoint_succ start p.val ht]
    exact adjacent_gridStep _ _ (p.property.1.1 t ht.le)
  · intro n p s t hs ht hst
    exact p.property.1.2 s t hs ht hst
  · intro n p t ht
    exact p.property.2.1 t ht
  · intro n p t ht
    exact p.property.2.2 t ht

theorem corridor_ray_of_arbitrarily_far_constrained_codes
    (start : LatticePoint) (S : LatticePoint → Prop)
    (E : LatticePoint → LatticePoint → Prop)
    (hfar : ∀ bound, ∃ n, ∃ code : Fin n → GridDirection,
      CorridorConstrainedCode start S E code ∧
      (bound ≤ (codedPoint start code n).x ∨ bound ≤ (codedPoint start code n).y)) :
    ∃ P : ℕ → LatticePoint, Function.Injective P ∧
      (∀ t, SafePoint (P t)) ∧ (∀ t, Adjacent (P t) (P (t + 1))) ∧
      (∀ t, S (P t)) ∧ (∀ t, E (P t) (P (t + 1))) := by
  apply corridor_ray_of_arbitrarily_long_constrained_codes start S E
  intro depth
  obtain ⟨n, code, hc, hbound⟩ := hfar (max start.x start.y + depth)
  have hdepth : depth ≤ n := by
    rcases hbound with hx | hy
    · have h := codedPoint_x_le start code n
      have hs := le_max_left start.x start.y
      omega
    · have h := codedPoint_y_le start code n
      have hs := le_max_right start.x start.y
      omega
  exact ⟨restrictCode hdepth code, corridorConstrainedCode_restrict start S E hdepth code hc⟩

end
end Erdos1212Kernel
