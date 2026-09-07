namespace Erdos1212Kernel

/-!
The unchanged target for Erdős Problem 1212.

This is intentionally stated independently of the legacy connector route.
Every point lies strictly above the boundary strips, is visible, and has at
least one composite coordinate.  Consecutive points are unit grid neighbours,
and the path leaves every finite coordinate box.
-/

structure LatticePoint where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

def Composite (n : Nat) : Prop :=
  ∃ a b : Nat, 1 < a ∧ 1 < b ∧ n = a * b

def Visible (p : LatticePoint) : Prop :=
  Nat.gcd p.x p.y = 1

def SafePoint (p : LatticePoint) : Prop :=
  1 < p.x ∧ 1 < p.y ∧ Visible p ∧ (Composite p.x ∨ Composite p.y)

def Adjacent (p q : LatticePoint) : Prop :=
  (q.x = p.x + 1 ∧ q.y = p.y) ∨
  (p.x = q.x + 1 ∧ q.y = p.y) ∨
  (q.y = p.y + 1 ∧ q.x = p.x) ∨
  (p.y = q.y + 1 ∧ q.x = p.x)

def GoesToInfinity (P : Nat → LatticePoint) : Prop :=
  ∀ B : Nat, ∃ t : Nat, B ≤ (P t).x ∨ B ≤ (P t).y

def SafeInfinitePath (P : Nat → LatticePoint) : Prop :=
  (∀ t : Nat, SafePoint (P t)) ∧
  (∀ t : Nat, Adjacent (P t) (P (t + 1))) ∧
  GoesToInfinity P

def Erdos1212FullClose : Prop :=
  ∃ P : Nat → LatticePoint, SafeInfinitePath P

end Erdos1212Kernel
