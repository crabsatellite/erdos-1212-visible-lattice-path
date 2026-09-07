import Mathlib.NumberTheory.Chebyshev
import Erdos1212Kernel.Target

namespace Erdos1212Kernel

open scoped Nat.Prime

/-!
The sparse baseline used by the relative close route.

For a scale `N`, a root is encoded by a prime `p` in `(N, 4 * N]` and an
integer `k` in `[2, N / 2]`; its lattice point is `(p, 2 * k)`.  Thus the
second coordinate is composite and lies strictly below the prime column.
The entire construction is finite and its cardinality is an exact product.
-/

def corridorPrimes (N : Nat) : Finset Nat :=
  (Nat.primesLE (4 * N)).filter fun p => N < p

def corridorHeights (N : Nat) : Finset Nat :=
  Finset.Icc 2 (N / 2)

def primeCorridorRoots (N : Nat) : Finset (Nat × Nat) :=
  corridorPrimes N ×ˢ corridorHeights N

def primeCorridorPoint (r : Nat × Nat) : LatticePoint :=
  ⟨r.1, 2 * r.2⟩

def primeColumnPoint (p j : Nat) : LatticePoint :=
  ⟨p, j⟩

theorem composite_iff_not_prime {n : Nat} (hn : 2 ≤ n) :
    Composite n ↔ ¬ Nat.Prime n := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩ hp
    apply ((Nat.not_prime_iff_exists_mul_eq hn).2 ?_) hp
    refine ⟨a, b, ?_, ?_, hab.symm⟩
    · nlinarith
    · nlinarith
  · intro hnPrime
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq hn).1 hnPrime
    have ha0 : a ≠ 0 := by
      intro h
      simp [h] at hab
      omega
    have hb0 : b ≠ 0 := by
      intro h
      simp [h] at hab
      omega
    have ha1 : a ≠ 1 := by
      intro h
      simp [h] at hab
      omega
    have hb1 : b ≠ 1 := by
      intro h
      simp [h] at hab
      omega
    exact ⟨a, b, (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ha0, ha1⟩),
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hb0, hb1⟩), hab.symm⟩

theorem primeColumnPoint_visible {p j : Nat} (hp : Nat.Prime p)
    (hj0 : j ≠ 0) (hjp : j < p) :
    Visible (primeColumnPoint p j) := by
  exact Nat.coprime_of_lt_prime hj0 hjp hp

theorem primeColumn_bad_height_is_prime {p j : Nat} (hp : Nat.Prime p)
    (hj : 2 ≤ j) (hjp : j < p)
    (hbad : ¬ SafePoint (primeColumnPoint p j)) :
    Nat.Prime j := by
  by_contra hjPrime
  apply hbad
  change 1 < p ∧ 1 < j ∧ Nat.gcd p j = 1 ∧
    (Composite p ∨ Composite j)
  refine ⟨hp.one_lt, by omega,
    primeColumnPoint_visible hp (by omega) hjp, ?_⟩
  exact Or.inr ((composite_iff_not_prime hj).2 hjPrime)

theorem corridorPrimes_eq_sdiff (N : Nat) :
    corridorPrimes N = Nat.primesLE (4 * N) \ Nat.primesLE N := by
  ext p
  by_cases hp : Nat.Prime p
  · simp [corridorPrimes, Nat.mem_primesLE, hp]
  · simp [corridorPrimes, Nat.mem_primesLE, hp]

theorem corridorPrimes_card (N : Nat) :
    (corridorPrimes N).card =
      Nat.primeCounting (4 * N) - Nat.primeCounting N := by
  rw [corridorPrimes_eq_sdiff]
  have hsub : Nat.primesLE N ⊆ Nat.primesLE (4 * N) :=
    Nat.primesLE_mono (by omega)
  rw [Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hsub]
  simp only [Nat.primesLE_card_eq_primeCounting]

theorem corridorHeights_card (N : Nat) :
    (corridorHeights N).card = N / 2 - 1 := by
  simp [corridorHeights]

theorem primeCorridorRoots_card (N : Nat) :
    (primeCorridorRoots N).card =
      (Nat.primeCounting (4 * N) - Nat.primeCounting N) * (N / 2 - 1) := by
  simp [primeCorridorRoots, corridorPrimes_card, corridorHeights_card]

theorem primeCorridorPoint_injective : Function.Injective primeCorridorPoint := by
  rintro ⟨p, k⟩ ⟨p', k'⟩ h
  have hx := congrArg LatticePoint.x h
  have hy := congrArg LatticePoint.y h
  simp only [primeCorridorPoint] at hx hy
  congr
  omega

theorem primeCorridorPoint_safe {N p k : Nat}
    (hroot : (p, k) ∈ primeCorridorRoots N) :
    SafePoint (primeCorridorPoint (p, k)) := by
  rcases Finset.mem_product.mp hroot with ⟨hpMem, hkMem⟩
  have hpData := Finset.mem_filter.mp hpMem
  have hp : Nat.Prime p := (Nat.mem_primesLE.mp hpData.1).2
  have hpLower : N < p := hpData.2
  have hk : 2 ≤ k := (Finset.mem_Icc.mp hkMem).1
  have hkUpper : k ≤ N / 2 := (Finset.mem_Icc.mp hkMem).2
  have hkp : 2 * k < p := by omega
  have hcoprime : Nat.Coprime p (2 * k) :=
    Nat.coprime_of_lt_prime (by omega) hkp hp
  change 1 < p ∧ 1 < 2 * k ∧ Nat.gcd p (2 * k) = 1 ∧
    (Composite p ∨ Composite (2 * k))
  refine ⟨hp.one_lt, by omega, ?_, ?_⟩
  · exact hcoprime
  · exact Or.inr ⟨2, k, by omega, hk, rfl⟩

end Erdos1212Kernel
