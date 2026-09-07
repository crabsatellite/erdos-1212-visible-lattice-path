import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace Erdos1212Kernel

/-!
The real-cutoff roughness and short-band argument of Sections 1 and 3,
consumed by the distinct-divisor step in Lemma 4.2 of the published paper.
No assertion about how many rough composites exist is made in this module.
-/

/-- The paper's literal real-cutoff roughness convention: every prime factor exceeds z. -/
def CorridorRough (z : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)

/-- A common prime would divide a positive difference smaller than the roughness cutoff. -/
theorem corridorRough_coprime_of_dist_lt {z : ℝ} {a b : ℕ}
    (ha : CorridorRough z a) (hab : a ≠ b)
    (hdist : (Nat.dist a b : ℝ) < z) : a.Coprime b := by
  by_contra hcoprime
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcoprime
  have hpd : p ∣ Nat.dist a b := by
    unfold Nat.dist
    exact dvd_add (Nat.dvd_sub hpa hpb) (Nat.dvd_sub hpb hpa)
  have hpdist : (p : ℝ) ≤ (Nat.dist a b : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.dist_pos_of_ne hab) hpd
  exact (not_lt_of_ge (hpdist.trans hdist.le)) (ha p hp hpa)

/-- Lemma 3.2: the actual B consecutive integers are indexed by [lower, lower+B). -/
theorem corridorRough_coprime_of_mem_block {z : ℝ} {lower B a b : ℕ}
    (ha : CorridorRough z a) (hab : a ≠ b)
    (haL : lower ≤ a) (haU : a < lower + B)
    (hbL : lower ≤ b) (hbU : b < lower + B)
    (hB : (B : ℝ) < z) : a.Coprime b := by
  apply corridorRough_coprime_of_dist_lt ha hab
  have hdist : Nat.dist a b < B := by
    rcases le_total a b with hab' | hba'
    · rw [Nat.dist_eq_sub_of_le hab']
      omega
    · rw [Nat.dist_eq_sub_of_le_right hba']
      omega
  exact (by exact_mod_cast hdist : (Nat.dist a b : ℝ) < (B : ℝ)).trans hB

/-- A selected family of distinct rough rows in the same short band is pairwise coprime. -/
theorem corridorRough_rows_pairwise_coprime {ι : Type*} {z : ℝ} {lower B : ℕ}
    (row : ι → ℕ) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hband : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hB : (B : ℝ) < z) : Pairwise (fun i j => (row i).Coprime (row j)) := by
  intro i j hij
  exact corridorRough_coprime_of_mem_block (hrough i)
    (fun heq => hij (hrow heq)) (hband i).1 (hband i).2
    (hband j).1 (hband j).2 hB

/-- Lemma 4.2: choosing one prime factor on each row gives genuinely distinct primes. -/
theorem corridorRough_selected_primes_injective {ι : Type*} {z : ℝ} {lower B : ℕ}
    (row prime : ι → ℕ) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hband : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hB : (B : ℝ) < z)
    (hprime : ∀ i, (prime i).Prime) (hdiv : ∀ i, prime i ∣ row i) :
    Function.Injective prime := by
  intro i j heq
  by_contra hij
  have hcoprime := corridorRough_rows_pairwise_coprime row hrow hrough hband hB hij
  have hdj : prime i ∣ row j := by simpa only [heq] using hdiv j
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨prime i, hprime i, hdiv i, hdj⟩) hcoprime

end Erdos1212Kernel
