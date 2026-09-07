import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

open scoped BigOperators

/-!
The signed integer evaluation in Lemma 5.1 and Proposition 5.2.
Fin 2 indexes the paper's two polynomial variables. The original root and
each offset remain integer coordinate pairs throughout the argument.
-/

theorem corridorPolynomial_eval_modEq {σ : Type*} (H : MvPolynomial σ ℤ)
    {q : ℤ} {a b : σ → ℤ} (hab : ∀ i, a i ≡ b i [ZMOD q]) :
    MvPolynomial.eval a H ≡ MvPolynomial.eval b H [ZMOD q] := by
  refine MvPolynomial.induction_on
    (motive := fun P => MvPolynomial.eval a P ≡ MvPolynomial.eval b P [ZMOD q]) H ?_ ?_ ?_
  · intro c
    simpa only [MvPolynomial.eval_C] using (Int.ModEq.refl (n := q) c)
  · intro P Q hP hQ
    simpa only [MvPolynomial.eval_add] using hP.add hQ
  · intro P i hP
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hP.mul (hab i)

/-- A common coordinate divisor at root + offset divides evaluation at the negative root. -/
theorem corridorPolynomial_dvd_eval_neg_root (H : MvPolynomial (Fin 2) ℤ)
    (root offset : Fin 2 → ℤ) (q : ℤ)
    (hzero : MvPolynomial.eval offset H = 0)
    (hdiv : ∀ i, q ∣ root i + offset i) :
    q ∣ MvPolynomial.eval (fun i => -root i) H := by
  have hmod : ∀ i, offset i ≡ -root i [ZMOD q] := by
    intro i
    apply Int.modEq_iff_dvd.mpr
    convert (dvd_neg.mpr (hdiv i)) using 1 <;> ring
  have heval := corridorPolynomial_eval_modEq H hmod
  rw [hzero] at heval
  exact Int.modEq_zero_iff_dvd.mp heval.symm

/-- The product uses all distinct selected primes; no repeated factor is discarded. -/
theorem corridorPolynomial_prime_product_dvd_eval_neg_root
    {ι : Type*} [Fintype ι] (H : MvPolynomial (Fin 2) ℤ)
    (root : Fin 2 → ℤ) (offset : ι → Fin 2 → ℤ) (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hzero : ∀ i, MvPolynomial.eval (offset i) H = 0)
    (hdiv : ∀ i j, (q i : ℤ) ∣ root j + offset i j) :
    ((∏ i, q i : ℕ) : ℤ) ∣ MvPolynomial.eval (fun j => -root j) H := by
  apply Int.natCast_dvd.mpr
  apply Fintype.prod_dvd_of_isRelPrime
  · intro i j hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (Nat.coprime_primes (hq i) (hq j)).mpr
    exact fun heq => hij (hinj heq)
  · intro i
    exact Int.natCast_dvd.mp
      (corridorPolynomial_dvd_eval_neg_root H root (offset i) (q i) (hzero i) (hdiv i))

/-- The paper's final integer-size comparison forces zero, with its signed evaluation unchanged. -/
theorem corridorPolynomial_eval_eq_zero_of_prime_product_large
    {ι : Type*} [Fintype ι] (H : MvPolynomial (Fin 2) ℤ)
    (root : Fin 2 → ℤ) (offset : ι → Fin 2 → ℤ) (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hzero : ∀ i, MvPolynomial.eval (offset i) H = 0)
    (hdiv : ∀ i j, (q i : ℤ) ∣ root j + offset i j)
    (hsize : (MvPolynomial.eval (fun j => -root j) H).natAbs < ∏ i, q i) :
    MvPolynomial.eval (fun j => -root j) H = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (corridorPolynomial_prime_product_dvd_eval_neg_root H root offset q hq hinj hzero hdiv)
  simpa only [Int.natAbs_natCast] using hsize

end Erdos1212Kernel
