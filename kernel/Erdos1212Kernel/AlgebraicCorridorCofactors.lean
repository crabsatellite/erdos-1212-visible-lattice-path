import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-!
The signed maximal minors of the t by (t+1) matrix in Lemma 5.1.
No full-rank assumption is hidden: nonvanishing of a selected minor is a
separate input, to be supplied by the maximal-rank selection producer.
-/

def corridorCofactorVector {t : ℕ}
    (A : Matrix (Fin t) (Fin (t + 1)) ℤ) (j : Fin (t + 1)) : ℤ :=
  (-1 : ℤ) ^ j.val * (A.submatrix id j.succAbove).det

/-- Laplace expansion identifies the signed-minor dot product with the bordered determinant. -/
theorem corridorCofactorVector_dot_eq_border_det {t : ℕ}
    (A : Matrix (Fin t) (Fin (t + 1)) ℤ) (row : Fin (t + 1) → ℤ) :
    (∑ j, row j * corridorCofactorVector A j) =
      Matrix.det (Fin.cons row A : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ) := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hminor :
      Matrix.submatrix (Fin.cons row A : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ)
          Fin.succ j.succAbove = A.submatrix id j.succAbove := by
    ext i k
    simp [Matrix.submatrix]
  rw [hminor]
  simp only [Fin.cons_zero, corridorCofactorVector]
  ring

/-- Each actual row is annihilated, by the determinant with that row repeated. -/
theorem corridorCofactorVector_annihilates_rows {t : ℕ}
    (A : Matrix (Fin t) (Fin (t + 1)) ℤ) (i : Fin t) :
    ∑ j, A i j * corridorCofactorVector A j = 0 := by
  rw [corridorCofactorVector_dot_eq_border_det]
  exact Matrix.det_zero_of_row_eq
    (M := (Fin.cons (A i) A : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ))
    (Fin.succ_ne_zero i).symm (by simp only [Fin.cons_zero, Fin.cons_succ])

theorem corridorCofactorVector_ne_zero_of_minor {t : ℕ}
    (A : Matrix (Fin t) (Fin (t + 1)) ℤ) (j : Fin (t + 1))
    (hminor : (A.submatrix id j.succAbove).det ≠ 0) :
    corridorCofactorVector A ≠ 0 := by
  have hj : corridorCofactorVector A j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0)) hminor
  intro hzero
  exact hj (congrFun hzero j)

/-- The paper's coefficient bound, from the existing exact factorial determinant bound. -/
theorem corridorCofactorVector_height_bound {t d : ℕ} {R : ℝ}
    (A : Matrix (Fin t) (Fin (t + 1)) ℤ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ R ^ d) (j : Fin (t + 1)) :
    |(corridorCofactorVector A j : ℝ)| ≤ (t.factorial : ℝ) * R ^ (d * t) := by
  have hdet := Matrix.det_le
    (A := (A.submatrix id j.succAbove).map (fun z : ℤ => (z : ℝ)))
    (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) (x := R ^ d)
    (fun i k => hA i (j.succAbove k))
  have habs : |(corridorCofactorVector A j : ℝ)| =
      |((A.submatrix id j.succAbove).det : ℝ)| := by
    simp [corridorCofactorVector, abs_mul, abs_pow]
  rw [habs, Int.cast_det]
  simpa only [Fintype.card_fin, nsmul_eq_mul, ← pow_mul] using hdet

end

end Erdos1212Kernel
