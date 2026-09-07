import Erdos1212Kernel.AlgebraicCorridorCofactors
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-!
The maximal nonvanishing minor of the same integer evaluation matrix in
Lemma 5.1. The properties of its rank that are used in the paper are proved
here: a nonzero selected minor and vanishing of every one-order-larger
minor. Laplace expansion formalizes the paper's "hence every row" step.
-/

theorem corridorMinor_rows_injective {r c t : ℕ}
    (M : Matrix (Fin r) (Fin c) ℤ) (rows : Fin t → Fin r) (cols : Fin t → Fin c)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j heq
  by_contra hij
  apply hdet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  exact congrArg (fun a => M a (cols k)) heq

theorem corridorMinor_cols_injective {r c t : ℕ}
    (M : Matrix (Fin r) (Fin c) ℤ) (rows : Fin t → Fin r) (cols : Fin t → Fin c)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective cols := by
  intro i j heq
  by_contra hij
  apply hdet
  apply Matrix.det_zero_of_column_eq hij
  intro k
  exact congrArg (M (rows k)) heq

theorem corridorMinor_order_le_rows {r c t : ℕ}
    (M : Matrix (Fin r) (Fin c) ℤ) (rows : Fin t → Fin r) (cols : Fin t → Fin c)
    (hdet : (M.submatrix rows cols).det ≠ 0) : t ≤ r := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective rows (corridorMinor_rows_injective M rows cols hdet)

/-- Maximality is produced for every rectangular integer matrix, including rank zero. -/
theorem corridor_exists_maximal_minor {r : ℕ}
    (M : Matrix (Fin r) (Fin (r + 1)) ℤ) :
    ∃ t : ℕ, t ≤ r ∧ ∃ rows : Fin t → Fin r, ∃ cols : Fin t → Fin (r + 1),
      Function.Injective rows ∧ Function.Injective cols ∧
      (M.submatrix rows cols).det ≠ 0 ∧
      ∀ (rows' : Fin (t + 1) → Fin r) (cols' : Fin (t + 1) → Fin (r + 1)),
        (M.submatrix rows' cols').det = 0 := by
  classical
  let P : ℕ → Prop := fun t =>
    ∃ rows : Fin t → Fin r, ∃ cols : Fin t → Fin (r + 1),
      (M.submatrix rows cols).det ≠ 0
  have hzero : P 0 := by
    refine ⟨Fin.elim0, Fin.elim0, ?_⟩
    simp
  let t := Nat.findGreatest P r
  have ht : P t := Nat.findGreatest_spec (Nat.zero_le r) hzero
  obtain ⟨rows, cols, hdet⟩ := ht
  refine ⟨t, Nat.findGreatest_le r, rows, cols,
    corridorMinor_rows_injective M rows cols hdet,
    corridorMinor_cols_injective M rows cols hdet, hdet, ?_⟩
  intro rows' cols'
  by_contra hnonzero
  have hbound := corridorMinor_order_le_rows M rows' cols' hnonzero
  have htoo := Nat.le_findGreatest hbound (show P (t + 1) from ⟨rows', cols', hnonzero⟩)
  change t + 1 ≤ t at htoo
  omega

/-- The complete bounded signed-minor vector on selected distinct columns.
The polynomial construction will extend these coefficients by zero on all
other monomials, exactly as in the paper. -/
theorem corridor_exists_bounded_minor_kernel {r d : ℕ} {R : ℝ}
    (M : Matrix (Fin r) (Fin (r + 1)) ℤ) (hR : 1 ≤ R)
    (hM : ∀ i j, |(M i j : ℝ)| ≤ R ^ d) :
    ∃ t : ℕ, t ≤ r ∧ ∃ cols : Fin (t + 1) → Fin (r + 1),
      ∃ weight : Fin (t + 1) → ℤ,
        Function.Injective cols ∧ weight ≠ 0 ∧
        (∀ i, ∑ j, M i (cols j) * weight j = 0) ∧
        (∀ j, |(weight j : ℝ)| ≤ (r.factorial : ℝ) * R ^ (d * r)) := by
  classical
  obtain ⟨t, htr, rows, oldCols, _hrows, hcols, hdet, hmax⟩ :=
    corridor_exists_maximal_minor M
  have hextra : ∃ extra : Fin (r + 1), extra ∉ Set.range oldCols := by
    by_contra hnone
    push_neg at hnone
    have hsurj : Function.Surjective oldCols := hnone
    have hcard := Fintype.card_le_of_surjective oldCols hsurj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨extra, hextra⟩ := hextra
  let cols : Fin (t + 1) → Fin (r + 1) := Fin.cons extra oldCols
  let A : Matrix (Fin t) (Fin (t + 1)) ℤ := M.submatrix rows cols
  let weight : Fin (t + 1) → ℤ := corridorCofactorVector A
  have hcols' : Function.Injective cols := Fin.cons_injective_of_injective hextra hcols
  have hminor : (A.submatrix id (0 : Fin (t + 1)).succAbove).det ≠ 0 := by
    simpa only [A, cols, Matrix.submatrix, Fin.succAbove_zero, Fin.cons_succ, id_eq] using hdet
  refine ⟨t, htr, cols, weight, hcols', corridorCofactorVector_ne_zero_of_minor A 0 hminor, ?_, ?_⟩
  · intro i
    change (∑ j, (fun j => M i (cols j)) j * corridorCofactorVector A j) = 0
    rw [corridorCofactorVector_dot_eq_border_det]
    have hborder :
        (Fin.cons (fun j => M i (cols j)) A : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ) =
          M.submatrix (Fin.cons i rows) cols := by
      ext j k
      cases j using Fin.cases <;> simp [A, Matrix.submatrix]
    rw [hborder]
    exact hmax (Fin.cons i rows) cols
  · intro j
    have hlocal := corridorCofactorVector_height_bound A
      (fun i k => hM (rows i) (cols k)) j
    have hfactorial : (t.factorial : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le htr
    have hpower : R ^ (d * t) ≤ R ^ (d * r) :=
      pow_le_pow_right₀ hR (Nat.mul_le_mul_left d htr)
    exact hlocal.trans (mul_le_mul hfactorial hpower
      (pow_nonneg (zero_le_one.trans hR) _) (Nat.cast_nonneg _))

end

end Erdos1212Kernel
