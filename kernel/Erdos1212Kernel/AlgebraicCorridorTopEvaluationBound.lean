import Erdos1212Kernel.AlgebraicCorridorHomogeneousEvaluation

namespace Erdos1212Kernel.CorridorScale

noncomputable section

theorem corridorTopPolynomial_eval_abs_le_homogeneousNumerator
    {N : ℝ} (hN : 0 < N) (F : MvPolynomial (Fin 2) ℤ)
    (hm : 0 < F.totalDegree) (hdegree : F.totalDegree ≤ degree N)
    (hheight : corridorPolynomialHeight F ≤ height N)
    {x y : ℕ} (hy : 0 < y) (hxTwo : (x : ℝ) ≤ 2 * (y : ℝ))
    (hyLower : N / 2 ≤ (y : ℝ))
    (hzero : MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0) :
    |(Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F)).eval
        ((x : ℝ) / (y : ℝ))| ≤ homogeneousNumerator N / N := by
  let lowerF := corridorLowerPolynomial F
  let m := F.totalDegree
  have hmPos : 0 < m := hm
  have hmOne : 1 ≤ m := hm
  have hlowerDegree : lowerF.totalDegree ≤ m - 1 := by
    exact corridorLowerPolynomial_totalDegree_le_pred F
  have hX : (1 : ℝ) ≤ 2 * (y : ℝ) := by
    have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith
  have hcoords : ∀ k : Fin 2,
      |(![(x : ℤ), (y : ℤ)] k : ℝ)| ≤ 2 * (y : ℝ) := by
    intro k
    fin_cases k
    · change |(x : ℝ)| ≤ 2 * (y : ℝ)
      rw [abs_of_nonneg (Nat.cast_nonneg x)]
      exact hxTwo
    · change |(y : ℝ)| ≤ 2 * (y : ℝ)
      rw [abs_of_nonneg (Nat.cast_nonneg y)]
      nlinarith
  have heval := corridor_polynomial_eval_abs_le lowerF hlowerDegree hX
    ![(x : ℤ), (y : ℤ)] hcoords
  have hmArith : m - 1 + 2 = m + 1 := by omega
  rw [hmArith] at heval
  have hlowerHeight : corridorPolynomialHeight lowerF ≤ height N :=
    (corridorLowerPolynomial_height_le F).trans hheight
  have hchoose : (m + 1).choose 2 ≤ (degree N + 2).choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  have hchooseScale : ((m + 1).choose 2 : ℝ) ≤ (rows N : ℝ) + 1 := by
    have hchooseR : ((m + 1).choose 2 : ℝ) ≤
        ((degree N + 2).choose 2 : ℝ) := by exact_mod_cast hchoose
    have hrows := congrArg (fun n : ℕ => (n : ℝ))
      (corridorInterpolationRowCount_succ (degree N))
    push_cast at hrows
    calc
      ((m + 1).choose 2 : ℝ) ≤
          ((degree N + 2).choose 2 : ℝ) := hchooseR
      _ = (corridorInterpolationRowCount (degree N) : ℝ) + 1 := hrows.symm
      _ = (rows N : ℝ) + 1 := rfl
  have hpowTwo : (2 : ℝ) ^ (m - 1) ≤ (2 : ℝ) ^ degree N := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hheightR : (corridorPolynomialHeight lowerF : ℝ) ≤
      (height N : ℝ) := by exact_mod_cast hlowerHeight
  have hyRPos : (0 : ℝ) < y := by exact_mod_cast hy
  have hpowEq : (2 * (y : ℝ)) ^ (m - 1) / (y : ℝ) ^ m =
      (2 : ℝ) ^ (m - 1) / (y : ℝ) := by
    rw [mul_pow]
    field_simp [pow_ne_zero _ hyRPos.ne']
    rw [pow_sub_one_mul hm.ne']
  have hscaled :
      (((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          (2 * (y : ℝ)) ^ (m - 1)) /
          (y : ℝ) ^ m ≤
        homogeneousNumerator N / N := by
    rw [show (((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          (2 * (y : ℝ)) ^ (m - 1)) /
          (y : ℝ) ^ m =
        ((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          ((2 * (y : ℝ)) ^ (m - 1) / (y : ℝ) ^ m) by ring,
      hpowEq]
    rw [show ((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          ((2 : ℝ) ^ (m - 1) / (y : ℝ)) =
        (((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          (2 : ℝ) ^ (m - 1)) / (y : ℝ) by ring]
    apply (div_le_div_iff₀ hyRPos hN).mpr
    unfold homogeneousNumerator
    have hNtwoY : N ≤ 2 * (y : ℝ) := by linarith
    have hleftNonneg : 0 ≤ ((m + 1).choose 2 : ℝ) *
        (corridorPolynomialHeight lowerF : ℝ) * (2 : ℝ) ^ (m - 1) := by
      positivity
    have hrightNonneg : 0 ≤ 2 * ((rows N : ℝ) + 1) *
        (2 : ℝ) ^ degree N * (height N : ℝ) := by positivity
    calc
      (((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          (2 : ℝ) ^ (m - 1)) * N ≤
        (((m + 1).choose 2 : ℝ) *
          (corridorPolynomialHeight lowerF : ℝ) *
          (2 : ℝ) ^ (m - 1)) * (2 * (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hNtwoY hleftNonneg
      _ ≤ (((rows N : ℝ) + 1) * (height N : ℝ) *
          (2 : ℝ) ^ degree N) * (2 * (y : ℝ)) := by
        gcongr
      _ = (2 * ((rows N : ℝ) + 1) * (2 : ℝ) ^ degree N *
          (height N : ℝ)) * (y : ℝ) := by ring
  rw [corridorTopPolynomial_eval_abs_eq_lower_div F hy hzero]
  dsimp [lowerF, m] at heval hscaled ⊢
  exact (div_le_div_of_nonneg_right heval (pow_nonneg hyRPos.le _)).trans hscaled

end

end Erdos1212Kernel.CorridorScale
