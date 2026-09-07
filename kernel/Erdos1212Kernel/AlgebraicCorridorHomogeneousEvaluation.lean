import Erdos1212Kernel.AlgebraicCorridorComplexRootProximity

namespace Erdos1212Kernel

noncomputable section

theorem corridorTopPolynomial_eval_mul_pow
    (F : MvPolynomial (Fin 2) ℤ) {x y : ℕ} (hy : 0 < y) :
    (Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F)).eval
          ((x : ℝ) / (y : ℝ)) * (y : ℝ) ^ F.totalDegree =
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
        (MvPolynomial.map (Int.castRingHom ℝ)
          (MvPolynomial.homogeneousComponent F.totalDegree F)) := by
  let p : Polynomial ℝ :=
    Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F)
  have hpDegree : p.natDegree ≤ F.totalDegree := by
    dsimp [p]
    exact Polynomial.natDegree_map_le.trans
      (corridorTopPolynomial_natDegree_le F)
  have heval := Polynomial.eval_homogenize hpDegree
    ![(x : ℝ), (y : ℝ)] (by
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact_mod_cast hy.ne')
  have hhom : p.homogenize F.totalDegree =
      MvPolynomial.map (Int.castRingHom ℝ)
        (MvPolynomial.homogeneousComponent F.totalDegree F) := by
    dsimp [p]
    rw [Polynomial.homogenize_map,
      corridorTopPolynomial_homogenize_eq]
  rw [hhom] at heval
  simpa [p] using heval.symm

theorem corridorMappedLower_add_top
    (F : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.map (Int.castRingHom ℝ) (corridorLowerPolynomial F) +
        MvPolynomial.map (Int.castRingHom ℝ)
          (MvPolynomial.homogeneousComponent F.totalDegree F) =
      MvPolynomial.map (Int.castRingHom ℝ) F := by
  unfold corridorLowerPolynomial
  simp

theorem corridorTopPolynomial_eval_abs_eq_lower_div
    (F : MvPolynomial (Fin 2) ℤ) {x y : ℕ} (hy : 0 < y)
    (hzero : MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0) :
    |(Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F)).eval
        ((x : ℝ) / (y : ℝ))| =
      |((MvPolynomial.eval ![(x : ℤ), (y : ℤ)]
        (corridorLowerPolynomial F) : ℤ) : ℝ)| /
        (y : ℝ) ^ F.totalDegree := by
  have hscale := corridorTopPolynomial_eval_mul_pow F (x := x) hy
  have hmapZero : MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
      (MvPolynomial.map (Int.castRingHom ℝ) F) = 0 := by
    have hmap := MvPolynomial.map_eval (Int.castRingHom ℝ)
      ![(x : ℤ), (y : ℤ)] F
    have hcoords : (((Int.castRingHom ℝ : ℤ →+* ℝ) : ℤ → ℝ) ∘
        ![(x : ℤ), (y : ℤ)]) = ![(x : ℝ), (y : ℝ)] := by
      funext i
      fin_cases i <;> simp
    rw [hcoords] at hmap
    rw [hzero, map_zero] at hmap
    simpa using hmap.symm
  have hsplit := congrArg
    (MvPolynomial.eval ![(x : ℝ), (y : ℝ)])
    (corridorMappedLower_add_top F)
  simp only [map_add] at hsplit
  have htop : MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
      (MvPolynomial.map (Int.castRingHom ℝ)
        (MvPolynomial.homogeneousComponent F.totalDegree F)) =
      -MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
        (MvPolynomial.map (Int.castRingHom ℝ)
          (corridorLowerPolynomial F)) := by
    linarith
  rw [htop] at hscale
  have hyPow : 0 < (y : ℝ) ^ F.totalDegree := by positivity
  have habs := congrArg abs hscale
  rw [abs_mul, abs_of_pos hyPow, abs_neg] at habs
  have hlowerMap :
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
        (MvPolynomial.map (Int.castRingHom ℝ) (corridorLowerPolynomial F)) =
      ((MvPolynomial.eval ![(x : ℤ), (y : ℤ)]
        (corridorLowerPolynomial F) : ℤ) : ℝ) := by
    have hmap := MvPolynomial.map_eval (Int.castRingHom ℝ)
      ![(x : ℤ), (y : ℤ)] (corridorLowerPolynomial F)
    have hcoords : (((Int.castRingHom ℝ : ℤ →+* ℝ) : ℤ → ℝ) ∘
        ![(x : ℤ), (y : ℤ)]) = ![(x : ℝ), (y : ℝ)] := by
      funext i
      fin_cases i <;> simp
    rw [hcoords] at hmap
    simpa using hmap.symm
  rw [hlowerMap] at habs
  apply (eq_div_iff hyPow.ne').mpr
  exact habs

end

end Erdos1212Kernel
