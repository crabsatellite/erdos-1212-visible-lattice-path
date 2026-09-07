import Erdos1212Kernel.AlgebraicCorridorTopEvaluationBound

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

theorem totalDegree_pos_of_nonzero_eval_zero
    (F : MvPolynomial (Fin 2) ℤ) (hF : F ≠ 0)
    {x y : ℕ} (hzero : MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0) :
    0 < F.totalDegree := by
  by_contra hnot
  have hdegree : F.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  rw [hconst, MvPolynomial.eval_C] at hzero
  apply hF
  rw [hconst, hzero]
  exact MvPolynomial.C_0

theorem eventually_topPolynomial_eval_abs_le_root_error :
    ∀ᶠ N : ℝ in atTop, ∀ (F : MvPolynomial (Fin 2) ℤ), F ≠ 0 →
      F.totalDegree ≤ degree N → corridorPolynomialHeight F ≤ height N →
      ∀ {x y : ℕ}, 0 < y → (x : ℝ) ≤ 2 * (y : ℝ) →
      N / 2 ≤ (y : ℝ) →
      MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0 →
      |(Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F)).eval
          ((x : ℝ) / (y : ℝ))| ≤ N ^ ((-1 : ℝ) / 2) := by
  filter_upwards [eventually_low_degree_error_le, eventually_large_domain] with N hscale hdom
  intro F hF hdegree hheight x y hy hxTwo hyLower hzero
  exact (corridorTopPolynomial_eval_abs_le_homogeneousNumerator
    (zero_lt_one.trans hdom.1)
    F (totalDegree_pos_of_nonzero_eval_zero F hF hzero) hdegree hheight
    hy hxTwo hyLower hzero).trans hscale

theorem eventually_root_error_lt_one :
    ∀ᶠ N : ℝ in atTop, N ^ ((-1 : ℝ) / 2) < 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  rw [← Real.rpow_zero N]
  exact Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)

theorem corridorTopPolynomial_natDegree_pos_of_small_eval
    {N : ℝ} (hN : N ^ ((-1 : ℝ) / 2) < 1)
    (F : MvPolynomial (Fin 2) ℤ) (hF : F ≠ 0) {t : ℝ}
    (heval : |(Polynomial.map (Int.castRingHom ℝ)
      (corridorTopPolynomial F)).eval t| ≤ N ^ ((-1 : ℝ) / 2)) :
    0 < (corridorTopPolynomial F).natDegree := by
  by_contra hnot
  have hdegree : (corridorTopPolynomial F).natDegree = 0 :=
    Nat.eq_zero_of_not_pos hnot
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegree
  have hpz : corridorTopPolynomial F ≠ 0 := corridorTopPolynomial_ne_zero F hF
  have hc0 : c ≠ 0 := by
    intro hz
    apply hpz
    rw [← hc, hz, Polynomial.C_0]
  have hcOne : (1 : ℝ) ≤ |(c : ℤ)| := by exact_mod_cast Int.one_le_abs hc0
  have hevalC : |(Polynomial.map (Int.castRingHom ℝ)
      (corridorTopPolynomial F)).eval t| = |(c : ℤ)| := by
    rw [← hc]
    simp
  rw [hevalC] at heval
  linarith

/-- The exact univariate witness in the first half of Lemma 6.1. -/
theorem eventually_exists_topPolynomial_small_value :
    ∀ᶠ N : ℝ in atTop, ∀ (F : MvPolynomial (Fin 2) ℤ), F ≠ 0 →
      F.totalDegree ≤ degree N → corridorPolynomialHeight F ≤ height N →
      ∀ {x y : ℕ}, 0 < y → (x : ℝ) ≤ 2 * (y : ℝ) →
      N / 2 ≤ (y : ℝ) →
      MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0 →
      ∃ p : Polynomial ℤ,
        p = corridorTopPolynomial F ∧ p ≠ 0 ∧ 0 < p.natDegree ∧
        p.natDegree ≤ degree N ∧
        (Polynomial.map (Int.castRingHom ℝ) p ∈
          nonzeroBoundedIntegerPolynomialFamily (degree N) (height N)) ∧
        |(Polynomial.map (Int.castRingHom ℝ) p).eval
          ((x : ℝ) / (y : ℝ))| ≤ N ^ ((-1 : ℝ) / 2) := by
  filter_upwards [eventually_topPolynomial_eval_abs_le_root_error,
    eventually_root_error_lt_one] with N hsmall herror
  intro F hF hd hh x y hy hx hyl hz
  have heval := hsmall F hF hd hh hy hx hyl hz
  exact ⟨corridorTopPolynomial F, rfl, corridorTopPolynomial_ne_zero F hF,
    corridorTopPolynomial_natDegree_pos_of_small_eval herror F hF heval,
    (corridorTopPolynomial_natDegree_le F).trans hd,
    corridorTopPolynomial_mem_family hF hd hh, heval⟩

end

end Erdos1212Kernel.CorridorScale
