import Erdos1212Kernel.AlgebraicCorridorAvoidanceBasics

namespace Erdos1212Kernel
noncomputable section

theorem integerPolynomial_complex_leadingCoeff_norm_ge_one
    (p : Polynomial ℤ) (hp : p ≠ 0) :
    1 ≤ ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ := by
  rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
  have h := Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hr : (1 : ℝ) ≤ |(p.leadingCoeff : ℝ)| := by exact_mod_cast h
  simpa using hr

theorem integerPolynomial_exists_close_complex_root
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : 0 < p.natDegree)
    (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (heval : |(p.map (Int.castRingHom ℝ)).eval t| ≤ ε) :
    ∃ β ∈ (p.map (Int.castRingHom ℂ)).roots,
      ‖(t : ℂ) - β‖ ≤ ε ^ ((p.natDegree : ℝ)⁻¹) := by
  have hpc : p.map (Int.castRingHom ℂ) ≠ 0 := by
    intro hz
    apply hp
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa using hz
  have hdc : (p.map (Int.castRingHom ℂ)).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective p
  have heq : (p.map (Int.castRingHom ℂ)).eval (t : ℂ) =
      (((p.map (Int.castRingHom ℝ)).eval t : ℝ) : ℂ) := by
    clear hp hd heval hpc hdc
    induction p using Polynomial.induction_on' with
    | add p q ihp ihq => simp [ihp, ihq]
    | monomial n a => simp
  have hevalC : ‖(p.map (Int.castRingHom ℂ)).eval (t : ℂ)‖ ≤ ε := by
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact heval
  have hroot := exists_complex_root_norm_sub_le_rpow
    (p.map (Int.castRingHom ℂ)) hpc (by rwa [hdc]) (t : ℂ) hε
    (integerPolynomial_complex_leadingCoeff_norm_ge_one p hp) hevalC
  simpa only [hdc] using hroot

namespace CorridorScale

theorem eventually_integerPolynomial_close_root_rho :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ p : Polynomial ℤ,
      p ≠ 0 → 0 < p.natDegree → p.natDegree ≤ degree N →
      ∀ t : ℝ, |(p.map (Int.castRingHom ℝ)).eval t| ≤ N ^ ((-1 : ℝ) / 2) →
      ∃ β ∈ (p.map (Int.castRingHom ℂ)).roots,
        ‖(t : ℂ) - β‖ ≤ rho N ^ 2 := by
  filter_upwards [eventually_large_domain, eventually_root_error_le_rho_sq]
    with N hdom hscale
  intro p hp hpd hdeg t heval
  have hN : 0 < N := zero_lt_one.trans hdom.1
  obtain ⟨β, hβ, hnear⟩ := integerPolynomial_exists_close_complex_root
    p hp hpd t (Real.rpow_nonneg hN.le _) heval
  refine ⟨β, hβ, hnear.trans (le_trans ?_ hscale)⟩
  rw [← Real.rpow_mul hN.le]
  apply Real.rpow_le_rpow_of_exponent_le hdom.1.le
  have hpPos : (0 : ℝ) < p.natDegree := by exact_mod_cast hpd
  have hdPos : (0 : ℝ) < degree N := by exact_mod_cast hpd.trans_le hdeg
  have hdegR : (p.natDegree : ℝ) ≤ degree N := by exact_mod_cast hdeg
  have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 < 2 * (p.natDegree : ℝ))
    (show 2 * (p.natDegree : ℝ) ≤ 2 * (degree N : ℝ) by linarith)
  convert neg_le_neg hdiv using 1 <;> ring

theorem eventually_zero_near_direction_mem_exceptional :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ (F : MvPolynomial (Fin 2) ℤ),
      F ≠ 0 → F.totalDegree ≤ degree N → corridorPolynomialHeight F ≤ height N →
      ∀ (x y : ℕ) (α : ℝ), 0 < y → (x : ℝ) ≤ 2 * (y : ℝ) →
      N / 2 ≤ (y : ℝ) → |(x : ℝ) / (y : ℝ) - α| ≤ rho N →
      MvPolynomial.eval ![(x : ℤ), (y : ℤ)] F = 0 →
      α ∈ algebraicCorridorExceptionalSet N := by
  have hrho := rho_tendsto_zero.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_exists_topPolynomial_small_value,
    eventually_integerPolynomial_close_root_rho, hrho] with N hpoly hroot hrho
  intro F hF hd hh x y α hy hx hyl hα hz
  obtain ⟨p, hpEq, hp, hpd, hdeg, hfamily, heval⟩ :=
    hpoly F hF hd hh hy hx hyl hz
  obtain ⟨β, hβ, hnear⟩ := hroot p hp hpd hdeg ((x : ℝ) / (y : ℝ)) heval
  have hmap : (p.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) =
      p.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have hβ' : β ∈ ((p.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)).roots := by
    rwa [hmap]
  apply complex_root_realPart_mem_exceptional hfamily hβ'
  have hre : |(x : ℝ) / (y : ℝ) - β.re| ≤ rho N ^ 2 := by
    have h := Complex.abs_re_le_norm ((((x : ℝ) / (y : ℝ) : ℝ) : ℂ) - β)
    simpa using h.trans hnear
  have hα' : |α - (x : ℝ) / (y : ℝ)| ≤ rho N := by
    simpa only [abs_sub_comm] using hα
  have htri := abs_add_le (α - (x : ℝ) / (y : ℝ))
    ((x : ℝ) / (y : ℝ) - β.re)
  have hrpos : 0 < rho N := Real.exp_pos _
  have hsum : |α - β.re| ≤ rho N + rho N ^ 2 := by
    rw [sub_add_sub_cancel] at htri
    linarith
  exact hsum.trans_lt (by nlinarith)

end CorridorScale

end
end Erdos1212Kernel
