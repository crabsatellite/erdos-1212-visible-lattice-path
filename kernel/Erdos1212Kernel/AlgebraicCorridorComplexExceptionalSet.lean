import Erdos1212Kernel.AlgebraicCorridorBadCrossingScale
import Erdos1212Kernel.AlgebraicCorridorPolynomialFamily
import Erdos1212Kernel.AlgebraicCorridorLowDegreeScale

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Set MeasureTheory Polynomial

/-- Real parts of every complex root, exactly as in the paper. -/
def complexRootRealParts (p : Polynomial ℝ) : Finset ℝ :=
  ((p.map (algebraMap ℝ ℂ)).roots.toFinset).image Complex.re

theorem complexRootRealParts_card_le_natDegree (p : Polynomial ℝ) :
    (complexRootRealParts p).card ≤ p.natDegree := by
  unfold complexRootRealParts
  exact Finset.card_image_le.trans
    ((Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_map_le_natDegree p))

def complexRootRealPartNeighborhood (p : Polynomial ℝ) (δ : ℝ) : Set ℝ :=
  rootNeighborhood (complexRootRealParts p) δ

theorem complexRootRealPartNeighborhood_measurable
    (p : Polynomial ℝ) (δ : ℝ) :
    MeasurableSet (complexRootRealPartNeighborhood p δ) :=
  rootNeighborhood_measurable _ _

theorem complexRootRealPartNeighborhood_measure_le_degree
    (p : Polynomial ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (complexRootRealPartNeighborhood p δ) ≤
      (p.natDegree : ℕ) • ENNReal.ofReal (2 * δ) := by
  unfold complexRootRealPartNeighborhood
  calc
    volume (rootNeighborhood (complexRootRealParts p) δ) ≤
        ∑ _β : complexRootRealParts p, ENNReal.ofReal (2 * δ) :=
      rootNeighborhood_measure_le _ hδ
    _ = (complexRootRealParts p).card • ENNReal.ofReal (2 * δ) := by simp
    _ ≤ p.natDegree • ENNReal.ofReal (2 * δ) :=
      nsmul_le_nsmul_left (by positivity) (complexRootRealParts_card_le_natDegree p)

def algebraicCorridorExceptionalSet (N : ℝ) : Set ℝ :=
  ⋃ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
    complexRootRealPartNeighborhood p.val (4 * rho N)

theorem algebraicCorridorExceptionalSet_measurable (N : ℝ) :
    MeasurableSet (algebraicCorridorExceptionalSet N) := by
  unfold algebraicCorridorExceptionalSet
  exact MeasurableSet.iUnion fun p =>
    complexRootRealPartNeighborhood_measurable p.val _

theorem algebraicCorridorExceptionalSet_measure_le_sum (N : ℝ) :
    volume (algebraicCorridorExceptionalSet N) ≤
      ∑ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        (p.val.natDegree : ℕ) • ENNReal.ofReal (8 * rho N) := by
  unfold algebraicCorridorExceptionalSet
  calc
    volume (⋃ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        complexRootRealPartNeighborhood p.val (4 * rho N)) ≤
      ∑ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        volume (complexRootRealPartNeighborhood p.val (4 * rho N)) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        (p.val.natDegree : ℕ) • ENNReal.ofReal (8 * rho N) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [show 2 * (4 * rho N) = 8 * rho N by ring] using
        complexRootRealPartNeighborhood_measure_le_degree p.val
          (show 0 ≤ 4 * rho N by unfold rho; positivity)

theorem algebraicCorridorExceptionalSet_measure_le (N : ℝ) :
    volume (algebraicCorridorExceptionalSet N) ≤
      ((degree N : ℕ) *
        (nonzeroBoundedIntegerPolynomialFamily
          (degree N) (height N)).card : ℕ) •
        ENNReal.ofReal (8 * rho N) := by
  refine (algebraicCorridorExceptionalSet_measure_le_sum N).trans ?_
  calc
    (∑ p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        (p.val.natDegree : ℕ) • ENNReal.ofReal (8 * rho N)) ≤
      ∑ _p : nonzeroBoundedIntegerPolynomialFamily (degree N) (height N),
        (degree N : ℕ) • ENNReal.ofReal (8 * rho N) := by
      apply Finset.sum_le_sum
      intro p hp
      exact nsmul_le_nsmul_left (by positivity)
        (nonzeroBoundedIntegerPolynomial_natDegree_le p.property)
    _ = ((degree N : ℕ) *
        (nonzeroBoundedIntegerPolynomialFamily
          (degree N) (height N)).card : ℕ) •
        ENNReal.ofReal (8 * rho N) := by
      have hcard : (Finset.univ : Finset
          (nonzeroBoundedIntegerPolynomialFamily
            (degree N) (height N))).card =
          (nonzeroBoundedIntegerPolynomialFamily
            (degree N) (height N)).card := by
        rw [Finset.card_univ, Fintype.card_coe]
      simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_mul]
      ac_rfl

def algebraicCorridorExceptionalMajorant (N : ℝ) : ℝ :=
  8 * rho N * (degree N : ℝ) *
    (((2 * height N + 1) ^ (degree N + 1) : ℕ) : ℝ)

theorem algebraicCorridorExceptionalSet_measure_le_ofReal (N : ℝ) :
    volume (algebraicCorridorExceptionalSet N) ≤
      ENNReal.ofReal (algebraicCorridorExceptionalMajorant N) := by
  have hfamily := nonzeroBoundedIntegerPolynomialFamily_card_le
    (degree N) (height N)
  have hcoeff : degree N *
      (nonzeroBoundedIntegerPolynomialFamily
        (degree N) (height N)).card ≤
      degree N * (2 * height N + 1) ^ (degree N + 1) :=
    Nat.mul_le_mul_left (degree N) hfamily
  have hmeasure := algebraicCorridorExceptionalSet_measure_le N
  refine hmeasure.trans ((nsmul_le_nsmul_left
    (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal (8 * rho N)) hcoeff).trans ?_)
  unfold algebraicCorridorExceptionalMajorant
  rw [nsmul_eq_mul]
  apply le_of_eq
  rw [show 8 * rho N * (degree N : ℝ) *
      (((2 * height N + 1) ^ (degree N + 1) : ℕ) : ℝ) =
      ((degree N * (2 * height N + 1) ^ (degree N + 1) : ℕ) : ℝ) *
        (8 * rho N) by push_cast; ring,
    ENNReal.ofReal_mul (by positivity :
      0 ≤ ((degree N * (2 * height N + 1) ^ (degree N + 1) : ℕ) : ℝ)),
    ENNReal.ofReal_natCast]

theorem eventually_algebraicCorridorExceptionalMajorant_le_exp_decay :
    ∀ᶠ N : ℝ in Filter.atTop,
      algebraicCorridorExceptionalMajorant N ≤
        Real.exp (-ell N / (40000 * L N)) := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell 1200000000 8] with N hdom hLsmall
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hdPos : (0 : ℝ) < degree N := by
    exact_mod_cast (degree_bounds hdom.2.2).1
  have hdUpper := (degree_bounds hdom.2.2).2
  have hhPos : (0 : ℝ) < height N := by
    exact_mod_cast (show 0 < height N from
      Nat.ceil_pos.mpr (Real.exp_pos (L N ^ 6)))
  have hhOne : (1 : ℝ) ≤ height N := by
    exact_mod_cast (show 1 ≤ height N from Nat.one_le_iff_ne_zero.mpr
      (by exact_mod_cast hhPos.ne'))
  have hrhoPos : 0 < rho N := by unfold rho; positivity
  have hfamilyBasePos : (0 : ℝ) < 2 * height N + 1 := by positivity
  have hfamilyPowPos : (0 : ℝ) <
      (((2 * height N + 1) ^ (degree N + 1) : ℕ) : ℝ) := by positivity
  have hlogEight : Real.log (8 : ℝ) ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h
    exact h
  have hlogDegree : Real.log (degree N : ℝ) ≤ 5000 * L N := by
    have hlog := Real.log_le_sub_one_of_pos hdPos
    linarith
  have hheightLog := log_height_le hdom.2.2
  have hbaseLe : (2 * height N + 1 : ℕ) ≤ (3 : ℝ) * height N := by
    push_cast
    linarith
  push_cast at hbaseLe
  have hlogBase : Real.log (2 * (height N : ℝ) + 1) ≤
      4 * L N ^ 6 := by
    have hlogMono := Real.log_le_log hfamilyBasePos hbaseLe
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hhPos.ne'] at hlogMono
    have hlogThree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hlogThree
    have hLsix : (1 : ℝ) ≤ L N ^ 6 := one_le_pow₀ hdom.2.2
    calc
      Real.log (2 * (height N : ℝ) + 1) ≤
          Real.log 3 + Real.log (height N : ℝ) := hlogMono
      _ ≤ 2 + 2 * L N ^ 6 := add_le_add hlogThree hheightLog
      _ ≤ 4 * L N ^ 6 := by nlinarith
  have hlogBaseNonneg : 0 ≤ Real.log (2 * (height N : ℝ) + 1) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * height N + 1 by omega))
  have hdSucc : ((degree N + 1 : ℕ) : ℝ) ≤ 5000 * L N + 1 := by
    push_cast
    linarith
  have hdegreeHeight : ((degree N + 1 : ℕ) : ℝ) *
      Real.log (2 * (height N : ℝ) + 1) ≤
        (5000 * L N + 1) * (4 * L N ^ 6) :=
    mul_le_mul hdSucc hlogBase hlogBaseNonneg (by positivity)
  have hpositive : Real.log (8 : ℝ) + Real.log (degree N : ℝ) +
      ((degree N + 1 : ℕ) : ℝ) *
        Real.log (2 * (height N : ℝ) + 1) ≤
      30000 * L N ^ 7 := by
    nlinarith [pow_le_pow_right₀ hdom.2.2 (by norm_num : 1 ≤ 7),
      pow_le_pow_right₀ hdom.2.2 (by norm_num : 6 ≤ 7)]
  have habsorb : 30000 * L N ^ 7 ≤ ell N / (40000 * L N) := by
    apply (le_div_iff₀ (by positivity : 0 < 40000 * L N)).mpr
    have hLsmall' : 1200000000 * L N ^ 8 < ell N := by
      simpa using hLsmall
    nlinarith [show 30000 * L N ^ 7 * (40000 * L N) =
      1200000000 * L N ^ 8 by ring]
  have hlogMajorant : Real.log (algebraicCorridorExceptionalMajorant N) ≤
      -ell N / (40000 * L N) := by
    unfold algebraicCorridorExceptionalMajorant rho
    push_cast
    have hrealPowPos : 0 < (2 * (height N : ℝ) + 1) ^ (degree N + 1) :=
      pow_pos hfamilyBasePos _
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0)
          (Real.exp_ne_zero _)) hdPos.ne') hrealPowPos.ne',
      Real.log_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0)
          (Real.exp_ne_zero _)) hdPos.ne',
      Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_pow]
    calc
      Real.log 8 + -ell N / (20000 * L N) + Real.log (degree N : ℝ) +
          ((degree N + 1 : ℕ) : ℝ) *
            Real.log (2 * (height N : ℝ) + 1) =
        -ell N / (20000 * L N) +
          (Real.log 8 + Real.log (degree N : ℝ) +
            ((degree N + 1 : ℕ) : ℝ) *
              Real.log (2 * (height N : ℝ) + 1)) := by ring
      _ ≤ -ell N / (20000 * L N) + 30000 * L N ^ 7 :=
        by simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hpositive (-ell N / (20000 * L N))
      _ ≤ -ell N / (20000 * L N) + ell N / (40000 * L N) :=
        by simpa [add_comm] using
          add_le_add_left habsorb (-ell N / (20000 * L N))
      _ = -ell N / (40000 * L N) := by
        field_simp [hLPos.ne']
        ring
  have hmajorantPos : 0 < algebraicCorridorExceptionalMajorant N := by
    unfold algebraicCorridorExceptionalMajorant
    positivity
  have hexp := Real.exp_le_exp.mpr hlogMajorant
  rw [Real.exp_log hmajorantPos] at hexp
  exact hexp

theorem complex_root_realPart_mem_exceptional
    {N : ℝ} {p : Polynomial ℝ}
    (hp : p ∈ nonzeroBoundedIntegerPolynomialFamily (degree N) (height N))
    {β : ℂ} (hβ : β ∈ (p.map (algebraMap ℝ ℂ)).roots)
    {α : ℝ} (hnear : |α - β.re| < 4 * rho N) :
    α ∈ algebraicCorridorExceptionalSet N := by
  unfold algebraicCorridorExceptionalSet
  rw [Set.mem_iUnion]
  refine ⟨⟨p, hp⟩, ?_⟩
  unfold complexRootRealPartNeighborhood rootNeighborhood
  rw [Set.mem_iUnion]
  let root : complexRootRealParts p :=
    ⟨β.re, Finset.mem_image.mpr
      ⟨β, Multiset.mem_toFinset.mpr hβ, rfl⟩⟩
  refine ⟨root, ?_⟩
  simp only [Set.mem_Ioo]
  rw [abs_lt] at hnear
  constructor <;> linarith

end

end Erdos1212Kernel.CorridorScale
