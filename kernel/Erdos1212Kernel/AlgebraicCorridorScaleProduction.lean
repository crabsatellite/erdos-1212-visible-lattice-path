import Erdos1212Kernel.AlgebraicCorridorScaleLogBounds
import Erdos1212Kernel.AlgebraicCorridorValueBound

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter
open scoped BigOperators

theorem eventually_coefficientBound_le_height :
    ∀ᶠ N : ℝ in atTop, coefficientBound N ≤ (height N : ℝ) := by
  filter_upwards [eventually_large_domain,
    L_tendsto.eventually_gt_atTop (2000000000000000 : ℝ)] with N hdom hlarge
  have hL12 : L N ≤ L N ^ 2 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hdom.2.2 (by norm_num : 1 ≤ 2))
  have hC : (2000000000000000 : ℝ) < L N ^ 2 := hlarge.trans_le hL12
  have hsmall : 2000000000000000 * L N ^ 4 < L N ^ 6 := by
    calc
      _ < L N ^ 2 * L N ^ 4 :=
        mul_lt_mul_of_pos_right hC (pow_pos (zero_lt_one.trans_le hdom.2.2) 4)
      _ = _ := by ring
  have hlog := (log_coefficientBound_le hdom.2.1 hdom.2.2).trans_lt hsmall
  have hc := (Real.log_lt_iff_lt_exp (coefficientBound_pos hdom.2.1)).mp hlog
  exact hc.le.trans (Nat.le_ceil _)

/-- The strict comparison required for the integer-divisibility argument is produced from N alone. -/
theorem eventually_valueBound_lt_z_pow_rows :
    ∀ᶠ N : ℝ in atTop, valueBound N < z N ^ rows N := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell 3000000000000000 4] with N hdom hsmall
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hu : 0 < u N := by unfold u; linarith [hdom.2.2]
  have hd : (1 : ℝ) ≤ degree N := by exact_mod_cast (degree_bounds hdom.2.2).1
  have hell : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hlog : Real.log (valueBound N) < ((rows N : ℝ) / u N) * ell N := by
    calc
      _ ≤ (degree N : ℝ) * ell N + 3000000000000000 * L N ^ 4 :=
        log_valueBound_le hN hdom.2.1 hdom.2.2
      _ < (degree N : ℝ) * ell N + ell N := by linarith only [hsmall]
      _ ≤ (2 * (degree N : ℝ)) * ell N := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (rows_div_u_ge_twice_degree hu) hell.le
  have hpowlog : Real.log (z N ^ rows N) = ((rows N : ℝ) / u N) * ell N := by
    rw [Real.log_pow, log_z hN hu]
    ring
  rw [← hpowlog] at hlog
  exact (Real.log_lt_log_iff (valueBound_pos hN hdom.2.1) (pow_pos (z_pos hN hu) _)).mp hlog

theorem z_pow_rows_lt_product {N : ℝ} (hN : 0 < N) (hu : 0 < u N)
    (hr : 0 < rows N) (q : Fin (rows N) → ℕ)
    (hlarge : ∀ i, z N < (q i : ℝ)) :
    z N ^ rows N < ((∏ i, q i : ℕ) : ℝ) := by
  letI : Nonempty (Fin (rows N)) := ⟨⟨0, hr⟩⟩
  have hp := Finset.prod_lt_prod_of_nonempty (s := Finset.univ)
    (f := fun _ : Fin (rows N) => z N) (g := fun i => (q i : ℝ))
    (fun _ _ => z_pos hN hu) (fun i _ => hlarge i) Finset.univ_nonempty
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_prod] using hp

theorem log_product_lower {N : ℝ} (hN : 0 < N) (hu : 0 < u N)
    (hr : 0 < rows N) (q : Fin (rows N) → ℕ)
    (hlarge : ∀ i, z N < (q i : ℝ)) :
    ((rows N : ℝ) / u N) * ell N < Real.log ((∏ i, q i : ℕ) : ℝ) := by
  have h := Real.log_lt_log (pow_pos (z_pos hN hu) _)
    (z_pow_rows_lt_product hN hu hr q hlarge)
  rw [Real.log_pow, log_z hN hu] at h
  convert h using 1 <;> ring

/-- The arithmetic-algebraic producer of Proposition 5.2 on the exact paper scales.
Only the actual localized witness data remain to be supplied by geometry.
The common eventual threshold is selected before every root, offset and prime assignment. -/
theorem eventually_algebraic_point :
    ∀ᶠ N : ℝ in atTop,
      ∀ (root : Fin 2 → ℤ) (point : Fin (rows N) → Fin 2 → ℤ) (q : Fin (rows N) → ℕ),
        (∀ i k, |(point i k : ℝ)| ≤ (radius N : ℝ)) →
        (∀ k, |(root k : ℝ)| ≤ 4 * N) →
        (∀ i, (q i).Prime) → Function.Injective q →
        (∀ i, z N < (q i : ℝ)) →
        (∀ i k, (q i : ℤ) ∣ root k + point i k) →
        ∃ F : MvPolynomial (Fin 2) ℤ,
          F ≠ 0 ∧ F.totalDegree ≤ degree N ∧ MvPolynomial.eval root F = 0 ∧
          corridorPolynomialHeight F ≤ height N := by
  filter_upwards [eventually_large_domain, eventually_coefficientBound_le_height,
    eventually_valueBound_lt_z_pow_rows] with N hdom hheight hvalue
  intro root point q hpoint hroot hq hinj hlarge hdiv
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hu : 0 < u N := by unfold u; linarith [hdom.2.2]
  have hr : 0 < rows N := (rows_bounds hdom.2.2).1
  have hproduct := hvalue.trans (z_pow_rows_lt_product hN hu hr q hlarge)
  have hR : (1 : ℝ) ≤ radius N := by exact_mod_cast (radius_bounds hdom.2.1).1
  have hX : (1 : ℝ) ≤ 4 * N := by linarith [hdom.1]
  have hsize : ((degree N + 2).choose 2 : ℝ) *
      (((corridorInterpolationRowCount (degree N)).factorial : ℝ) *
        (radius N : ℝ) ^ (degree N * corridorInterpolationRowCount (degree N))) *
      (4 * N) ^ degree N < ((∏ i, q i : ℕ) : ℝ) := by
    simpa only [valueBound, coefficientBound, rows, ← corridorInterpolationRowCount_succ,
      Nat.cast_add, Nat.cast_one] using hproduct
  obtain ⟨F, hF, hdegree, hzero, hbound⟩ :=
    corridor_algebraic_zero_of_large_prime_product (degree N) (degree_bounds hdom.2.2).1
      (radius N : ℝ) (4 * N) hR hX root point q hpoint hroot hq hinj hdiv hsize
  refine ⟨F, hF, hdegree, hzero, ?_⟩
  have hh : (corridorPolynomialHeight F : ℝ) ≤ (height N : ℝ) := hbound.trans hheight
  exact_mod_cast hh

end

end Erdos1212Kernel.CorridorScale
