import Erdos1212Kernel.TaoFirstDerivativeSum

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

/-- Proposition 6's first-derivative estimate on an integer-spaced half-open
interval. Its length `M` is bounded by, but not identified with, the real
normalization scale `N`. The explicit constant is independent of all parameters. -/
theorem taoFirstDerivative_scaled_sum_bound (f f' f'' : Real → Real) (a : Real) (M : Nat)
    {A N T : Real} (hA : 1 ≤ A) (hN : 1 ≤ N) (hT : 0 < T) (hMN : (M : Real) ≤ N)
    (hsmall : T ≤ N / (2 * A))
    (hf : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc a (a + M), T / (A * N) ≤ |f' t|)
    (hfirst : ∀ t ∈ Set.Icc a (a + M), |f' t| ≤ A * T / N)
    (hsecond : ∀ t ∈ Set.Icc a (a + M), |f'' t| ≤ A * T / N ^ 2) :
    ‖∑ n ∈ Finset.range M, taoCorputPhase (f (a + n))‖ / N ≤ (2 + 2 * Real.pi) * A ^ 3 / T := by
  have hAp : 0 < A := by linarith
  have hNp : 0 < N := by linarith
  have hδ : 0 < T / (A * N) := by positivity
  have hD : 0 ≤ A * T / N ^ 2 := by positivity
  have hhalf : A * T / N ≤ 1 / 2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hsmall
    apply (div_le_iff₀ hNp).2
    nlinarith
  have hraw := taoFirstDerivative_sum_bound f f' f'' a M hδ hD hf hf' hlow
    (fun t ht => (hfirst t ht).trans hhalf) hsecond
  have hV : 0 ≤ (A * T / N ^ 2) * ((2 * Real.pi) / (T / (A * N)) ^ 2) := by positivity
  have hscale := mul_le_mul_of_nonneg_right hMN hV
  have he : (2 * (1 / (T / (A * N))) + N * ((A * T / N ^ 2) *
      ((2 * Real.pi) / (T / (A * N)) ^ 2))) / N = (2 * A + 2 * Real.pi * A ^ 3) / T := by
    field_simp
    <;> ring
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hA3 : A ≤ A ^ 3 := by
    nlinarith [mul_nonneg hAp.le (sub_nonneg.mpr hA2)]
  calc
    _ ≤ (2 * (1 / (T / (A * N))) + N * ((A * T / N ^ 2) *
        ((2 * Real.pi) / (T / (A * N)) ^ 2))) / N :=
      (div_le_div_iff_of_pos_right hNp).2 (hraw.trans (by linarith))
    _ = (2 * A + 2 * Real.pi * A ^ 3) / T := he
    _ ≤ (2 + 2 * Real.pi) * A ^ 3 / T := by
      apply (div_le_div_iff_of_pos_right hT).2
      nlinarith

/-- The deleted right endpoint contributes one unit of norm, not zero.
This is the closed-interval version of the same source proof. -/
theorem taoFirstDerivative_scaled_closed_sum_bound (f f' f'' : Real → Real) (a : Real) (M : Nat)
    {A N T : Real} (hA : 1 ≤ A) (hN : 1 ≤ N) (hT : 0 < T) (hMN : (M : Real) ≤ N)
    (hsmall : T ≤ N / (2 * A))
    (hf : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc a (a + M), T / (A * N) ≤ |f' t|)
    (hfirst : ∀ t ∈ Set.Icc a (a + M), |f' t| ≤ A * T / N)
    (hsecond : ∀ t ∈ Set.Icc a (a + M), |f'' t| ≤ A * T / N ^ 2) :
    ‖∑ n ∈ Finset.range (M + 1), taoCorputPhase (f (a + n))‖ / N ≤ (3 + 2 * Real.pi) * A ^ 3 / T := by
  have hNp : 0 < N := by linarith
  have hAp : 0 < A := by linarith
  have hbase := taoFirstDerivative_scaled_sum_bound f f' f'' a M hA hN hT hMN hsmall hf hf' hlow hfirst hsecond
  have hTle : T ≤ N := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hsmall
    nlinarith
  have hA3 : 1 ≤ A ^ 3 := by
    have hA2 : 1 ≤ A ^ 2 := by nlinarith
    nlinarith [mul_nonneg hAp.le (sub_nonneg.mpr hA2)]
  have hend : 1 / N ≤ A ^ 3 / T := by
    calc
      _ ≤ 1 / T := one_div_le_one_div_of_le hT hTle
      _ ≤ A ^ 3 / T := (div_le_div_iff_of_pos_right hT).2 hA3
  rw [Finset.sum_range_succ]
  have hnorm := norm_add_le (∑ n ∈ Finset.range M, taoCorputPhase (f (a + n))) (taoCorputPhase (f (a + M)))
  rw [taoCorputPhase_norm] at hnorm
  calc
    _ ≤ (‖∑ n ∈ Finset.range M, taoCorputPhase (f (a + n))‖ + 1) / N :=
      (div_le_div_iff_of_pos_right hNp).2 hnorm
    _ = ‖∑ n ∈ Finset.range M, taoCorputPhase (f (a + n))‖ / N + 1 / N := add_div _ _ _
    _ ≤ (2 + 2 * Real.pi) * A ^ 3 / T + A ^ 3 / T := add_le_add hbase hend
    _ = (3 + 2 * Real.pi) * A ^ 3 / T := by ring

end

end Erdos1212Kernel
