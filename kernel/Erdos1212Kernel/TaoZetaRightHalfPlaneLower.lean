import Erdos1212Kernel.TaoZetaAdjustedResidual
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory
open scoped BigOperators LSeries.notation

set_option maxHeartbeats 1900000

/-- Integral-test tail bound in the exact normalization used for zeta. -/
theorem taoRealPSeries_tail_bound {σ : Real} (hσ : 1 < σ) :
    (∑' n : Nat, ((n + 2 : Nat) : Real) ^ (-σ)) ≤ 1 / (σ - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro M
    have hanti : AntitoneOn (fun x : Real => x ^ (-σ))
        (Set.Icc 1 (1 + (M : Real))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hsum := hanti.sum_le_integral (x₀ := (1 : Real)) (a := M)
    have hzero : (0 : Real) ∉ Set.uIcc 1 (1 + (M : Real)) := by
      have hM : (0 : Real) ≤ (M : Real) := Nat.cast_nonneg M
      have hle : (1 : Real) ≤ 1 + (M : Real) := by linarith
      rw [Set.uIcc_of_le hle]
      intro h
      linarith [h.1]
    have hint : (∫ x in (1 : Real)..1 + (M : Real), x ^ (-σ)) =
        ((1 + (M : Real)) ^ (1 - σ) - 1) / (1 - σ) := by
      have h := integral_rpow (a := (1 : Real)) (b := 1 + (M : Real)) (r := -σ)
        (Or.inr ⟨(by linarith : -σ ≠ -1), hzero⟩)
      have hexp : -σ + 1 = 1 - σ := by ring
      rw [hexp] at h
      simpa using h
    calc
      (∑ n ∈ Finset.range M, ((n + 2 : Nat) : Real) ^ (-σ)) ≤
          ∫ x in (1 : Real)..1 + (M : Real), x ^ (-σ) := by
            have heq :
                (∑ n ∈ Finset.range M, ((n + 2 : Nat) : Real) ^ (-σ)) =
                  ∑ n ∈ Finset.range M, (1 + ((n + 1 : Nat) : Real)) ^ (-σ) := by
              apply Finset.sum_congr rfl
              intro n _hn
              congr 1
              push_cast
              ring
            rw [heq]
            exact hsum
      _ = ((1 + (M : Real)) ^ (1 - σ) - 1) / (1 - σ) := hint
      _ = (1 - (1 + (M : Real)) ^ (1 - σ)) / (σ - 1) := by
        apply (div_eq_div_iff (by linarith) (by linarith)).2
        ring
      _ ≤ 1 / (σ - 1) := by
        apply (div_le_div_iff_of_pos_right (by linarith)).2
        have hnonneg := Real.rpow_nonneg (by positivity : (0 : Real) ≤ 1 + (M : Real)) (1 - σ)
        linarith

/-- Elementary bound `zeta(sigma) <= 1 + 1/(sigma-1)`. -/
theorem taoRealPSeries_bound {σ : Real} (hσ : 1 < σ) :
    (∑' n : Nat, ((n + 1 : Nat) : Real) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hsum : Summable (fun n : Nat => ((n + 1 : Nat) : Real) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (_root_.summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  rw [hsum.tsum_eq_zero_add]
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
    add_le_add_left (taoRealPSeries_tail_bound hσ) 1

/-- Absolute convergence bounds zeta at `sigma+it` by the real p-series. -/
theorem norm_riemannZeta_le_realPSeries {σ t : Real} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      ∑' n : Nat, ((n + 1 : Nat) : Real) ^ (-σ) := by
  let s : Complex := (σ : Complex) + (t : Complex) * Complex.I
  have hsre : 1 < s.re := by simpa [s] using hσ
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsre]
  have hsum : Summable (fun n : Nat => ‖1 / (n + 1 : Complex) ^ s‖) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).2
        ((Complex.summable_one_div_nat_cpow).2 hsre)).norm
  calc
    ‖∑' n : Nat, 1 / (n + 1 : Complex) ^ s‖ ≤
        ∑' n : Nat, ‖1 / (n + 1 : Complex) ^ s‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = ∑' n : Nat, ((n + 1 : Nat) : Real) ^ (-σ) := by
      congr 1
      funext n
      have hbase : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
        norm_cast
      rw [hbase]
      rw [one_div, ← Complex.cpow_neg]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity)
          (Complex.re_neg_ne_zero_of_one_lt_re hsre)]
      simp [s]

theorem norm_riemannZeta_le_one_add_inv_sub_one {σ t : Real} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      1 + 1 / (σ - 1) :=
  (norm_riemannZeta_le_realPSeries hσ).trans (taoRealPSeries_bound hσ)

/-- The de la Vallee Poussin `3-4-1` Euler-product inequality specialized
to the modulus-one character, hence to the Riemann zeta function. -/
theorem norm_riemannZeta_three_four_one_product_ge_one
    (σ t : Real) (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta (σ : Complex) ^ 3 *
      riemannZeta ((σ : Complex) + (t : Complex) * Complex.I) ^ 4 *
      riemannZeta ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ := by
  have hx : 0 < σ - 1 := by linarith
  have h := DirichletCharacter.norm_LSeries_product_ge_one
    (χ := (1 : DirichletCharacter Complex 1)) hx t
  simp only [one_pow, DirichletCharacter.LSeries_modOne_eq] at h
  have hs0eq : (1 : Complex) + ((σ - 1 : Real) : Complex) = (σ : Complex) := by
    push_cast
    ring
  have hs1eq : (σ : Complex) + Complex.I * (t : Complex) =
      (σ : Complex) + (t : Complex) * Complex.I := by
    ring
  have hs2eq : (σ : Complex) + 2 * Complex.I * (t : Complex) =
        (σ : Complex) + ((2 * t : Real) : Complex) * Complex.I := by
    push_cast
    ring
  rw [hs0eq, hs1eq, hs2eq] at h
  have hσc : 1 < ((σ : Real) : Complex).re := by simpa using hσ
  have hσtc : 1 < ((σ : Complex) + (t : Complex) * Complex.I).re := by simp [hσ]
  have hσ2tc : 1 < ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I).re := by
    simp [hσ]
  simpa only [LSeries_one_eq_riemannZeta hσc,
    LSeries_one_eq_riemannZeta hσtc,
    LSeries_one_eq_riemannZeta hσ2tc,
    mul_assoc] using h

/-- A fourth-root-free quantitative lower bound. This is deliberately
stated multiplicatively because taking logarithms is the next consumer. -/
theorem one_le_pseriesBound_pow_four_mul_norm_riemannZeta
    (σ t : Real) (hσ : 1 < σ) :
    1 ≤ (1 + 1 / (σ - 1)) ^ 4 *
      ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ := by
  let B : Real := 1 + 1 / (σ - 1)
  let a : Real := ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖
  have hden : 0 < σ - 1 := by linarith
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have hinv : 0 ≤ 1 / (σ - 1) := by positivity
    linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have ha0 : 0 ≤ a := norm_nonneg _
  have hzeroUpper : ‖riemannZeta (σ : Complex)‖ ≤ B := by
    dsimp only [B]
    convert norm_riemannZeta_le_one_add_inv_sub_one (σ := σ) (t := 0) hσ using 1 <;>
      norm_num
  have htwoUpper :
      ‖riemannZeta ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ ≤ B := by
    simpa only [B] using
      (norm_riemannZeta_le_one_add_inv_sub_one (σ := σ) (t := 2 * t) hσ)
  have hprod := norm_riemannZeta_three_four_one_product_ge_one σ t hσ
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have hpow : 1 ≤ B ^ 4 * a ^ 4 := by
    calc
      1 ≤ ‖riemannZeta (σ : Complex)‖ ^ 3 * a ^ 4 *
          ‖riemannZeta ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ :=
        hprod
      _ ≤ B ^ 3 * a ^ 4 * B := by
        gcongr
      _ = B ^ 4 * a ^ 4 := by ring
  by_cases ha : 1 ≤ a
  · have hmul := mul_le_mul (one_le_pow₀ hB1) ha
        (by norm_num : (0 : Real) ≤ 1) (pow_nonneg hB0 4)
    norm_num at hmul
    simpa only [B, a] using hmul
  · have ha1 : a ≤ 1 := le_of_not_ge ha
    have ha4 : a ^ 4 ≤ a := by
      calc
        a ^ 4 = a * a ^ 3 := by ring
        _ ≤ a * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) ha0
        _ = a := mul_one a
    have := hpow.trans (mul_le_mul_of_nonneg_left ha4 (pow_nonneg hB0 4))
    simpa only [B, a] using this

/-- Explicit lower bound in the normalized logarithmic form consumed by
the adjusted-residual Borel estimate. -/
theorem neg_four_mul_log_pseriesBound_le_log_norm_riemannZeta
    (σ t : Real) (hσ : 1 < σ) :
    -4 * Real.log (1 + 1 / (σ - 1)) ≤
      Real.log ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ := by
  let B : Real := 1 + 1 / (σ - 1)
  let a : Real := ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖
  have hBpos : 0 < B := by
    dsimp [B]
    have hden : 0 < σ - 1 := by linarith
    have hinv : 0 ≤ 1 / (σ - 1) := by positivity
    linarith
  have hsre : 1 < ((σ : Complex) + (t : Complex) * Complex.I).re := by simp [hσ]
  have hapos : 0 < a := by
    exact norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hsre)
  have hmul := one_le_pseriesBound_pow_four_mul_norm_riemannZeta σ t hσ
  change 1 ≤ B ^ 4 * a at hmul
  have hlog := Real.log_le_log (by positivity : (0 : Real) < 1) hmul
  rw [Real.log_one, Real.log_mul (pow_ne_zero 4 hBpos.ne') hapos.ne',
    Real.log_pow] at hlog
  change -4 * Real.log B ≤ Real.log a
  norm_num at hlog
  linarith

end

end Erdos1212Kernel
