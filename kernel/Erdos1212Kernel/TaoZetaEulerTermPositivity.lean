import Erdos1212Kernel.TaoZetaLogDerivativePositivity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoPureImaginaryCpow_re (t : Real) {n : Nat} (hn : 0 < n) :
    ((n : Complex) ^ (-(t : Complex) * Complex.I)).re =
      Real.cos (t * Real.log n) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  rw [show (n : Complex) ^ (-(t : Complex) * Complex.I) =
    taoCorputPhase (taoCorputLogPhase t n) from (taoCorputLogPhase_cpow t hnR).symm]
  unfold taoCorputPhase taoCorputLogPhase
  have hphase : 2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (n : Real)) =
      -(t * Real.log (n : Real)) := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hphase]
  rw [Complex.exp_re]
  have hre : (((-(t * Real.log (n : Real)) : Real) : Complex) * Complex.I).re = 0 := by
    change (-(t * Real.log (n : Real))) * 0 - 0 * 1 = 0
    ring
  have him : (((-(t * Real.log (n : Real)) : Real) : Complex) * Complex.I).im =
      -(t * Real.log (n : Real)) := by
    change (-(t * Real.log (n : Real))) * 1 + 0 * 0 = -(t * Real.log (n : Real))
    ring
  rw [hre, him, Real.exp_zero, one_mul, Real.cos_neg]

theorem taoZetaTerm_re (σ t : Real) {n : Nat} (hn : 0 < n) :
    (taoZetaTerm σ t n).re =
      (n : Real) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hterm := taoDyadicWeight_complex_term n n hn hn le_rfl σ t
  rw [Nat.sub_self, taoDyadicWeight_zero hn, Complex.ofReal_one, mul_one] at hterm
  unfold taoZetaTerm
  rw [← hterm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, taoPureImaginaryCpow_re t hn]

theorem taoVonMangoldtLSeriesTerm_re (σ t : Real) {n : Nat} (hn : 0 < n) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
      ((σ : Complex) + (t : Complex) * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-σ) *
        Real.cos (t * Real.log n) := by
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hn), div_eq_mul_inv,
    ← Complex.cpow_neg, show -((σ : Complex) + (t : Complex) * Complex.I) =
      -((σ : Complex) + (t : Complex) * Complex.I) by rfl]
  change (((ArithmeticFunction.vonMangoldt n : Real) : Complex) *
    taoZetaTerm σ t n).re = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    taoZetaTerm_re σ t hn]
  ring

/-- Termwise source positivity before summing the von Mangoldt L-series. -/
theorem taoVonMangoldtLSeriesTerm_three_four_one_nonneg
    (σ t : Real) (n : Nat) :
    0 ≤ (3 * LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) (σ : Complex) n +
      4 * LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
          ((σ : Complex) + (t : Complex) * Complex.I) n +
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
          ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) n).re := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    simp only [Complex.add_re, Complex.mul_re]
    rw [show (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
        (σ : Complex) n).re = ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-σ) from by
          simpa using taoVonMangoldtLSeriesTerm_re σ 0 hn,
      taoVonMangoldtLSeriesTerm_re σ t hn,
      taoVonMangoldtLSeriesTerm_re σ (2 * t) hn]
    norm_num
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hpow : 0 ≤ (n : Real) ^ (-σ) := by positivity
    have htrig := taoZeta_three_four_one_nonneg (t * Real.log n)
    have htwo : (2 * t) * Real.log n = 2 * (t * Real.log n) := by ring
    rw [htwo]
    nlinarith [mul_nonneg (mul_nonneg hΛ hpow) htrig]

/-- Summed Euler-series positivity on `σ>1`, before replacing each
L-series by the canonical logarithmic derivative. -/
theorem taoVonMangoldtLSeries_three_four_one_nonneg
    (σ t : Real) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) (σ : Complex) +
      4 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
        ((σ : Complex) + (t : Complex) * Complex.I) +
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
        ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)).re := by
  let f0 : Nat → Complex := fun n => LSeries.term
    (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) (σ : Complex) n
  let f1 : Nat → Complex := fun n => LSeries.term
    (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
      ((σ : Complex) + (t : Complex) * Complex.I) n
  let f2 : Nat → Complex := fun n => LSeries.term
    (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
      ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) n
  let g : Nat → Complex := fun n => 3 * f0 n + 4 * f1 n + f2 n
  have hs0 : Summable f0 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : Complex)) (by simpa using hσ)
  have hs1 : Summable f1 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : Complex) + (t : Complex) * Complex.I) (by simpa using hσ)
  have hs2 : Summable f2 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) (by simpa using hσ)
  have hg : Summable g := (hs0.mul_left 3).add (hs1.mul_left 4) |>.add hs2
  have heq : (∑' n, g n) =
      3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) (σ : Complex) +
      4 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
        ((σ : Complex) + (t : Complex) * Complex.I) +
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
        ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) := by
    unfold g f0 f1 f2 LSeries
    rw [((hs0.mul_left 3).add (hs1.mul_left 4)).tsum_add hs2,
      (hs0.mul_left 3).tsum_add (hs1.mul_left 4), tsum_mul_left, tsum_mul_left]
  rw [← heq, Complex.re_tsum hg]
  exact tsum_nonneg fun n => taoVonMangoldtLSeriesTerm_three_four_one_nonneg σ t n

/-- Canonical logarithmic-derivative positivity, consuming the summed
von Mangoldt Euler-series theorem. -/
theorem taoZetaLogDerivative_three_four_one_nonneg
    (σ t : Real) (hσ : 1 < σ) :
    0 ≤ (3 * taoZetaLogDerivative (σ : Complex) +
      4 * taoZetaLogDerivative ((σ : Complex) + (t : Complex) * Complex.I) +
      taoZetaLogDerivative
        ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)).re := by
  rw [taoZetaLogDerivative_eq_vonMangoldtLSeries (by simpa using hσ),
    taoZetaLogDerivative_eq_vonMangoldtLSeries (by simpa using hσ),
    taoZetaLogDerivative_eq_vonMangoldtLSeries (by simpa using hσ)]
  exact taoVonMangoldtLSeries_three_four_one_nonneg σ t hσ

end

end Erdos1212Kernel
