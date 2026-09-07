import Erdos1212Kernel.AlgebraicCorridorBandScale
import Erdos1212Kernel.VaughanSupportRadiusLogarithmic
import Erdos1212Kernel.AlgebraicCorridorSupportColumns

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def bandPrimeStateRank (N : ℝ) : ℕ :=
  Nat.ceil (bandPrimeStateConstant * ell N ^ 3)

/-- The precise support distance is eventually absorbed by the paper's
`D_N = ceil(log(N)^11)` scale for every band prime state at that scale. -/
theorem eventually_vaughan_support_product_le_supportGap :
    ∀ᶠ N : ℝ in atTop, ∀ (R : Finset ℕ),
      R.card ≤ bandPrimeStateRank N → (∀ q ∈ R, q.Prime) →
      Nat.nth Nat.Prime R.card * vaughanPolynomialPrimeStateGap R + 1 ≤
        supportGap N := by
  obtain ⟨C, c, hC, hbound⟩ := exists_vaughan_support_product_cubic_log_bound
  let D1 : ℝ := bandPrimeStateConstant + 2
  let D2 : ℝ := bandPrimeStateConstant + c + 3
  let D3 : ℝ := Real.log D2 + 3
  let Ctotal : ℝ := C * D1 * D2 ^ 2 * D3 ^ 5
  have hD1 : 0 < D1 := by dsimp [D1]; linarith [bandPrimeStateConstant_pos]
  have hD2 : 1 < D2 := by dsimp [D2]; linarith [bandPrimeStateConstant_pos]
  have hD3 : 0 < D3 := by
    dsimp [D3]
    have := Real.log_pos hD2
    linarith
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell Ctotal 5] with N hdom hsmall R hcard hprime
  have hell : 1 ≤ ell N := hdom.2.1
  have hL : 1 ≤ L N := hdom.2.2
  have hellPos : 0 < ell N := zero_lt_one.trans_le hell
  let M := bandPrimeStateRank N
  let S : ℝ := (M + c + 2 : ℕ)
  have hMceil : (M : ℝ) ≤ bandPrimeStateConstant * ell N ^ 3 + 1 := by
    dsimp [M, bandPrimeStateRank]
    exact (Nat.ceil_lt_add_one
      (mul_nonneg bandPrimeStateConstant_pos.le (pow_nonneg hellPos.le 3))).le
  have hellCube : (1 : ℝ) ≤ ell N ^ 3 := one_le_pow₀ hell
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ D1 * ell N ^ 3 := by
    dsimp [D1]
    push_cast
    nlinarith
  have hS : S ≤ D2 * ell N ^ 3 := by
    dsimp [S, D2]
    push_cast
    nlinarith
  have hSgeOne : (1 : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast (show 1 ≤ M + c + 2 by omega)
  have hSPos : 0 < S := zero_lt_one.trans_le hSgeOne
  have hlogSNonneg : 0 ≤ Real.log S := Real.log_nonneg hSgeOne
  have hlogS : Real.log S ≤ D3 * L N := by
    have hrightPos : 0 < D2 * ell N ^ 3 := by positivity
    have hmono := Real.log_le_log hSPos hS
    have hlogProduct : Real.log (D2 * ell N ^ 3) =
        Real.log D2 + 3 * L N := by
      rw [Real.log_mul (by positivity : D2 ≠ 0) (pow_ne_zero 3 hellPos.ne'),
        Real.log_pow]
      rw [show Real.log (ell N) = L N by rfl]
      norm_num
    rw [hlogProduct] at hmono
    dsimp [D3]
    have hlogD2 : 0 ≤ Real.log D2 := (Real.log_pos hD2).le
    nlinarith
  have hraw := hbound M R hcard hprime
  have hmajor : C * (M + 1 : ℕ) * S ^ 2 * Real.log S ^ 5 ≤
      Ctotal * ell N ^ 9 * L N ^ 5 := by
    have hS2 := pow_le_pow_left₀ hSPos.le hS 2
    have hlog5 := pow_le_pow_left₀ hlogSNonneg hlogS 5
    have hnonneg1 : 0 ≤ ((M + 1 : ℕ) : ℝ) := by positivity
    have hnonnegS : 0 ≤ S ^ 2 := sq_nonneg S
    have hstep := mul_le_mul
      (mul_le_mul (mul_le_mul le_rfl hM1 (by positivity) hC.le)
        hS2 hnonnegS (by positivity))
      hlog5 (pow_nonneg hlogSNonneg 5) (by positivity)
    dsimp [Ctotal]
    calc
      _ ≤ (C * (D1 * ell N ^ 3) * (D2 * ell N ^ 3) ^ 2) *
          (D3 * L N) ^ 5 := by simpa only [mul_assoc] using hstep
      _ = _ := by ring
  have hten : ell N ^ 10 ≤ ell N ^ 11 := by
    have := pow_le_pow_right₀ hell (by norm_num : 10 ≤ 11)
    exact this
  have hstrict : Ctotal * ell N ^ 9 * L N ^ 5 < ell N ^ 10 := by
    have hscaled := mul_lt_mul_of_pos_right hsmall (pow_pos hellPos 9)
    convert hscaled using 1 <;> ring
  have hceil : ell N ^ 11 ≤ (supportGap N : ℝ) := by
    unfold supportGap
    exact Nat.le_ceil _
  have hfinalReal :
      ((Nat.nth Nat.Prime R.card * vaughanPolynomialPrimeStateGap R + 1 : ℕ) : ℝ) <
        (supportGap N : ℝ) :=
    (((hraw.trans hmajor).trans_lt hstrict).trans_le hten).trans_le hceil
  exact_mod_cast hfinalReal.le

theorem eventually_two_supportGap_add_two_le_half :
    ∀ᶠ N : ℝ in atTop,
      2 * supportGap N + 2 ≤ Nat.floor (N / 2) := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_ell_pow_lt_N 20 11] with N hdom hsmall
  have hell : 1 ≤ ell N := hdom.2.1
  have hgapUpper : (supportGap N : ℝ) ≤ ell N ^ 11 + 1 := by
    unfold supportGap
    exact (Nat.ceil_lt_add_one (pow_nonneg (zero_le_one.trans hell) 11)).le
  have hp : (1 : ℝ) ≤ ell N ^ 11 := one_le_pow₀ hell
  have hreal : ((2 * supportGap N + 2 : ℕ) : ℝ) ≤ N / 2 := by
    push_cast
    nlinarith
  exact Nat.le_floor hreal

/-- Scale-specialized version of the paper's support lemma for the actual
prime-factor state of a band in `[N/2,4N]`. -/
theorem eventually_actual_band_safe_supports :
    ∀ᶠ N : ℝ in atTop, ∀ (lower x : ℕ),
      1 < lower → lower + band N - 1 ≤ Nat.floor (4 * N) →
      Nat.floor (N / 2) ≤ x →
      ∃ west east : ℕ,
        west < x ∧ x < east ∧ west < east ∧
        x ≤ west + supportGap N ∧ east ≤ x + supportGap N ∧
        (∀ y, CorridorBandPoint lower (band N) {x := west, y := y} →
          SafePoint {x := west, y := y}) ∧
        (∀ y, CorridorBandPoint lower (band N) {x := east, y := y} →
          SafePoint {x := east, y := y}) := by
  filter_upwards [eventually_bandPrimeState_card_le,
    eventually_vaughan_support_product_le_supportGap,
    eventually_two_supportGap_add_two_le_half] with N hcardScale hgapScale hsmall
  intro lower x hlower hupper hx
  let Q := corridorBandPrimeFactors lower (band N)
  let J := vaughanPolynomialPrimeStateGap Q
  have hQprime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    exact prime_of_mem_corridorBandPrimeFactors hq
  have hQcard : Q.card ≤ bandPrimeStateRank N := hcardScale lower hlower hupper
  have hJgap : PrimeStateCoprimeGapBound Q J :=
    vaughanPolynomial_primeStateCoprimeGapBound Q hQprime
  have hprod : Nat.nth Nat.Prime Q.card * J + 1 ≤ supportGap N :=
    hgapScale Q hQcard hQprime
  have hJpos : 0 < J := hJgap.1
  have hnthLeProd : Nat.nth Nat.Prime Q.card ≤
      Nat.nth Nat.Prime Q.card * J := by
    nlinarith
  have hleft : Nat.nth Nat.Prime Q.card +
      Nat.nth Nat.Prime Q.card * J + 2 ≤ x := by
    have hxSmall := hsmall.trans hx
    omega
  exact exists_vaughan_safe_support_columns hlower le_rfl hJgap hleft hprod

end

end Erdos1212Kernel.CorridorScale
