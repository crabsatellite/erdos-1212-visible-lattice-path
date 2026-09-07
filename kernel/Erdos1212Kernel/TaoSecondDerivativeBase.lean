import Erdos1212Kernel.TaoSecondDerivativeOptimized
import Erdos1212Kernel.TaoSecondDerivativeNormalization

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1700000

theorem taoSecondDerivative_trivial_sum_bound (f : Real → Real) (a : Int) (M N : Nat)
    (hN : 0 < N) (hMN : M ≤ N) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤ 1 := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hM : (M : Real) ≤ N := by exact_mod_cast hMN
  have hnorm : ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ ≤ (M : Real) := by
    calc
      _ ≤ ∑ n ∈ taoCorputInterval a M, ‖taoCorputPhase (f (n : Real))‖ := norm_sum_le _ _
      _ = _ := by simp [taoCorputPhase_norm, taoCorputInterval, Int.card_Ico]
  apply (div_le_iff₀ hNp).2
  linarith

/-- The k=2 base of Tao's Proposition 10, in its displayed log(2+T)
normalization, with an explicit absolute constant. This consumes the
original FTC, first-derivative, and van der Corput proofs in every regime.
The interval remains the literal integer half-open interval of length M<=N. -/
theorem taoSecondDerivative_proposition10_base (f f' f'' f''' : Real → Real) (a : Int) (M N : Nat)
    {A T : Real} (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N)
    (hf : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f'' (f''' t) t)
    (hc''' : ContinuousOn f''' (Set.Icc (a : Real) (a + M)))
    (hfirst : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real)) ≤ |f' t| ∧ |f' t| ≤ A * T / (N : Real))
    (hsecond : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 2) ≤ |f'' t| ∧ |f'' t| ≤ A * T / (N : Real) ^ 2)
    (hthird : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 3) ≤ |f''' t| ∧ |f''' t| ≤ A * T / (N : Real) ^ 3) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤
      (16 * (2 + 2 * Real.pi)) * A ^ 2 * (Real.log (2 + T) / Real.sqrt T + Real.sqrt T / N) := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hAp : 0 < A := by linarith
  have hC : 1 ≤ 2 + 2 * Real.pi := by linarith [Real.pi_pos]
  have hR := taoSecondDerivative_rate_nonneg hNp hT
  have hP : 0 ≤ A ^ 2 * taoSecondDerivativeRate N T := mul_nonneg (sq_nonneg _) hR
  have htriv := taoSecondDerivative_trivial_sum_bound f a M N hN hMN
  have htwo : 2 * A ^ 2 * taoSecondDerivativeRate N T ≤
      (16 * (2 + 2 * Real.pi)) * A ^ 2 * taoSecondDerivativeRate N T := by
    have h := mul_le_mul_of_nonneg_right hC hP
    nlinarith
  change ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤
    (16 * (2 + 2 * Real.pi)) * A ^ 2 * taoSecondDerivativeRate N T
  by_cases hbigA : Real.sqrt T ≤ A ^ 2
  · exact htriv.trans ((taoSecondDerivative_trivial_large_A hA hNp hT hbigA).trans htwo)
  have hsmallA : A ^ 2 ≤ Real.sqrt T := (lt_of_not_ge hbigA).le
  by_cases hsmall : T ≤ (N : Real) / (2 * A)
  · have hNscale : 1 ≤ (N : Real) := by exact_mod_cast hN
    have hMscale : (M : Real) ≤ N := by exact_mod_cast hMN
    have hbase := taoFirstDerivative_scaled_sum_bound f f' f'' (a : Real) M hA hNscale hT hMscale hsmall
      hf hf' (fun t ht => (hfirst t ht).1) (fun t ht => (hfirst t ht).2) (fun t ht => (hsecond t ht).2)
    rw [← taoFirstDerivative_sum_Ico_eq_range f a M] at hbase
    have hcompare := mul_le_mul_of_nonneg_left
      (taoSecondDerivative_small_T_comparison hA hNp hT hsmallA) (show 0 ≤ 2 + 2 * Real.pi by positivity)
    have hCP : 0 ≤ (2 + 2 * Real.pi) * (A ^ 2 * taoSecondDerivativeRate N T) := by positivity
    apply hbase.trans
    calc
      _ = (2 + 2 * Real.pi) * (A ^ 3 / T) := by ring
      _ ≤ (2 + 2 * Real.pi) * (2 * A ^ 2 * taoSecondDerivativeRate N T) := hcompare
      _ ≤ _ := by nlinarith
  by_cases hlarge : (N : Real) ^ 2 / (2 * A) ≤ T
  · exact htriv.trans ((taoSecondDerivative_trivial_large_T hA hNp hT hlarge).trans htwo)
  have hlo := (lt_of_not_ge hsmall).le
  have hhi := (lt_of_not_ge hlarge).le
  exact (taoSecondDerivative_middle_bound f f' f'' f''' a M N hA hN hT hMN hlo hhi
    hf hf' hf'' hc''' hsecond hthird).trans
    (taoSecondDerivative_middle_rate_comparison hA hNp hT hC hsmallA hlo)

end

end Erdos1212Kernel
