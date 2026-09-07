import Erdos1212Kernel.DeBruijnVolterraOscillationContraction
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnVolterraOddDefect (k : Nat) : Real := 1 / (8 * (2 * (k : Real) + 3))

def deBruijnVolterraOddProduct (n : Nat) : Real := ∏ k ∈ Finset.range n, (1 - deBruijnVolterraOddDefect k)

theorem deBruijnVolterraOddDefect_bounds (k : Nat) :
    0 ≤ deBruijnVolterraOddDefect k ∧ deBruijnVolterraOddDefect k ≤ 1 / 24 := by
  have hk : 0 ≤ (k : Real) := Nat.cast_nonneg k
  constructor
  · unfold deBruijnVolterraOddDefect
    positivity
  · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : Real) < 24) (by nlinarith)

theorem deBruijnVolterra_odd_step {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) (k : Nat) :
    deBruijnVolterraOscillation f (2 * (k : Real) + 3) ≤
      (1 - deBruijnVolterraOddDefect k) * deBruijnVolterraOscillation f (2 * (k : Real) + 1) := by
  have hk : 0 ≤ (k : Real) := Nat.cast_nonneg k
  have h := deBruijnVolterra_two_step_contraction hf heq (n := 2 * (k : Real) + 1) (γ := (1 / 8 : Real))
    (by linarith) (by norm_num)
  have hdiv : (1 / 8 : Real) / (2 * (k : Real) + 1 + 2) = deBruijnVolterraOddDefect k := by
    unfold deBruijnVolterraOddDefect
    field_simp
    <;> ring
  have hcoef : (3 : Real) / (4 * (1 - 1 / 8)) ≤ 1 - deBruijnVolterraOddDefect k := by
    have hb := (deBruijnVolterraOddDefect_bounds k).2
    norm_num at ⊢
    linarith
  rw [hdiv, max_eq_right hcoef] at h
  convert h using 1 <;> congr 1 <;> ring

theorem deBruijnVolterraOddProduct_nonneg (n : Nat) : 0 ≤ deBruijnVolterraOddProduct n := by
  apply Finset.prod_nonneg
  intro k _hk
  have h := (deBruijnVolterraOddDefect_bounds k).2
  linarith

theorem deBruijnVolterra_odd_product_bound {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) (n : Nat) :
    deBruijnVolterraOscillation f (2 * (n : Real) + 1) ≤
      deBruijnVolterraOddProduct n * deBruijnVolterraOscillation f 1 := by
  induction n with
  | zero => simpa only [Nat.cast_zero, mul_zero, zero_add, deBruijnVolterraOddProduct, Finset.range_zero,
      Finset.prod_empty, one_mul] using (le_refl (deBruijnVolterraOscillation f 1))
  | succ n ih =>
      have hp : deBruijnVolterraOddProduct (n + 1) = deBruijnVolterraOddProduct n * (1 - deBruijnVolterraOddDefect n) :=
        Finset.prod_range_succ _ _
      rw [Nat.cast_add, Nat.cast_one, show 2 * ((n : Real) + 1) + 1 = 2 * (n : Real) + 3 by ring, hp]
      have hn : 0 ≤ 1 - deBruijnVolterraOddDefect n := by
        have hb := (deBruijnVolterraOddDefect_bounds n).2
        linarith
      calc
        _ ≤ (1 - deBruijnVolterraOddDefect n) * deBruijnVolterraOscillation f (2 * (n : Real) + 1) :=
          deBruijnVolterra_odd_step hf heq n
        _ ≤ (1 - deBruijnVolterraOddDefect n) * (deBruijnVolterraOddProduct n * deBruijnVolterraOscillation f 1) :=
          mul_le_mul_of_nonneg_left ih hn
        _ = _ := by ring

theorem deBruijnVolterraOddProduct_exp_bound (n : Nat) :
    deBruijnVolterraOddProduct n ≤ Real.exp (-(∑ k ∈ Finset.range n, deBruijnVolterraOddDefect k)) := by
  calc
    _ ≤ ∏ k ∈ Finset.range n, Real.exp (-deBruijnVolterraOddDefect k) := by
      apply Finset.prod_le_prod
      · intro k _hk
        have h := (deBruijnVolterraOddDefect_bounds k).2
        linarith
      · intro k _hk
        have h := Real.add_one_le_exp (-deBruijnVolterraOddDefect k)
        linarith
    _ = Real.exp (∑ k ∈ Finset.range n, -deBruijnVolterraOddDefect k) := (Real.exp_sum _ _).symm
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem deBruijnVolterraOddDefect_harmonic_lower (k : Nat) :
    (1 / 24 : Real) * (1 / ((k : Real) + 1)) ≤ deBruijnVolterraOddDefect k := by
  have hk : 0 ≤ (k : Real) := Nat.cast_nonneg k
  calc
    _ = 1 / (24 * ((k : Real) + 1)) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < 8 * (2 * (k : Real) + 3)) (by nlinarith)

theorem tendsto_deBruijnVolterraOddDefect_sum :
    Tendsto (fun n : Nat => ∑ k ∈ Finset.range n, deBruijnVolterraOddDefect k) atTop atTop := by
  have hlow : ∀ n : Nat, (1 / 24 : Real) * (∑ k ∈ Finset.range n, (1 / ((k : Real) + 1))) ≤
      ∑ k ∈ Finset.range n, deBruijnVolterraOddDefect k := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _hk => deBruijnVolterraOddDefect_harmonic_lower k)
  exact tendsto_atTop_mono hlow (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (by norm_num))

theorem tendsto_deBruijnVolterraOddProduct : Tendsto deBruijnVolterraOddProduct atTop (nhds 0) := by
  exact squeeze_zero deBruijnVolterraOddProduct_nonneg deBruijnVolterraOddProduct_exp_bound
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_deBruijnVolterraOddDefect_sum)

end

end Erdos1212Kernel
