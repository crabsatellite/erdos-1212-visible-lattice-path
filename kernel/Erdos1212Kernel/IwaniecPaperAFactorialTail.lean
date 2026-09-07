import Erdos1212Kernel.IwaniecPaperAElementaryLayers
import Mathlib.Algebra.Order.Field.GeomSum

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecFactorialTerm (M : Real) (k : Nat) : Real := M ^ k / k.factorial

theorem iwaniecFactorialTerm_nonneg {M : Real} (hM : 0 ≤ M) (k : Nat) :
    0 ≤ iwaniecFactorialTerm M k := by
  unfold iwaniecFactorialTerm
  positivity

theorem iwaniecFactorialTerm_succ (M : Real) (k : Nat) :
    iwaniecFactorialTerm M (k + 1) =
      (M / (k + 1 : Nat)) * iwaniecFactorialTerm M k := by
  unfold iwaniecFactorialTerm
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem iwaniecFactorialTerm_succ_le_half
    {M : Real} (hM : 0 ≤ M) (k : Nat) (hthreshold : 2 * M ≤ (k + 1 : Nat)) :
    iwaniecFactorialTerm M (k + 1) ≤ (1 / 2 : Real) * iwaniecFactorialTerm M k := by
  rw [iwaniecFactorialTerm_succ]
  apply mul_le_mul_of_nonneg_right _ (iwaniecFactorialTerm_nonneg hM k)
  rw [div_le_iff₀ (by positivity : (0 : Real) < (k + 1 : Nat))]
  linarith

theorem iwaniecFactorialTerm_shift_le_geometric
    {M : Real} (hM : 0 ≤ M) (K j : Nat)
    (hthreshold : 2 * M ≤ (K + 1 : Nat)) :
    iwaniecFactorialTerm M (K + j) ≤
      iwaniecFactorialTerm M K * (1 / 2 : Real) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hKj : ((K + 1 : Nat) : Real) ≤ (K + j + 1 : Nat) := by
        exact_mod_cast (show K + 1 ≤ K + j + 1 by omega)
      have hstep := iwaniecFactorialTerm_succ_le_half hM (K + j)
        (hthreshold.trans hKj)
      have hscaled := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : Real) ≤ 1 / 2)
      simp only [Nat.add_succ, pow_succ]
      nlinarith

/-- The entire finite factorial tail is at most twice its first term once
`K+1 ≥ 2M`; no hidden tail summability premise is required. -/
theorem iwaniecFactorialTerm_sum_tail_le
    {M : Real} (hM : 0 ≤ M) (K upper : Nat)
    (hthreshold : 2 * M ≤ (K + 1 : Nat)) :
    (∑ k ∈ Finset.Ico K upper, iwaniecFactorialTerm M k) ≤
      2 * iwaniecFactorialTerm M K := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hgeom : (∑ j ∈ Finset.range (upper - K), (1 / 2 : Real) ^ j) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : Real))
      (m := 0) (n := upper - K) (by norm_num) (by norm_num)
    norm_num at h
    simpa using h
  calc
    (∑ j ∈ Finset.range (upper - K), iwaniecFactorialTerm M (K + j)) ≤
        ∑ j ∈ Finset.range (upper - K),
          iwaniecFactorialTerm M K * (1 / 2 : Real) ^ j :=
      Finset.sum_le_sum (fun j _hj =>
        iwaniecFactorialTerm_shift_le_geometric hM K j hthreshold)
    _ = iwaniecFactorialTerm M K *
        ∑ j ∈ Finset.range (upper - K), (1 / 2 : Real) ^ j := by rw [Finset.mul_sum]
    _ ≤ iwaniecFactorialTerm M K * 2 :=
      mul_le_mul_of_nonneg_left hgeom (iwaniecFactorialTerm_nonneg hM K)
    _ = 2 * iwaniecFactorialTerm M K := by ring

theorem iwaniecCubicRealProductCount_sum_tail_le
    (offset : Nat) (level : Real) (factors : List Nat) (K upper : Nat)
    (hlevel : 0 ≤ level) (hpositive : ∀ p ∈ factors, 0 < p)
    (hthreshold : 2 * (factors.map (fun p : Nat => (p : Real)⁻¹)).sum ≤ (K + 1 : Nat)) :
    (∑ k ∈ Finset.Ico K upper,
      (iwaniecCubicRealProductCount offset level factors k : Real)) ≤
        2 * level * (factors.map (fun p : Nat => (p : Real)⁻¹)).sum ^ K / K.factorial := by
  let M := (factors.map (fun p : Nat => (p : Real)⁻¹)).sum
  have hM : 0 ≤ M := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    positivity
  have htail := iwaniecFactorialTerm_sum_tail_le hM K upper hthreshold
  have hpoint : ∀ k : Nat,
      (iwaniecCubicRealProductCount offset level factors k : Real) ≤
        level * iwaniecFactorialTerm M k := by
    intro k
    have h := iwaniecCubicRealProductCount_le_reciprocal_factorial
      offset level factors k hlevel hpositive
    simpa only [M, iwaniecFactorialTerm, mul_div_assoc] using h
  calc
    (∑ k ∈ Finset.Ico K upper,
        (iwaniecCubicRealProductCount offset level factors k : Real)) ≤
        ∑ k ∈ Finset.Ico K upper, level * iwaniecFactorialTerm M k :=
      Finset.sum_le_sum (fun k _hk => hpoint k)
    _ = level * ∑ k ∈ Finset.Ico K upper, iwaniecFactorialTerm M k := by
      rw [Finset.mul_sum]
    _ ≤ level * (2 * iwaniecFactorialTerm M K) :=
      mul_le_mul_of_nonneg_left htail hlevel
    _ = _ := by unfold iwaniecFactorialTerm M; ring

end

end Erdos1212Kernel
