import Erdos1212Kernel.TaoZetaEulerFiniteTail

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoZetaEuler_integral_formula {s : Complex} {a b : Real}
    (hs1 : s ≠ 1) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, taoZetaEulerKernel s x) =
      ((b : Complex) ^ (1 - s) - (a : Complex) ^ (1 - s)) / (1 - s) := by
  have hzero : (0 : Real) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  have h := integral_cpow (a := a) (b := b) (r := -s)
    (Or.inr ⟨fun h => hs1 (neg_inj.mp h), hzero⟩)
  unfold taoZetaEulerKernel
  have hexp : -s + 1 = 1 - s := by ring
  rw [hexp] at h
  exact h

theorem taoZetaEuler_finite_truncation_error {s : Complex} {a : Real}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (ha : 1 ≤ a) (M : Nat) :
    ‖(∑ m ∈ Finset.range M, taoZetaEulerKernel s (a + m)) -
        (((a : Complex) ^ (1 - s) - ((a + M : Real) : Complex) ^ (1 - s)) / (s - 1))‖ ≤
      ‖s‖ * a ^ (-s.re) * (1 + 1 / s.re) := by
  have htail := taoZetaEuler_finite_tail_error hs ha M
  have hint := taoZetaEuler_integral_formula hs1 (by linarith : 0 < a)
    (show a ≤ a + M by
      have hM : (0 : Real) ≤ M := by positivity
      exact le_add_of_nonneg_right hM)
  rw [hint] at htail
  have hfrac : (((a + M : Real) : Complex) ^ (1 - s) - (a : Complex) ^ (1 - s)) / (1 - s) =
      ((a : Complex) ^ (1 - s) - ((a + M : Real) : Complex) ^ (1 - s)) / (s - 1) := by
    rw [show 1 - s = -(s - 1) by ring, div_neg]
    congr 1
    ring
  rw [hfrac] at htail
  exact htail

def taoZetaEulerApprox (s : Complex) (N : Nat) : Complex :=
  (∑ n ∈ Finset.Ico 1 N, (n : Complex) ^ (-s)) +
    (N : Complex) ^ (1 - s) / (s - 1)

theorem taoZetaEulerApprox_sub {s : Complex} {A B : Nat}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hA : 1 ≤ A) (hAB : A ≤ B) :
    ‖taoZetaEulerApprox s B - taoZetaEulerApprox s A‖ ≤
      ‖s‖ * (A : Real) ^ (-s.re) * (1 + 1 / s.re) := by
  have hsum : (∑ n ∈ Finset.Ico 1 B, (n : Complex) ^ (-s)) -
      (∑ n ∈ Finset.Ico 1 A, (n : Complex) ^ (-s)) =
      ∑ n ∈ Finset.Ico A B, (n : Complex) ^ (-s) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ A) hAB]
    abel
  have hrange : (∑ n ∈ Finset.Ico A B, (n : Complex) ^ (-s)) =
      ∑ m ∈ Finset.range (B - A), taoZetaEulerKernel s ((A : Real) + m) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m _hm
    unfold taoZetaEulerKernel
    norm_cast
  have hAR : (1 : Real) ≤ A := by exact_mod_cast hA
  have htail := taoZetaEuler_finite_truncation_error hs hs1 hAR (B - A)
  rw [← hrange] at htail
  have hcast : ((A : Real) + (B - A : Nat) : Real) = B := by
    rw [Nat.cast_sub hAB]
    push_cast
    ring
  rw [hcast] at htail
  have heq : taoZetaEulerApprox s B - taoZetaEulerApprox s A =
      (∑ n ∈ Finset.Ico A B, (n : Complex) ^ (-s)) -
        (((A : Complex) ^ (1 - s) - (B : Complex) ^ (1 - s)) / (s - 1)) := by
    unfold taoZetaEulerApprox
    calc
      _ = ((∑ n ∈ Finset.Ico 1 B, (n : Complex) ^ (-s)) -
          (∑ n ∈ Finset.Ico 1 A, (n : Complex) ^ (-s))) -
          (((A : Complex) ^ (1 - s) - (B : Complex) ^ (1 - s)) / (s - 1)) := by ring
      _ = _ := by rw [hsum]
  rw [heq]
  exact htail

end

end Erdos1212Kernel
