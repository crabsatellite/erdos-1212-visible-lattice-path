import Erdos1212Kernel.TaoShiftDifferenceScale
import Erdos1212Kernel.TaoFirstDerivativeInterval

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

theorem taoCorputOverlap_eq_empty_of_length_le (a : Int) (M h : Nat) (hh : M ≤ h) :
    taoCorputOverlap a M h = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  simp only [taoCorputOverlap, taoCorputInterval, Finset.mem_filter, Finset.mem_Ico] at hn
  omega

/-- The actual inner overlap sum in Proposition 9, derived from the
original three derivatives by FTC and the proved first-derivative estimate.
For shifts beyond the actual length, the overlap is proved empty. -/
theorem taoDifferenced_overlap_bound (f f' f'' f''' : Real → Real) (a : Int) (M N h : Nat)
    {A T : Real} (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N) (hh : 0 < h)
    (hsmall : (h : Real) * T / N ≤ (N : Real) / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f'' (f''' t) t)
    (hc''' : ContinuousOn f''' (Set.Icc (a : Real) (a + M)))
    (hsecond : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 2) ≤ |f'' t| ∧ |f'' t| ≤ A * T / (N : Real) ^ 2)
    (hthird : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 3) ≤ |f''' t| ∧ |f''' t| ≤ A * T / (N : Real) ^ 3) :
    ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (f ((n : Real) + h) - f n)‖ / (N : Real) ≤
      (2 + 2 * Real.pi) * A ^ 3 * N / (T * h) := by
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hhp : 0 < (h : Real) := by exact_mod_cast hh
  by_cases hhm : h ≤ M
  · have hnew : 0 < (h : Real) * T / N := by positivity
    have hscale : 1 ≤ (N : Real) := by exact_mod_cast hN
    have hlen : ((M - h : Nat) : Real) ≤ N := by exact_mod_cast (Nat.sub_le M h).trans hMN
    have hloc {x : Real} (hx : x ∈ Set.Icc (a : Real) ((a : Real) + (M - h : Nat))) :
        x ∈ Set.Icc (a : Real) (((a : Real) + M) - h) := by
      simpa only [Nat.cast_sub hhm, add_sub_assoc] using hx
    have hc'' : ContinuousOn f'' (Set.Icc (a : Real) ((a : Real) + M)) :=
      fun t ht => (hf'' t ht).continuousAt.continuousWithinAt
    have hb1 {x : Real} (hx : x ∈ Set.Icc (a : Real) ((a : Real) + (M - h : Nat))) :=
      taoShiftDifference_scaled_bounds f' f'' 1 hAp hNp hT hhp.le hf' hc''
        (fun t ht => (hsecond t ht).1) (fun t ht => (hsecond t ht).2) (hloc hx)
    have hb2 {x : Real} (hx : x ∈ Set.Icc (a : Real) ((a : Real) + (M - h : Nat))) :=
      taoShiftDifference_scaled_bounds f'' f''' 2 hAp hNp hT hhp.le hf'' hc'''
        (fun t ht => (hthird t ht).1) (fun t ht => (hthird t ht).2) (hloc hx)
    have hbase := taoFirstDerivative_scaled_sum_bound
      (taoShiftDifference f h) (taoShiftDifference f' h) (taoShiftDifference f'' h)
      (a : Real) (M - h) hA hscale hnew hlen hsmall
      (fun _x hx => taoShiftDifference_hasDerivAt f f' hhp.le hf (hloc hx))
      (fun _x hx => taoShiftDifference_hasDerivAt f' f'' hhp.le hf' (hloc hx))
      (fun _x hx => by simpa only [pow_one] using (hb1 hx).1)
      (fun _x hx => by simpa only [pow_one] using (hb1 hx).2)
      (fun _x hx => (hb2 hx).2)
    have hsum : (∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (f ((n : Real) + h) - f n)) =
        ∑ n ∈ Finset.range (M - h), taoCorputPhase (taoShiftDifference f h ((a : Real) + n)) := by
      rw [taoCorputOverlap_eq_interval a M h hhm]
      exact taoFirstDerivative_sum_Ico_eq_range (taoShiftDifference f h) a (M - h)
    rw [hsum]
    apply hbase.trans_eq
    field_simp
    <;> ring
  · rw [taoCorputOverlap_eq_empty_of_length_le a M h (by omega), Finset.sum_empty, norm_zero, zero_div]
    positivity

end

end Erdos1212Kernel
