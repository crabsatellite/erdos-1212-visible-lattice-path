import Erdos1212Kernel.TaoCorputShortInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

/-- The literal phase used for the zeta Dirichlet polynomial in the source. -/
def taoCorputLogPhase (t x : Real) : Real := -(t / (2 * Real.pi)) * Real.log x

theorem taoCorputLogPhase_shift (t : Real) {x h : Real} (hx : 0 < x) (hxh : 0 < x + h) :
    taoCorputLogPhase t (x + h) - taoCorputLogPhase t x =
      -(t / (2 * Real.pi)) * Real.log (1 + h / x) := by
  have he : 1 + h / x = (x + h) / x := by field_simp <;> ring
  rw [he, Real.log_div hxh.ne' hx.ne']
  unfold taoCorputLogPhase
  ring

theorem taoCorputLogPhase_hasDerivAt (t : Real) {x : Real} (hx : 0 < x) :
    HasDerivAt (taoCorputLogPhase t) (-t / (2 * Real.pi * x)) x := by
  have h := (Real.hasDerivAt_log hx.ne').const_mul (-(t / (2 * Real.pi)))
  apply h.congr_deriv
  ring

theorem taoCorputLogPhase_shift_hasDerivAt (t h : Real) {x : Real} (hx : 0 < x) (hxh : 0 < x + h) :
    HasDerivAt (fun y : Real => taoCorputLogPhase t (y + h) - taoCorputLogPhase t y)
      (t * h / (2 * Real.pi * x * (x + h))) x := by
  have hd := ((taoCorputLogPhase_hasDerivAt t hxh).comp x ((hasDerivAt_id x).add_const h)).sub
    (taoCorputLogPhase_hasDerivAt t hx)
  apply hd.congr_deriv
  simp only [mul_one]
  field_simp [hx.ne', hxh.ne', Real.pi_ne_zero]
  <;> ring

theorem taoCorputLogPhase_cpow (t : Real) {x : Real} (hx : 0 < x) :
    taoCorputPhase (taoCorputLogPhase t x) = (x : Complex) ^ (-(t : Complex) * Complex.I) := by
  have hxC : (x : Complex) ≠ 0 := by exact_mod_cast hx.ne'
  have he : 2 * Real.pi * taoCorputLogPhase t x = -t * Real.log x := by
    unfold taoCorputLogPhase
    field_simp [Real.pi_ne_zero]
    <;> ring
  unfold taoCorputPhase
  rw [he, Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- Direct source consumer for the actual logarithmic phase, with the
exact difference log(1+h/n) rather than an assumed derivative surrogate. -/
theorem taoCorput_logarithmic_sum_bound (t : Real) (a : Int) (N H : Nat)
    (ha : 1 ≤ a) (hH : 0 < H) (hHN : H ≤ N) :
    ‖∑ n ∈ taoCorputInterval a N, taoCorputPhase (taoCorputLogPhase t n)‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ taoCorputOverlap a N h,
          taoCorputPhase (-(t / (2 * Real.pi)) * Real.log (1 + (h : Real) / n))‖ / (N : Real))) := by
  have h := taoCorput_exponential_sum_bound (fun n : Int => taoCorputLogPhase t n) a N H hH hHN
  have hcorr (k : Nat) :
      (∑ n ∈ taoCorputOverlap a N k, taoCorputPhase (taoCorputLogPhase t (n + k : Int) - taoCorputLogPhase t n)) =
      ∑ n ∈ taoCorputOverlap a N k, taoCorputPhase (-(t / (2 * Real.pi)) * Real.log (1 + (k : Real) / n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    have hna := (Finset.mem_Ico.mp hnI).1
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast (show (0 : Int) < n by omega)
    have hsum : (0 : Real) < (n : Real) + k := by positivity
    rw [Int.cast_add, Int.cast_natCast, taoCorputLogPhase_shift t hn0 hsum]
  simpa only [hcorr] using h

theorem taoCorput_dirichlet_sum_bound (t : Real) (a : Int) (N H : Nat)
    (ha : 1 ≤ a) (hH : 0 < H) (hHN : H ≤ N) :
    ‖∑ n ∈ taoCorputInterval a N, (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ taoCorputOverlap a N h,
          taoCorputPhase (-(t / (2 * Real.pi)) * Real.log (1 + (h : Real) / n))‖ / (N : Real))) := by
  have h := taoCorput_logarithmic_sum_bound t a N H ha hH hHN
  have hsum : (∑ n ∈ taoCorputInterval a N, taoCorputPhase (taoCorputLogPhase t n)) =
      ∑ n ∈ taoCorputInterval a N, (n : Complex) ^ (-(t : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast (show (0 : Int) < n by omega)
    simpa using taoCorputLogPhase_cpow t hn0
  rwa [hsum] at h

/-- Short Dirichlet sums retain the ambient scale N used in the source
zeta reduction; it is not replaced by the shorter length M. -/
theorem taoCorput_short_dirichlet_sum_bound (t : Real) (a : Int) (M N H : Nat)
    (ha : 1 ≤ a) (hMN : M ≤ N) (hH : 0 < H) (hHN : H ≤ N) :
    ‖∑ n ∈ taoCorputInterval a M, (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ taoCorputOverlap a M h,
          taoCorputPhase (-(t / (2 * Real.pi)) * Real.log (1 + (h : Real) / n))‖ / (N : Real))) := by
  have h := taoCorput_short_exponential_sum_bound (fun n : Int => taoCorputLogPhase t n) a M N H hMN hH hHN
  have hsum : (∑ n ∈ taoCorputInterval a M, taoCorputPhase (taoCorputLogPhase t n)) =
      ∑ n ∈ taoCorputInterval a M, (n : Complex) ^ (-(t : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast (show (0 : Int) < n by omega)
    simpa using taoCorputLogPhase_cpow t hn0
  have hcorr (k : Nat) :
      (∑ n ∈ taoCorputOverlap a M k, taoCorputPhase (taoCorputLogPhase t (n + k : Int) - taoCorputLogPhase t n)) =
      ∑ n ∈ taoCorputOverlap a M k, taoCorputPhase (-(t / (2 * Real.pi)) * Real.log (1 + (k : Real) / n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    have hna := (Finset.mem_Ico.mp hnI).1
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast (show (0 : Int) < n by omega)
    have hnk : (0 : Real) < (n : Real) + k := by positivity
    rw [Int.cast_add, Int.cast_natCast, taoCorputLogPhase_shift t hn0 hnk]
  simpa only [hsum, hcorr] using h

end

end Erdos1212Kernel
