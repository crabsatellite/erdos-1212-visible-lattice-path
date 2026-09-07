import Erdos1212Kernel.TaoCorputInequality
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

def taoCorputPhase (x : Real) : Complex := Complex.exp ((2 * Real.pi * x : Real) * Complex.I)

theorem taoCorputPhase_norm (x : Real) : ‖taoCorputPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem taoCorputPhase_sub (x y : Real) : taoCorputPhase (x - y) = taoCorputPhase x * star (taoCorputPhase y) := by
  unfold taoCorputPhase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

def taoCorputPhaseSequence (f : Int → Real) (a : Int) (N : Nat) (n : Int) : Complex :=
  if n ∈ taoCorputInterval a N then taoCorputPhase (f n) else 0

theorem taoCorputPhaseSequence_on (f : Int → Real) (a : Int) (N : Nat) {n : Int} (hn : n ∈ taoCorputInterval a N) :
    taoCorputPhaseSequence f a N n = taoCorputPhase (f n) := by simp only [taoCorputPhaseSequence, if_pos hn]

theorem taoCorputPhaseSequence_off (f : Int → Real) (a : Int) (N : Nat) {n : Int} (hn : n ∉ taoCorputInterval a N) :
    taoCorputPhaseSequence f a N n = 0 := by simp only [taoCorputPhaseSequence, if_neg hn]

theorem taoCorputPhaseSequence_sum (f : Int → Real) (a : Int) (N : Nat) :
    taoCorputSum (taoCorputPhaseSequence f a N) a N = ∑ n ∈ taoCorputInterval a N, taoCorputPhase (f n) := by
  unfold taoCorputSum
  apply Finset.sum_congr rfl
  intro n hn
  exact taoCorputPhaseSequence_on f a N hn

def taoCorputOverlap (a : Int) (N h : Nat) : Finset Int :=
  (taoCorputInterval a N).filter (fun n => n + h ∈ taoCorputInterval a N)

theorem taoCorputOverlap_eq_interval (a : Int) (N h : Nat) (hh : h ≤ N) :
    taoCorputOverlap a N h = taoCorputInterval a (N - h) := by
  ext n
  simp only [taoCorputOverlap, taoCorputInterval, Finset.mem_filter, Finset.mem_Ico, Nat.cast_sub hh]
  omega

/-- Exact transport to the source I intersect (I-h) and phase difference. -/
theorem taoCorputPhaseSequence_correlation (f : Int → Real) (a : Int) (N h : Nat) :
    taoCorputCorrelation (taoCorputPhaseSequence f a N) a N h =
      ∑ n ∈ taoCorputOverlap a N h, taoCorputPhase (f (n + h) - f n) := by
  unfold taoCorputCorrelation taoCorputOverlap
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [taoCorputPhaseSequence_on f a N hn]
  by_cases hh : n + h ∈ taoCorputInterval a N
  · rw [taoCorputPhaseSequence_on f a N hh, if_pos hh]
    exact (taoCorputPhase_sub _ _).symm
  · rw [taoCorputPhaseSequence_off f a N hh, zero_mul, if_neg hh]

/-- The literal integer-interval exponential-sum instance of Tao's
Proposition 7, with both normalizations and all overlaps retained. -/
theorem taoCorput_exponential_sum_bound (f : Int → Real) (a : Int) (N H : Nat) (hH : 0 < H) (hHN : H ≤ N) :
    ‖∑ n ∈ taoCorputInterval a N, taoCorputPhase (f n)‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ taoCorputOverlap a N h, taoCorputPhase (f (n + h) - f n)‖ / (N : Real))) := by
  have h := taoCorput_vdc_source_bound (taoCorputPhaseSequence f a N) a N H hH hHN
    (fun n hn => taoCorputPhaseSequence_off f a N hn) (by
      intro n hn
      rw [taoCorputPhaseSequence_on f a N hn, taoCorputPhase_norm])
  simpa only [taoCorputPhaseSequence_sum, taoCorputPhaseSequence_correlation] using h

end

end Erdos1212Kernel
