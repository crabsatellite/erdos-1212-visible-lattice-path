import Erdos1212Kernel.IwaniecAuxiliaryConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxInitial_continuousAt
    (sigma : Real) {s : Real} (hs : 1 < s) :
    ContinuousAt (iwaniecAuxInitial sigma) s := by
  have hshift : ContinuousAt (fun t : Real => t - 1) s :=
    continuousAt_id.sub continuousAt_const
  have hne : s - 1 ≠ 0 := by linarith
  exact (continuousAt_const.add (hshift.inv₀ hne)).sub (hshift.log hne)

theorem iwaniecAuxBase_continuousAt
    (sigma : Real) {s : Real} (hs : 1 < s) :
    ContinuousAt (iwaniecAuxBase sigma) s := by
  have hmin : 1 < min s (3 : Real) := lt_min hs (by norm_num)
  exact (iwaniecAuxInitial_continuousAt sigma hmin).comp (f := fun u : Real => min u 3)
    (continuousAt_id.min continuousAt_const)

theorem iwaniecAuxDelayKernel_continuousAt
    {s : Real} (hs : 1 < s) :
    ContinuousAt iwaniecAuxDelayKernel s := by
  unfold iwaniecAuxDelayKernel
  exact continuousAt_id.div ((continuousAt_id.sub continuousAt_const).pow 2)
    (pow_ne_zero 2 (by linarith : s - 1 ≠ 0))

def iwaniecAuxIntegrand (sigma : Real) (n : Nat) (t : Real) : Real :=
  iwaniecAuxDelayKernel t * iwaniecAuxApprox sigma n (t - 1)

theorem iwaniecAuxIntegrand_continuousOn_of_approx
    (sigma : Real) (n : Nat)
    (happrox : ContinuousOn (iwaniecAuxApprox sigma n) (Set.Ioi (1 : Real))) :
    ContinuousOn (iwaniecAuxIntegrand sigma n) (Set.Ioi (2 : Real)) := by
  intro t ht
  have htTwo : 2 < t := ht
  have hshift : ContinuousAt (fun s : Real => s - 1) t :=
    continuousAt_id.sub continuousAt_const
  have harg : 1 < t - 1 := by linarith
  have hvalue := (happrox.continuousAt (Ioi_mem_nhds harg)).comp
    (f := fun s : Real => s - 1) hshift
  exact ((iwaniecAuxDelayKernel_continuousAt (s := t) (by linarith)).mul hvalue).continuousWithinAt

theorem iwaniecAuxIntegrand_intervalIntegrable_of_approx
    (sigma : Real) (n : Nat)
    (happrox : ContinuousOn (iwaniecAuxApprox sigma n) (Set.Ioi (1 : Real)))
    {a b : Real} (ha : 2 < a) (hb : 2 < b) :
    IntervalIntegrable (iwaniecAuxIntegrand sigma n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (iwaniecAuxIntegrand_continuousOn_of_approx sigma n happrox).mono
  intro t ht
  exact lt_of_lt_of_le (lt_min ha hb) ht.1

theorem iwaniecAuxPrimitive_hasDerivAt_of_approx
    (sigma : Real) (n : Nat)
    (happrox : ContinuousOn (iwaniecAuxApprox sigma n) (Set.Ioi (1 : Real)))
    {s : Real} (hs : 2 < s) :
    HasDerivAt (fun u : Real => ∫ t in (3 : Real)..u, iwaniecAuxIntegrand sigma n t)
      (iwaniecAuxIntegrand sigma n s) s := by
  have hcont := iwaniecAuxIntegrand_continuousOn_of_approx sigma n happrox
  exact intervalIntegral.integral_hasDerivAt_right
    (iwaniecAuxIntegrand_intervalIntegrable_of_approx sigma n happrox (by norm_num) hs)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hcont.continuousAt (Ioi_mem_nhds hs))

theorem iwaniecAuxApprox_continuousOn (sigma : Real) (n : Nat) :
    ContinuousOn (iwaniecAuxApprox sigma n) (Set.Ioi (1 : Real)) := by
  induction n with
  | zero =>
      intro s hs
      exact (iwaniecAuxBase_continuousAt sigma hs).continuousWithinAt
  | succ n ih =>
      intro s hs
      have hsOne : 1 < s := hs
      have hv : 2 < max (3 : Real) s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hprim := (iwaniecAuxPrimitive_hasDerivAt_of_approx sigma n ih hv).continuousAt
      have hmax : ContinuousAt (fun u : Real => max 3 u) s :=
        continuousAt_const.max continuousAt_id
      have hint := hprim.comp hmax
      have hsum := (iwaniecAuxBase_continuousAt sigma hsOne).add
        ((show ContinuousAt (fun _u : Real => sigma) s from continuousAt_const).mul hint)
      exact hsum.continuousWithinAt

theorem iwaniecAuxApprox_succ_hasDerivAt
    (sigma : Real) (n : Nat) {s : Real} (hs : 3 < s) :
    HasDerivAt (iwaniecAuxApprox sigma (n + 1))
      (sigma * iwaniecAuxIntegrand sigma n s) s := by
  have hprim := iwaniecAuxPrimitive_hasDerivAt_of_approx sigma n
    (iwaniecAuxApprox_continuousOn sigma n) (by linarith : 2 < s)
  let model := fun u : Real => iwaniecAuxInitial sigma 3 +
    sigma * ∫ t in (3 : Real)..u, iwaniecAuxIntegrand sigma n t
  have hmodel : HasDerivAt model (sigma * iwaniecAuxIntegrand sigma n s) s := by
    simpa only [model, zero_add] using
      (hasDerivAt_const s (iwaniecAuxInitial sigma 3)).add (hprim.const_mul sigma)
  have heq : iwaniecAuxApprox sigma (n + 1) =ᶠ[nhds s] model := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    change (3 : Real) < u at hu
    simp only [iwaniecAuxApprox, iwaniecAuxBase, model,
      min_eq_right hu.le, max_eq_right hu.le, iwaniecAuxIntegrand]
  exact hmodel.congr_of_eventuallyEq heq

theorem iwaniecAuxFunction_continuousOn (sigma : Real) :
    ContinuousOn (iwaniecAuxFunction sigma) (Set.Ioi (1 : Real)) := by
  intro s hs
  have hceil := Nat.le_ceil s
  have heq := iwaniecAuxFunction_eventuallyEq_approx sigma ⌈s⌉₊ (by linarith)
  have hcont := (iwaniecAuxApprox_continuousOn sigma ⌈s⌉₊).continuousAt
    (Ioi_mem_nhds hs)
  exact (hcont.congr_of_eventuallyEq heq).continuousWithinAt

/-- Premise-free delay equation for the constructed function.  Local exact
stabilization removes the ceiling from both the derivative and its lag. -/
theorem iwaniecAuxFunction_hasDerivAt
    (sigma : Real) {s : Real} (hs : 3 < s) :
    HasDerivAt (iwaniecAuxFunction sigma)
      (sigma * iwaniecAuxDelayKernel s * iwaniecAuxFunction sigma (s - 1)) s := by
  let n := ⌈s⌉₊
  have hceil : s ≤ (n : Real) := Nat.le_ceil s
  have heq := iwaniecAuxFunction_eventuallyEq_approx sigma (n + 1) (by
    push_cast
    linarith)
  have hderiv := (iwaniecAuxApprox_succ_hasDerivAt sigma n hs).congr_of_eventuallyEq heq
  have hlag := iwaniecAuxFunction_eq_approx sigma n (s := s - 1) (by linarith)
  rw [hlag]
  simpa only [iwaniecAuxIntegrand, mul_assoc] using hderiv

theorem iwaniecAuxW_continuousOn : ContinuousOn iwaniecAuxW (Set.Ici (2 : Real)) := by
  apply (iwaniecAuxFunction_continuousOn 1).mono
  intro s hs
  have h : 2 ≤ s := hs
  change (1 : Real) < s
  linarith

theorem iwaniecAuxM_continuousOn : ContinuousOn iwaniecAuxM (Set.Ici (2 : Real)) := by
  apply (iwaniecAuxFunction_continuousOn (-1)).mono
  intro s hs
  have h : 2 ≤ s := hs
  change (1 : Real) < s
  linarith

theorem iwaniecAuxW_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxW (s / (s - 1) ^ 2 * iwaniecAuxW (s - 1)) s := by
  simpa only [iwaniecAuxW, iwaniecAuxDelayKernel, one_mul] using
    iwaniecAuxFunction_hasDerivAt 1 hs

theorem iwaniecAuxM_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxM (-s / (s - 1) ^ 2 * iwaniecAuxM (s - 1)) s := by
  have h := iwaniecAuxFunction_hasDerivAt (-1) hs
  simpa only [iwaniecAuxM, iwaniecAuxDelayKernel, neg_one_mul, neg_div] using h

end

end Erdos1212Kernel
