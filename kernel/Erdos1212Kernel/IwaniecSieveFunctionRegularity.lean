import Erdos1212Kernel.IwaniecSieveFunctionBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem iwaniecGTwo_continuousOn :
    ContinuousOn iwaniecGTwo (Set.Icc (2 : Real) 4) := by
  let formula := fun s : Real => 3 * Real.log (3 / (s - 1)) + s - 4
  have hformula : ContinuousOn formula (Set.Icc (2 : Real) 4) := by
    intro s hs
    have hden : s - 1 ≠ 0 := by linarith [hs.1]
    have hsub : HasDerivAt (fun x : Real => x - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have hinner : HasDerivAt (fun x : Real => 3 / (x - 1))
        (-3 / (s - 1) ^ 2) s := by
      convert (hasDerivAt_const s (3 : Real)).div hsub hden using 1 <;>
        field_simp <;> ring
    have hinnerNe : (3 : Real) / (s - 1) ≠ 0 :=
      div_ne_zero (by norm_num) hden
    have hlog := hinner.log hinnerNe
    have hderiv := ((hlog.const_mul 3).add (hasDerivAt_id s)).sub_const 4
    exact hderiv.continuousAt.continuousWithinAt
  apply hformula.congr
  intro s hs
  exact iwaniecGTwo_eq hs.1 hs.2

theorem iwaniecGEven_zero_continuousOn :
    ContinuousOn (iwaniecGEven 0) (Set.Icc (2 : Real) 4) := by
  apply iwaniecGTwo_continuousOn.congr
  intro s _hs
  exact iwaniecGEven_zero s

theorem iwaniecGOdd_continuousOn_of_even
    (n : Nat)
    (heven : ContinuousOn (iwaniecGEven n)
      (Set.Icc (2 : Real) (4 + 2 * n))) :
    ContinuousOn (iwaniecGOdd n)
      (Set.Icc (1 : Real) (5 + 2 * n)) := by
  let upper : Real := 5 + 2 * n
  let integrand := fun t : Real => iwaniecGEven n (t - 1) / (t - 1)
  let primitive := fun s : Real => ∫ t in s..upper, integrand t
  have hshift : ContinuousOn (fun t : Real => iwaniecGEven n (t - 1))
      (Set.Icc (3 : Real) upper) := by
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc (3 : Real) upper) := by fun_prop
    apply heven.comp hsub
    intro t ht
    change t - 1 ∈ Set.Icc (2 : Real) (4 + 2 * n)
    constructor
    · linarith [ht.1]
    · dsimp [upper] at ht ⊢
      linarith [ht.2]
  have hintegrand : ContinuousOn integrand (Set.Icc (3 : Real) upper) := by
    dsimp [integrand]
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc (3 : Real) upper) := by fun_prop
    apply hshift.div hsub
    intro t ht
    change t - 1 ≠ 0
    linarith [ht.1]
  have hint : IntegrableOn integrand (Set.Icc (3 : Real) upper) :=
    hintegrand.integrableOn_Icc
  have hprimitive : ContinuousOn primitive (Set.Icc (3 : Real) upper) := by
    dsimp [primitive]
    have hn : (0 : Real) ≤ n := by positivity
    have hle : (3 : Real) ≤ upper := by
      dsimp [upper]
      linarith
    have hp := continuousOn_primitive_interval_left
      (a := (3 : Real)) (b := upper)
      (by simpa [Set.uIcc_of_le hle] using hint)
    simpa [Set.uIcc_of_le hle] using hp
  let simple := fun s : Real => if s ≤ 3 then primitive 3 else primitive s
  have hsimple : ContinuousOn simple (Set.Icc (1 : Real) upper) := by
    dsimp [simple]
    apply ContinuousOn.if (p := fun s : Real => s ≤ 3)
    · intro s hs
      have hsFrontier : s ∈ frontier (Set.Iic (3 : Real)) := by
        have hset : {s : Real | s ≤ 3} = Set.Iic 3 := by ext; simp
        simpa [hset] using hs.2
      have hsEq : s = 3 := by
        simpa using frontier_Iic_subset (3 : Real) hsFrontier
      subst s
      rfl
    · exact continuousOn_const
    · apply hprimitive.mono
      intro s hs
      have hsDomain := hs.1
      have hsLower : 3 ≤ s := by
        have hsClosure : s ∈ closure {s : Real | ¬s ≤ 3} := hs.2
        have hset : {s : Real | ¬s ≤ 3} = Set.Ioi 3 := by ext; simp
        rw [hset, closure_Ioi] at hsClosure
        exact hsClosure
      exact ⟨hsLower, hsDomain.2⟩
  apply hsimple.congr
  intro s hs
  dsimp [simple, primitive, upper, integrand]
  by_cases hthree : s ≤ 3
  · rw [if_pos hthree, iwaniecGOdd_of_le_three n hthree]
    exact iwaniecGOdd_of_three_le n (le_refl 3) (by
      dsimp [upper] at hs ⊢
      linarith [hs.2])
  · rw [if_neg hthree]
    exact iwaniecGOdd_of_three_le n (le_of_not_ge hthree) hs.2

theorem iwaniecGEven_succ_continuousOn_of_odd
    (n : Nat)
    (hodd : ContinuousOn (iwaniecGOdd n)
      (Set.Icc (1 : Real) (5 + 2 * n))) :
    ContinuousOn (iwaniecGEven (n + 1))
      (Set.Icc (2 : Real) (6 + 2 * n)) := by
  let upper : Real := 6 + 2 * n
  let integrand := fun t : Real => iwaniecGOdd n (t - 1) / (t - 1)
  let primitive := fun s : Real => ∫ t in s..upper, integrand t
  have hshift : ContinuousOn (fun t : Real => iwaniecGOdd n (t - 1))
      (Set.Icc (2 : Real) upper) := by
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc (2 : Real) upper) := by fun_prop
    apply hodd.comp hsub
    intro t ht
    change t - 1 ∈ Set.Icc (1 : Real) (5 + 2 * n)
    constructor
    · linarith [ht.1]
    · dsimp [upper] at ht ⊢
      linarith [ht.2]
  have hintegrand : ContinuousOn integrand (Set.Icc (2 : Real) upper) := by
    dsimp [integrand]
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc (2 : Real) upper) := by fun_prop
    apply hshift.div hsub
    intro t ht
    change t - 1 ≠ 0
    linarith [ht.1]
  have hint : IntegrableOn integrand (Set.Icc (2 : Real) upper) :=
    hintegrand.integrableOn_Icc
  have hprimitive : ContinuousOn primitive (Set.Icc (2 : Real) upper) := by
    dsimp [primitive]
    have hn : (0 : Real) ≤ n := by positivity
    have hle : (2 : Real) ≤ upper := by
      dsimp [upper]
      linarith
    have hp := continuousOn_primitive_interval_left
      (a := (2 : Real)) (b := upper)
      (by simpa [Set.uIcc_of_le hle] using hint)
    simpa [Set.uIcc_of_le hle] using hp
  apply hprimitive.congr
  intro s hs
  dsimp [primitive, upper, integrand]
  exact iwaniecGEven_succ n hs.2

theorem iwaniecGEven_GOdd_continuousOn (n : Nat) :
    ContinuousOn (iwaniecGEven n)
        (Set.Icc (2 : Real) (4 + 2 * n)) ∧
      ContinuousOn (iwaniecGOdd n)
        (Set.Icc (1 : Real) (5 + 2 * n)) := by
  induction n with
  | zero =>
      have heven : ContinuousOn (iwaniecGEven 0)
          (Set.Icc (2 : Real) (4 + 2 * (0 : Nat))) := by
        simpa using iwaniecGEven_zero_continuousOn
      exact ⟨heven, iwaniecGOdd_continuousOn_of_even 0 heven⟩
  | succ n ih =>
      have heven := iwaniecGEven_succ_continuousOn_of_odd n ih.2
      have heven' : ContinuousOn (iwaniecGEven (n + 1))
          (Set.Icc (2 : Real) (4 + 2 * ((n + 1 : Nat) : Real))) := by
        rw [Nat.cast_add, Nat.cast_one]
        convert heven using 1 <;> ring
      exact ⟨heven', iwaniecGOdd_continuousOn_of_even (n + 1) heven'⟩

theorem iwaniecGEven_intervalIntegrable
    (n : Nat) : IntervalIntegrable (iwaniecGEven n) volume
      (2 : Real) (4 + 2 * n) :=
  by
    have hn : (0 : Real) ≤ n := by positivity
    have hle : (2 : Real) ≤ 4 + 2 * (n : Real) := by linarith
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hle] using (iwaniecGEven_GOdd_continuousOn n).1

theorem iwaniecGOdd_intervalIntegrable
    (n : Nat) : IntervalIntegrable (iwaniecGOdd n) volume
      (1 : Real) (5 + 2 * n) :=
  by
    have hn : (0 : Real) ≤ n := by positivity
    have hle : (1 : Real) ≤ 5 + 2 * (n : Real) := by linarith
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hle] using (iwaniecGEven_GOdd_continuousOn n).2

end

end Erdos1212Kernel
