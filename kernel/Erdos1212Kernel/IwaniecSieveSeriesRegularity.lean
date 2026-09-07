import Erdos1212Kernel.IwaniecBuchstabAdjointFamily

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1800000

theorem iwaniecGEven_continuousOn_Ici (n : Nat) :
    ContinuousOn (iwaniecGEven n) (Set.Ici (2 : Real)) := by
  let upper : Real := 4 + 2 * n
  let glued := fun s : Real => if s ≤ upper then iwaniecGEven n s else 0
  have hglued : ContinuousOn glued (Set.Ici (2 : Real)) := by
    dsimp [glued]
    apply ContinuousOn.if (p := fun s : Real => s ≤ upper)
    · intro s hs
      have hset : {t : Real | t ≤ upper} = Set.Iic upper := by ext; simp
      have hsFront : s ∈ frontier (Set.Iic upper) := by
        simpa [hset] using hs.2
      have hsEq : s = upper := by
        simpa using frontier_Iic_subset upper hsFront
      subst s
      exact iwaniecGEven_eq_zero_of_boundary n (le_refl upper)
    · apply (iwaniecGEven_GOdd_continuousOn n).1.mono
      intro s hs
      have hset : {t : Real | t ≤ upper} = Set.Iic upper := by ext; simp
      have hsUpper : s ≤ upper := by
        have hclosure := hs.2
        rw [hset, closure_Iic] at hclosure
        exact hclosure
      exact ⟨hs.1, by simpa [upper] using hsUpper⟩
    · exact continuousOn_const
  apply hglued.congr
  intro s hs
  dsimp [glued]
  by_cases hupper : s ≤ upper
  · simp [hupper]
  · rw [if_neg hupper, iwaniecGEven_eq_zero_of_boundary n (le_of_not_ge hupper)]

theorem iwaniecGOdd_continuousOn_Ici (n : Nat) :
    ContinuousOn (iwaniecGOdd n) (Set.Ici (1 : Real)) := by
  let upper : Real := 5 + 2 * n
  let glued := fun s : Real => if s ≤ upper then iwaniecGOdd n s else 0
  have hglued : ContinuousOn glued (Set.Ici (1 : Real)) := by
    dsimp [glued]
    apply ContinuousOn.if (p := fun s : Real => s ≤ upper)
    · intro s hs
      have hset : {t : Real | t ≤ upper} = Set.Iic upper := by ext; simp
      have hsFront : s ∈ frontier (Set.Iic upper) := by
        simpa [hset] using hs.2
      have hsEq : s = upper := by
        simpa using frontier_Iic_subset upper hsFront
      subst s
      exact iwaniecGOdd_eq_zero_of_boundary n (le_refl upper)
    · apply (iwaniecGEven_GOdd_continuousOn n).2.mono
      intro s hs
      have hset : {t : Real | t ≤ upper} = Set.Iic upper := by ext; simp
      have hsUpper : s ≤ upper := by
        have hclosure := hs.2
        rw [hset, closure_Iic] at hclosure
        exact hclosure
      exact ⟨hs.1, by simpa [upper] using hsUpper⟩
    · exact continuousOn_const
  apply hglued.congr
  intro s hs
  dsimp [glued]
  by_cases hupper : s ≤ upper
  · simp [hupper]
  · rw [if_neg hupper, iwaniecGOdd_eq_zero_of_boundary n (le_of_not_ge hupper)]

theorem summable_iwaniecEvenUniformBound :
    Summable (fun n : Nat =>
      iwaniecBaseA * Real.exp (-1) * iwaniecContractionA ^ n) := by
  have hgeom := summable_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  simpa [mul_assoc] using hgeom.mul_left (iwaniecBaseA * Real.exp (-1))

theorem summable_iwaniecOddUniformBound :
    Summable (fun n : Nat =>
      (Real.exp 1 / 3 * iwaniecBaseA * Real.exp (-1)) *
        iwaniecContractionA ^ n) := by
  have hgeom := summable_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  exact hgeom.mul_left _

theorem iwaniecGEven_norm_le_uniform
    (n : Nat) {s : Real} (hs : 2 ≤ s) :
    ‖iwaniecGEven n s‖ ≤
      iwaniecBaseA * Real.exp (-1) * iwaniecContractionA ^ n := by
  rw [Real.norm_of_nonneg (iwaniecGEven_nonneg n hs)]
  have hshape := Real.mul_exp_neg_le_exp_neg_one s
  have hbound := iwaniecGEven_geometricBound n hs
  have hscale : 0 ≤ iwaniecBaseA * iwaniecContractionA ^ n :=
    mul_nonneg iwaniecBaseA_nonneg
      (pow_nonneg iwaniecContractionA_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hshape hscale
  nlinarith

theorem iwaniecGOdd_norm_le_uniform
    (n : Nat) {s : Real} (hs : 1 ≤ s) :
    ‖iwaniecGOdd n s‖ ≤
      (Real.exp 1 / 3 * iwaniecBaseA * Real.exp (-1)) *
        iwaniecContractionA ^ n := by
  rw [Real.norm_of_nonneg (iwaniecGOdd_nonneg n hs)]
  have hshape := Real.mul_exp_neg_le_exp_neg_one s
  have hbound := iwaniecGOdd_geometricBound n hs
  have hscale : 0 ≤ Real.exp 1 / 3 * iwaniecBaseA *
      iwaniecContractionA ^ n := by
    exact mul_nonneg (mul_nonneg (by positivity) iwaniecBaseA_nonneg)
      (pow_nonneg iwaniecContractionA_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hshape hscale
  nlinarith

theorem iwaniecEvenSieveSeries_continuousOn :
    ContinuousOn iwaniecEvenSieveSeries (Set.Ici (2 : Real)) := by
  unfold iwaniecEvenSieveSeries
  apply continuousOn_tsum
  · exact iwaniecGEven_continuousOn_Ici
  · exact summable_iwaniecEvenUniformBound
  · intro n s hs
    exact iwaniecGEven_norm_le_uniform n hs

theorem iwaniecOddSieveSeries_continuousOn :
    ContinuousOn iwaniecOddSieveSeries (Set.Ici (1 : Real)) := by
  unfold iwaniecOddSieveSeries
  apply continuousOn_tsum
  · exact iwaniecGOdd_continuousOn_Ici
  · exact summable_iwaniecOddUniformBound
  · intro n s hs
    exact iwaniecGOdd_norm_le_uniform n hs

theorem tendsto_iwaniecEvenSieveSeries_atTop_zero :
    Tendsto iwaniecEvenSieveSeries atTop (nhds 0) := by
  let C := iwaniecBaseA * (1 - iwaniecContractionA)⁻¹
  have hmajor : Tendsto (fun s : Real => C * (s * Real.exp (-s)))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _s : Real => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa [pow_one] using
      hconst.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  apply squeeze_zero' (g := fun s : Real => C * (s * Real.exp (-s)))
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact iwaniecEvenSieveSeries_nonneg hs
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    have h := iwaniecEvenSieveSeries_le_geometric hs
    convert h using 1 <;> dsimp [C] <;> ring
  · exact hmajor

theorem tendsto_iwaniecOddSieveSeries_atTop_zero :
    Tendsto iwaniecOddSieveSeries atTop (nhds 0) := by
  let C := Real.exp 1 / 3 * iwaniecBaseA *
    (1 - iwaniecContractionA)⁻¹
  have hmajor : Tendsto (fun s : Real => C * (s * Real.exp (-s)))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _s : Real => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa [pow_one] using
      hconst.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  apply squeeze_zero' (g := fun s : Real => C * (s * Real.exp (-s)))
  · filter_upwards [eventually_ge_atTop (1 : Real)] with s hs
    exact iwaniecOddSieveSeries_nonneg hs
  · filter_upwards [eventually_ge_atTop (1 : Real)] with s hs
    have h := iwaniecOddSieveSeries_le_geometric hs
    convert h using 1 <;> dsimp [C] <;> ring
  · exact hmajor

end

end Erdos1212Kernel
