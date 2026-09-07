import Erdos1212Kernel.IwaniecSieveFunctions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def iwaniecPsi (s : Real) : Real :=
  s⁻¹ * Real.exp (s - 3) *
    (1 + 3 * Real.log (3 / (s - 1)))

def iwaniecPhi (s : Real) : Real :=
  3 * s / (s - 1) ^ 2 -
    (1 + 3 * Real.log (3 / (s - 1)))

theorem log_three_halves_lt_five_twelfths :
    Real.log ((3 : Real) / 2) < 5 / 12 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hbound := Real.exp_bound
    (x := (5 : Real) / 12) (by norm_num : |(5 : Real) / 12| ≤ 1)
    (n := 4) (by norm_num)
  have hlower := (abs_sub_le_iff.mp hbound).2
  norm_num [Finset.sum_range_succ] at hlower ⊢
  linarith

theorem iwaniecPhi_three_pos : 0 < iwaniecPhi 3 := by
  unfold iwaniecPhi
  rw [show (3 : Real) / (3 - 1) = 3 / 2 by norm_num]
  have hlog := log_three_halves_lt_five_twelfths
  norm_num
  linarith

theorem hasDerivAt_iwaniecPhi
    {s : Real} (hs : s ≠ 1) :
    HasDerivAt iwaniecPhi (3 * s * (s - 3) / (s - 1) ^ 3) s := by
  have hsub : HasDerivAt (fun x : Real => x - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hden : HasDerivAt (fun x : Real => (x - 1) ^ 2)
      (2 * (s - 1)) s := by
    convert hsub.pow 2 using 1 <;> ring
  have hnum : HasDerivAt (fun x : Real => 3 * x) 3 s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul 3
  have hfrac := hnum.div hden (pow_ne_zero 2 (sub_ne_zero.mpr hs))
  have hinner : HasDerivAt (fun x : Real => 3 / (x - 1))
      (-3 / (s - 1) ^ 2) s := by
    convert (hasDerivAt_const s (3 : Real)).div hsub
      (sub_ne_zero.mpr hs) using 1 <;> field_simp <;> ring
  have hinnerNe : (3 : Real) / (s - 1) ≠ 0 :=
    div_ne_zero (by norm_num) (sub_ne_zero.mpr hs)
  have hlog : HasDerivAt (fun x : Real => Real.log (3 / (x - 1)))
      (((3 : Real) / (s - 1))⁻¹ * (-3 / (s - 1) ^ 2)) s :=
    by
      simpa [div_eq_mul_inv, mul_comm] using hinner.log hinnerNe
  have hbracket : HasDerivAt
      (fun x : Real => 1 + 3 * Real.log (3 / (x - 1)))
      (3 * (((3 : Real) / (s - 1))⁻¹ * (-3 / (s - 1) ^ 2))) s := by
    convert (hasDerivAt_const s (1 : Real)).add
      (hlog.const_mul 3) using 1 <;> ring
  unfold iwaniecPhi
  convert hfrac.sub hbracket using 1 <;> field_simp <;> ring

theorem iwaniecPhi_continuousOn_Icc
    {a b : Real} (ha : 1 < a) :
    ContinuousOn iwaniecPhi (Set.Icc a b) := by
  intro s hs
  exact (hasDerivAt_iwaniecPhi (by linarith [hs.1])).continuousAt.continuousWithinAt

theorem iwaniecPhi_antitoneOn_two_three :
    AntitoneOn iwaniecPhi (Set.Icc (2 : Real) 3) := by
  let slope := fun s : Real => 3 * s * (s - 3) / (s - 1) ^ 3
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (2 : Real) 3)
    (iwaniecPhi_continuousOn_Icc (by norm_num))
  · intro s hs
    have hs' : s ∈ Set.Icc (2 : Real) 3 := interior_subset hs
    exact (hasDerivAt_iwaniecPhi (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (2 : Real) 3 := interior_subset hs
    change 3 * s * (s - 3) / (s - 1) ^ 3 ≤ 0
    have hsPos : 0 ≤ s := by linarith [hs'.1]
    have hsubPos : 0 < s - 1 := by linarith [hs'.1]
    have hden : 0 < (s - 1) ^ 3 := pow_pos hsubPos _
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hsPos)
        (by linarith [hs'.2]))
      (le_of_lt hden)

theorem iwaniecPhi_monotoneOn_three_four :
    MonotoneOn iwaniecPhi (Set.Icc (3 : Real) 4) := by
  let slope := fun s : Real => 3 * s * (s - 3) / (s - 1) ^ 3
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (3 : Real) 4)
    (iwaniecPhi_continuousOn_Icc (by norm_num))
  · intro s hs
    have hs' : s ∈ Set.Icc (3 : Real) 4 := interior_subset hs
    exact (hasDerivAt_iwaniecPhi (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (3 : Real) 4 := interior_subset hs
    change 0 ≤ 3 * s * (s - 3) / (s - 1) ^ 3
    have hsPos : 0 ≤ s := by linarith [hs'.1]
    have hdiff : 0 ≤ s - 3 := by linarith [hs'.1]
    have hden : 0 ≤ (s - 1) ^ 3 := pow_nonneg (by linarith [hs'.1]) _
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsPos) hdiff) hden

theorem iwaniecPhi_three_le
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecPhi 3 ≤ iwaniecPhi s := by
  by_cases hs : s ≤ 3
  · exact iwaniecPhi_antitoneOn_two_three
      ⟨hlower, hs⟩ ⟨by norm_num, by norm_num⟩ hs
  · exact iwaniecPhi_monotoneOn_three_four
      ⟨by norm_num, by norm_num⟩ ⟨le_of_not_ge hs, hupper⟩ (le_of_not_ge hs)

theorem iwaniecPhi_pos
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    0 < iwaniecPhi s :=
  iwaniecPhi_three_pos.trans_le (iwaniecPhi_three_le hlower hupper)

theorem hasDerivAt_iwaniecPsi
    {s : Real} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    HasDerivAt iwaniecPsi
      (-Real.exp (s - 3) * (s - 1) / s ^ 2 * iwaniecPhi s) s := by
  have hsub : HasDerivAt (fun x : Real => x - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hinner : HasDerivAt (fun x : Real => 3 / (x - 1))
      (-3 / (s - 1) ^ 2) s := by
    convert (hasDerivAt_const s (3 : Real)).div hsub
      (sub_ne_zero.mpr hs1) using 1 <;> field_simp <;> ring
  have hinnerNe : (3 : Real) / (s - 1) ≠ 0 :=
    div_ne_zero (by norm_num) (sub_ne_zero.mpr hs1)
  have hlog : HasDerivAt (fun x : Real => Real.log (3 / (x - 1)))
      (((3 : Real) / (s - 1))⁻¹ * (-3 / (s - 1) ^ 2)) s := by
    simpa [div_eq_mul_inv, mul_comm] using hinner.log hinnerNe
  have hbracket : HasDerivAt
      (fun x : Real => 1 + 3 * Real.log (3 / (x - 1)))
      (3 * (((3 : Real) / (s - 1))⁻¹ * (-3 / (s - 1) ^ 2))) s := by
    convert (hasDerivAt_const s (1 : Real)).add
      (hlog.const_mul 3) using 1 <;> ring
  have hinv : HasDerivAt (fun x : Real => x⁻¹) (-(s⁻¹ ^ 2)) s := by
    simpa [id_eq, div_eq_mul_inv] using (hasDerivAt_id s).inv hs0
  have hexp : HasDerivAt (fun x : Real => Real.exp (x - 3))
      (Real.exp (s - 3)) s := by
    simpa using ((hasDerivAt_id s).sub_const 3).exp
  unfold iwaniecPsi iwaniecPhi
  convert (hinv.mul hexp).mul hbracket using 1 <;>
    simp only [Pi.mul_apply, id_eq] <;> field_simp <;> ring

theorem iwaniecPsi_continuousOn_two_four :
    ContinuousOn iwaniecPsi (Set.Icc (2 : Real) 4) := by
  intro s hs
  exact (hasDerivAt_iwaniecPsi (by linarith [hs.1])
    (by linarith [hs.1])).continuousAt.continuousWithinAt

theorem iwaniecPsi_strictAntiOn_two_four :
    StrictAntiOn iwaniecPsi (Set.Icc (2 : Real) 4) := by
  let slope := fun s : Real =>
    -Real.exp (s - 3) * (s - 1) / s ^ 2 * iwaniecPhi s
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (2 : Real) 4)
    iwaniecPsi_continuousOn_two_four
  · intro s hs
    have hs' : s ∈ Set.Icc (2 : Real) 4 := interior_subset hs
    exact (hasDerivAt_iwaniecPsi (by linarith [hs'.1])
      (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (2 : Real) 4 := interior_subset hs
    change -Real.exp (s - 3) * (s - 1) / s ^ 2 * iwaniecPhi s < 0
    have hphi := iwaniecPhi_pos hs'.1 hs'.2
    have hsub : 0 < s - 1 := by linarith [hs'.1]
    have hsSq : 0 < s ^ 2 := sq_pos_of_pos (by linarith [hs'.1])
    have hcoeff : -Real.exp (s - 3) * (s - 1) / s ^ 2 < 0 := by
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hsub) hsSq
    exact mul_neg_of_neg_of_pos hcoeff hphi

/-- Iwaniec 1971, Lemma 3. -/
theorem iwaniecPsi_le_two
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecPsi s ≤ iwaniecPsi 2 := by
  exact iwaniecPsi_strictAntiOn_two_four.antitoneOn
    ⟨by norm_num, by norm_num⟩ ⟨hlower, hupper⟩ hlower

theorem iwaniecPsi_two :
    iwaniecPsi 2 =
      Real.exp (-1) / 2 * (1 + 3 * Real.log 3) := by
  unfold iwaniecPsi
  rw [show (2 : Real)⁻¹ = 1 / 2 by norm_num,
    show (2 : Real) - 3 = -1 by norm_num,
    show (3 : Real) / (2 - 1) = 3 by norm_num]
  ring

def iwaniecContractionA : Real :=
  Real.exp 1 / 3 * iwaniecPsi 2

theorem iwaniecContractionA_eq :
    iwaniecContractionA = (1 + 3 * Real.log 3) / 6 := by
  rw [iwaniecContractionA, iwaniecPsi_two, Real.exp_neg]
  have hexp : Real.exp (1 : Real) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

theorem log_three_lt_eleven_tenths :
    Real.log 3 < (11 : Real) / 10 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hbound := Real.exp_bound
    (x := (11 : Real) / 20) (by norm_num : |(11 : Real) / 20| ≤ 1)
    (n := 6) (by norm_num)
  have hlower := (abs_sub_le_iff.mp hbound).2
  norm_num [Finset.sum_range_succ] at hlower
  have hhalf : (1733 : Real) / 1000 < Real.exp ((11 : Real) / 20) := by
    linarith
  have hhalfPos := Real.exp_pos ((11 : Real) / 20)
  calc
    (3 : Real) < ((1733 : Real) / 1000) ^ 2 := by norm_num
    _ < (Real.exp ((11 : Real) / 20)) ^ 2 := by nlinarith
    _ = Real.exp ((11 : Real) / 10) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      norm_num

/-- The numerical contraction in Iwaniec 1971, Lemma 4. -/
theorem iwaniecContractionA_lt_eighteen_twentyfive :
    iwaniecContractionA < (18 : Real) / 25 := by
  rw [iwaniecContractionA_eq]
  have hlog := log_three_lt_eleven_tenths
  linarith

theorem iwaniecContractionA_nonneg : 0 ≤ iwaniecContractionA := by
  rw [iwaniecContractionA_eq]
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

theorem iwaniecContractionA_lt_one : iwaniecContractionA < 1 :=
  iwaniecContractionA_lt_eighteen_twentyfive.trans (by norm_num)

theorem exp_one_lt_eleven_fourths :
    Real.exp 1 < (11 : Real) / 4 := by
  have hupper := Real.exp_bound'
    (x := (1 : Real)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at hupper ⊢
  linarith

theorem one_lt_log_three : (1 : Real) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact exp_one_lt_eleven_fourths.trans (by norm_num)

theorem two_thirds_lt_iwaniecContractionA :
    (2 : Real) / 3 < iwaniecContractionA := by
  rw [iwaniecContractionA_eq]
  have hlog := one_lt_log_three
  linarith

theorem exp_one_sq_div_twelve_lt_iwaniecContractionA :
    Real.exp 1 ^ 2 / 12 < iwaniecContractionA := by
  have hePos := Real.exp_pos (1 : Real)
  have heUpper := exp_one_lt_eleven_fourths
  have hsquare : Real.exp 1 ^ 2 < 8 := by nlinarith
  have hratio : Real.exp 1 ^ 2 / 12 < (2 : Real) / 3 := by linarith
  exact hratio.trans two_thirds_lt_iwaniecContractionA

end

end Erdos1212Kernel
