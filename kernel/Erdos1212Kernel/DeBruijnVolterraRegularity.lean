import Erdos1212Kernel.DeBruijnVolterraRatio
import Mathlib.MeasureTheory.Measure.OpenPos

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- Upgrade the source's almost-everywhere window bounds only after
proving the continuous representative has the same bounds at endpoints. -/
theorem deBruijn_continuous_bounds_of_ae_Icc {f : Real → Real} {a b m M : Real}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), m ≤ f x ∧ f x ≤ M) :
    ∀ x ∈ Set.Icc a b, m ≤ f x ∧ f x ≤ M := by
  have hclosure : Set.Icc a b ⊆ closure (interior (Set.Icc a b)) := by
    rw [interior_Icc, closure_Ioo hab.ne]
  have hmin : (fun x : Real => min (f x) M) =ᵐ[volume.restrict (Set.Icc a b)] f := by
    filter_upwards [hbound] with x hx
    exact min_eq_left hx.2
  have hmax : (fun x : Real => max (f x) m) =ᵐ[volume.restrict (Set.Icc a b)] f := by
    filter_upwards [hbound] with x hx
    exact max_eq_left hx.1
  have hminEq := Measure.eqOn_of_ae_eq hmin (hf.inf continuousOn_const) hf hclosure
  have hmaxEq := Measure.eqOn_of_ae_eq hmax (hf.sup continuousOn_const) hf hclosure
  intro x hx
  constructor
  · calc
      m ≤ max (f x) m := le_max_right _ _
      _ = f x := hmaxEq hx
  · calc
      f x = min (f x) M := (hminEq hx).symm
      _ ≤ M := min_le_right _ _

/-- The first-contact proof in the source's Theorem 1, for its actual
rho kernel. No future-window bound is an input to this theorem. -/
theorem deBruijnRhoVolterra_upper_propagation {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {a M : Real} (ha : 1 ≤ a) (hinit : ∀ x ∈ Set.Icc (a - 1) a, f x ≤ M) :
    ∀ b : Real, a ≤ b → f b ≤ M := by
  intro b hab
  by_contra hnot
  have hbBad : M < f b := lt_of_not_ge hnot
  let bad : Set Real := Set.Icc a b ∩ f ⁻¹' Set.Ici (f b)
  have hc : ContinuousOn f (Set.Icc a b) := hf.mono (fun x hx => by change 0 ≤ x; linarith [hx.1])
  have hclosed : IsClosed bad := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  obtain ⟨c, hcLeast⟩ := hcompact.exists_isLeast
    (show bad.Nonempty from ⟨b, ⟨⟨hab, le_rfl⟩, (show f b ≤ f b from le_rfl)⟩⟩)
  have hca : a ≤ c := hcLeast.1.1.1
  have hcb : c ≤ b := hcLeast.1.1.2
  have hcBad : f b ≤ f c := hcLeast.1.2
  have hcOne : 1 ≤ c := ha.trans hca
  have hbefore : ∀ y : Real, a - 1 ≤ y → y < c → f y < f b := by
    intro y hy hyc
    by_cases hya : y ≤ a
    · exact (hinit y ⟨hy, hya⟩).trans_lt hbBad
    · by_contra hny
      have hyBad : y ∈ bad := ⟨⟨(lt_of_not_ge hya).le, hyc.le.trans hcb⟩, le_of_not_gt hny⟩
      have hcy := hcLeast.2 hyBad
      linarith
  have hgapCont : ContinuousOn (fun t : Real => deBruijnRhoVolterraKernel c t * (f b - f (c - t)))
      (Set.Icc (0 : Real) 1) :=
    (deBruijnRhoVolterraKernel_continuousOn hcOne).mul
      (continuousOn_const.sub (deBruijnRhoVolterra_lag_continuousOn hf hcOne))
  have hgapInt : IntervalIntegrable (fun t : Real => deBruijnRhoVolterraKernel c t * (f b - f (c - t))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using hgapCont
  have hpos : 0 < ∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel c t * (f b - f (c - t)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hgapInt _ (by norm_num)
    intro t ht
    exact mul_pos (deBruijnRhoVolterraKernel_pos hcOne ⟨ht.1.le, ht.2.le⟩)
      (sub_pos.mpr (hbefore (c - t) (by linarith [ht.2]) (by linarith [ht.1])))
  rw [deBruijnRhoVolterra_gap_integral hf heq hcOne (f b)] at hpos
  linarith

theorem deBruijnRhoVolterra_lower_propagation {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {a m : Real} (ha : 1 ≤ a) (hinit : ∀ x ∈ Set.Icc (a - 1) a, m ≤ f x) :
    ∀ b : Real, a ≤ b → m ≤ f b := by
  have h := deBruijnRhoVolterra_upper_propagation (f := fun x : Real => -f x) hf.neg heq.neg ha
    (M := -m) (fun x hx => neg_le_neg (hinit x hx))
  intro b hb
  exact neg_le_neg_iff.mp (h b hb)

def DeBruijnVolterraRegular (f : Real → Real) : Prop :=
  ∀ a : Real, 1 ≤ a → ∀ m M : Real,
    (∀ᵐ x ∂(volume.restrict (Set.Icc (a - 1) a)), m ≤ f x ∧ f x ≤ M) →
    ∀ x : Real, a < x → m ≤ f x ∧ f x ≤ M

theorem deBruijnRhoVolterra_continuous_regular {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    DeBruijnVolterraRegular f := by
  intro a ha m M hbound x hx
  have hc : ContinuousOn f (Set.Icc (a - 1) a) := hf.mono (fun y hy => by change 0 ≤ y; linarith [hy.1])
  have hb := deBruijn_continuous_bounds_of_ae_Icc (by linarith : a - 1 < a) hc hbound
  exact ⟨deBruijnRhoVolterra_lower_propagation hf heq ha (fun y hy => (hb y hy).1) x hx.le,
    deBruijnRhoVolterra_upper_propagation hf heq ha (fun y hy => (hb y hy).2) x hx.le⟩

theorem deBruijnRhoSolutionRatio_regular {F : Real → Real}
    (hc : ContinuousOn F (Set.Ici (0 : Real)))
    (heq : ∀ x : Real, 1 ≤ x → x * F x = ∫ t in (0 : Real)..1, F (x - t)) :
    DeBruijnVolterraRegular (deBruijnRhoSolutionRatio F) :=
  deBruijnRhoVolterra_continuous_regular (deBruijnRhoSolutionRatio_continuousOn hc)
    (deBruijnRhoSolutionRatio_equation heq)

end

end Erdos1212Kernel
