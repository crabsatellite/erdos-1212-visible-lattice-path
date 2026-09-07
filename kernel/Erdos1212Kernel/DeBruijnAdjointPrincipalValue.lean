import Erdos1212Kernel.DeBruijnAdjointCancellation
import Erdos1212Kernel.DeBruijnAdjointCutoffTails

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijn1951PositiveTail (u : Real) : Real := ∫ z in Set.Ioi (1 : Real), deBruijn1951AdjointDensity u z

def deBruijn1951NegativeTail (u : Real) : Real := ∫ z in Set.Ioi (1 : Real), deBruijn1951BoundaryKernel (u + 1) z

/-- The explicit regularization used to prove existence of the source
principal value. It is not identified with G1 until that limit is proved. -/
def deBruijn1951RegularizedAdjoint (u : Real) : Real :=
  deBruijn1951NearIntegral u + deBruijn1951PositiveTail u - deBruijn1951NegativeTail u

theorem deBruijn1951PVCutoff_decomposition {u δ : Real} (hu : -1 < u) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    deBruijn1951PVCutoff u δ = (∫ z in δ..1, deBruijn1951SymmetricDensity u z) +
      deBruijn1951PositiveTail u - deBruijn1951NegativeTail u := by
  have hpδ := deBruijn1951AdjointDensity_integrable_positive u hδ
  have hp1 := deBruijn1951AdjointDensity_integrable_positive u (show (0 : Real) < 1 by norm_num)
  have hnδ := deBruijn1951BoundaryKernel_integrable_cut (show 0 < u + 1 by linarith) hδ
  have hn1 := deBruijn1951BoundaryKernel_integrable (show 0 < u + 1 by linarith)
  have hsp := intervalIntegral.integral_interval_add_Ioi hpδ hp1
  have hsn := intervalIntegral.integral_interval_add_Ioi hnδ hn1
  have hpInt : IntervalIntegrable (deBruijn1951AdjointDensity u) volume δ 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδOne).mpr (hpδ.mono_set Set.Ioc_subset_Ioi_self)
  have hnInt : IntervalIntegrable (deBruijn1951BoundaryKernel (u + 1)) volume δ 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδOne).mpr (hnδ.mono_set Set.Ioc_subset_Ioi_self)
  have hr : (∫ z in δ..1, deBruijn1951SymmetricDensity u z) =
      (∫ z in δ..1, deBruijn1951AdjointDensity u z) - ∫ z in δ..1, deBruijn1951BoundaryKernel (u + 1) z := by
    calc
      _ = ∫ z in δ..1, deBruijn1951AdjointDensity u z - deBruijn1951BoundaryKernel (u + 1) z := by
        apply intervalIntegral.integral_congr
        intro z _hz
        exact deBruijn1951SymmetricDensity_eq u z
      _ = _ := intervalIntegral.integral_sub hpInt hnInt
  rw [deBruijn1951PVCutoff_eq_density]
  unfold deBruijn1951PositiveTail deBruijn1951NegativeTail
  rw [deBruijn1951AdjointDensity_negative_integral, ← hsp, ← hsn, hr]
  ring

theorem tendsto_deBruijn1951SymmetricTruncation (u : Real) :
    Tendsto (fun δ : Real => ∫ z in δ..1, deBruijn1951SymmetricDensity u z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951NearIntegral u)) := by
  have hp := intervalIntegral.continuousOn_primitive_interval'
    (deBruijn1951SymmetricDensity_intervalIntegrable u) (a := (1 : Real)) (by norm_num)
  have hc : ContinuousOn (fun δ : Real => ∫ z in δ..1, deBruijn1951SymmetricDensity u z)
      (Set.Icc (0 : Real) 1) := by
    have hn := hp.neg
    rw [Set.uIcc_of_le (show (0 : Real) ≤ 1 by norm_num)] at hn
    apply hn.congr
    intro δ _hδ
    exact intervalIntegral.integral_symm 1 δ
  have hw : ContinuousWithinAt (fun δ : Real => ∫ z in δ..1, deBruijn1951SymmetricDensity u z)
      (Set.Ioc (0 : Real) 1) 0 :=
    (hc 0 (by norm_num)).mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  have hsets : Set.Ioc (0 : Real) 1 =ᶠ[nhds 0] Set.Ioi 0 := by
    filter_upwards [Iic_mem_nhds (show (0 : Real) < 1 by norm_num)] with x hx
    apply propext
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, hx⟩
  exact (hw.congr_set hsets).tendsto

/-- De Bruijn 1951 (2.9), with the literal symmetric exclusion of zero.
Both improper cutoff integrals are separately integrable on this domain. -/
theorem deBruijn1951_principalValue_regularized {u : Real} (hu : -1 < u) :
    Tendsto (deBruijn1951PVCutoff u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951RegularizedAdjoint u)) := by
  have h := ((tendsto_deBruijn1951SymmetricTruncation u).add_const (deBruijn1951PositiveTail u)).sub_const
    (deBruijn1951NegativeTail u)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Iic_mem_nhds (show (0 : Real) < 1 by norm_num))] with δ hδ hδOne
  exact (deBruijn1951PVCutoff_decomposition hu hδ hδOne).symm

/-- The source's literal principal value. The next theorem supplies its
existence and exact value on `u>-1`. -/
def deBruijn1951G1 (u : Real) : Real := limUnder (nhdsWithin 0 (Set.Ioi 0)) (deBruijn1951PVCutoff u)

theorem deBruijn1951G1_eq_regularized {u : Real} (hu : -1 < u) :
    deBruijn1951G1 u = deBruijn1951RegularizedAdjoint u := by
  have h := deBruijn1951_principalValue_regularized hu
  have hl : Tendsto (deBruijn1951PVCutoff u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951G1 u)) :=
    tendsto_nhds_limUnder ⟨_, h⟩
  exact tendsto_nhds_unique hl h

theorem deBruijn1951_principalValue {u : Real} (hu : -1 < u) :
    Tendsto (deBruijn1951PVCutoff u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951G1 u)) := by
  rw [deBruijn1951G1_eq_regularized hu]
  exact deBruijn1951_principalValue_regularized hu

end

end Erdos1212Kernel
