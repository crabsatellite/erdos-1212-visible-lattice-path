import Erdos1212Kernel.IwaniecPaperD2ReciprocalMass

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- The logarithmic double sum after replacing R(q) by exp(-gamma)/log(q),
with exactly the original outer band and inner failed cubic condition. -/
def iwaniecPaperD2LogSum (level s : Real) : Real :=
  ∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹ * iwaniecPaperD2LogInner level p

/-- The literal remaining outer sum in the proof of Lemma 16. -/
def iwaniecPaperD2OuterMain (level s : Real) : Real :=
  ∑ p ∈ iwaniecPaperD2OuterBand level s,
    (p : Real)⁻¹ * (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)

theorem iwaniecPaperD2LogSum_eq_double_sum (level s : Real) :
    iwaniecPaperD2LogSum level s = ∑ p ∈ iwaniecPaperD2OuterBand level s,
      ∑ q ∈ iwaniecPaperD2InnerPool level p, 1 / ((p : Real) * q * Real.log (q : Real)) := by
  unfold iwaniecPaperD2LogSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [iwaniecPaperD2LogInner_eq_pool, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- Exact normalization of the total R-replacement error; no weight
or omitted prime suffix is lost before the triangle inequality. -/
theorem iwaniecPaperD2_log_remainder_identity (level s c : Real) :
    iwaniecPaperD2 level s - c * iwaniecPaperD2LogSum level s =
      ∑ p ∈ iwaniecPaperD2OuterBand level s,
        ∑ q ∈ iwaniecPaperD2InnerPool level p,
          (iwaniecPaperR (q : Real) - c / Real.log (q : Real)) / ((p : Real) * q) := by
  rw [iwaniecPaperD2_eq_mass_carrier, iwaniecPaperD2LogSum_eq_double_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem iwaniecPaperD2_outer_remainder_identity (level s : Real) :
    iwaniecPaperD2LogSum level s - iwaniecPaperD2OuterMain level s =
      ∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹ *
        (iwaniecPaperD2LogInner level p -
          (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)) := by
  unfold iwaniecPaperD2LogSum iwaniecPaperD2OuterMain
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end

end Erdos1212Kernel
