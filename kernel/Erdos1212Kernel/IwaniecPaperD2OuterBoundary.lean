import Erdos1212Kernel.IwaniecPaperD2SummedError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

def iwaniecPaperD2ClosedOuterBand (level s : Real) : Finset Nat :=
  iwaniecClosedPrimeBand (Real.exp (Real.log level / 4)) (Real.exp (Real.log level / s))

def iwaniecPaperD2ClosedOuterMain (level s : Real) : Real :=
  ∑ p ∈ iwaniecPaperD2ClosedOuterBand level s,
    (p : Real)⁻¹ * (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)

def iwaniecPaperD2OuterBoundary (level s : Real) : Real :=
  ∑ p ∈ iwaniecPaperD2ClosedOuterBand level s \ iwaniecPaperD2OuterBand level s,
    (p : Real)⁻¹ * (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)

theorem iwaniecPaperD2_outer_subset_closed {level : Real} (hy : 1 < level) (s : Real) :
    iwaniecPaperD2OuterBand level s ⊆ iwaniecPaperD2ClosedOuterBand level s := by
  intro p hp
  obtain ⟨hp, hquartic⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpPrime, hpUpper⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hl := Real.log_lt_log (zero_lt_one.trans hy) hquartic
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.log level / 4 ≤ Real.log (p : Real) := by linarith
  have hlower := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp0] at hlower
  exact (mem_iwaniecClosedPrimeBand (Real.exp_pos _).le p).mpr ⟨hpPrime, hlower, hpUpper.le⟩

theorem iwaniecPaperD2_closed_weight_nonneg {level s : Real} (hy : 1 < level) (hs : 2 ≤ s)
    {p : Nat} (hp : p ∈ iwaniecPaperD2ClosedOuterBand level s) :
    0 ≤ (p : Real)⁻¹ * (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹) := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := (mem_iwaniecClosedPrimeBand (Real.exp_pos _).le p).mp hp
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hp1 : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
  have hlp := Real.log_pos hp1
  have hL := Real.log_pos hy
  have hlo := Real.log_le_log (Real.exp_pos _) hpLower
  have hhi := Real.log_le_log hp0 hpUpper
  rw [Real.log_exp] at hlo hhi
  have hhalf : Real.log (p : Real) ≤ Real.log level / 2 :=
    hhi.trans (div_le_div_of_nonneg_left hL.le (by norm_num) hs)
  have hlogid : Real.log (level / p) = Real.log level - Real.log (p : Real) :=
    Real.log_div (zero_lt_one.trans hy).ne' hp0.ne'
  have hchild : 0 < Real.log (level / p) := by rw [hlogid]; linarith
  have hbracket : (Real.log (p : Real))⁻¹ ≤ 3 / Real.log (level / p) := by
    have hh : 1 / Real.log (p : Real) ≤ 3 / Real.log (level / p) := by
      apply (div_le_div_iff₀ hlp hchild).mpr
      rw [hlogid]
      linarith
    simpa only [one_div] using hh
  exact mul_nonneg (inv_nonneg.mpr hp0.le) (sub_nonneg.mpr hbracket)

/-- Exact finite endpoint transport. The omitted endpoint terms are
retained as a boundary sum before any inequality is taken. -/
theorem iwaniecPaperD2_outer_boundary_identity {level : Real} (hy : 1 < level) (s : Real) :
    iwaniecPaperD2OuterMain level s =
      iwaniecPaperD2ClosedOuterMain level s - iwaniecPaperD2OuterBoundary level s := by
  have hh := Finset.sum_sdiff
    (f := fun p : Nat => (p : Real)⁻¹ * (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹))
    (iwaniecPaperD2_outer_subset_closed hy s)
  change iwaniecPaperD2OuterBoundary level s + iwaniecPaperD2OuterMain level s =
    iwaniecPaperD2ClosedOuterMain level s at hh
  linarith

theorem iwaniecPaperD2_outer_main_le_closed {level s : Real} (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperD2OuterMain level s ≤ iwaniecPaperD2ClosedOuterMain level s := by
  have hboundary : 0 ≤ iwaniecPaperD2OuterBoundary level s := by
    apply Finset.sum_nonneg
    intro p hp
    exact iwaniecPaperD2_closed_weight_nonneg hy hs (Finset.mem_sdiff.mp hp).1
  rw [iwaniecPaperD2_outer_boundary_identity hy s]
  linarith

end

end Erdos1212Kernel
