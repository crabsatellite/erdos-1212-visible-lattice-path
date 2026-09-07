import Erdos1212Kernel.IwaniecPaperD2InnerSum

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Domain conditions for the inner prime sum are derived from the
original outer prime pool, not added to the final source-bound consumer. -/
theorem iwaniecPaperD2_child_domain {level s : Real} {p : Nat}
    (hy64 : 64 ≤ level) (hs : 2 ≤ s)
    (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    8 ≤ level / p ∧ Real.log level / 6 ≤ Real.log (level / p) / 3 := by
  have hy : 1 < level := by linarith
  have hy0 : 0 < level := zero_lt_one.trans hy
  have hpPrime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hlogp : Real.log (p : Real) < Real.log level / s := by
    have hh := Real.log_lt_log hp0 (mem_iwaniecStrictPrimePool.mp hp).2
    simpa only [Real.log_exp] using hh
  have hhalf : Real.log (p : Real) ≤ Real.log level / 2 :=
    hlogp.le.trans (div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num) hs)
  have hpRoot : (p : Real) ≤ Real.sqrt level := by
    have hh := Real.exp_le_exp.mpr hhalf
    rwa [Real.exp_log hp0, Real.exp_half, Real.exp_log hy0] at hh
  have hroot0 := Real.sqrt_nonneg level
  have hrootSq := Real.sq_sqrt hy0.le
  have hroot8 : 8 ≤ Real.sqrt level := by nlinarith
  constructor
  · apply (le_div_iff₀ hp0).mpr
    have h₁ := mul_le_mul_of_nonneg_right hroot8 hp0.le
    have h₂ := mul_le_mul_of_nonneg_left hpRoot hroot0
    nlinarith only [h₁, h₂, hrootSq]
  · rw [Real.log_div hy0.ne' hp0.ne']
    linarith

/-- The actual logarithmic inner sum, on the already proved quartic
outer band, has exactly the error scale displayed in Lemma 16. -/
theorem exists_iwaniecPaperD2LogInner_source_rate :
    ∃ C : Real, 0 < C ∧ ∀ (level s : Real) (p : Nat),
      64 ≤ level → 2 ≤ s →
      p ∈ (iwaniecStrictPrimePool (Real.exp (Real.log level / s))).filter
        (fun p : Nat => level < (p : Real) ^ 4) →
      |iwaniecPaperD2LogInner level p -
        (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨C, hC, hinner⟩ := exists_iwaniecPaperD2LogInner_unit_error
  refine ⟨C, hC, ?_⟩
  intro level s p hy hs hp
  obtain ⟨hp, hquartic⟩ := Finset.mem_filter.mp hp
  have hdata := iwaniecPaperD2_child_domain hy hs hp
  have hh := hinner level p (mem_iwaniecStrictPrimePool.mp hp).1 hdata.1 hquartic.le
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Real.sqrt_le_sqrt hdata.2)

end

end Erdos1212Kernel
