import Erdos1212Kernel.IwaniecPrimePowerBandMass

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

def iwaniecPaperD2OuterBand (level s : Real) : Finset Nat :=
  (iwaniecStrictPrimePool (Real.exp (Real.log level / s))).filter
    (fun p : Nat => level < (p : Real) ^ 4)

def iwaniecPaperD2InnerPool (level : Real) (p : Nat) : Finset Nat :=
  (iwaniecStrictPrimePool (p : Real)).filter (fun q : Nat => level / p ≤ (q : Real) ^ 3)

def iwaniecPaperD2ControlBand (level : Real) : Finset Nat :=
  iwaniecClosedPrimeBand (Real.exp (Real.log level / 6)) (Real.exp (Real.log level / 2))

theorem iwaniecPaperD2_prime_upper {level s : Real} (hy : 1 < level) (hs : 2 ≤ s)
    {p : Nat} (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    (p : Real) ≤ Real.exp (Real.log level / 2) := by
  apply (mem_iwaniecStrictPrimePool.mp hp).2.le.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num) hs

theorem iwaniecPaperD2_outer_subset_control {level s : Real} (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperD2OuterBand level s ⊆ iwaniecPaperD2ControlBand level := by
  intro p hp
  obtain ⟨hp, hquartic⟩ := Finset.mem_filter.mp hp
  have hpPrime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hl := Real.log_lt_log (zero_lt_one.trans hy) hquartic
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hL := Real.log_pos hy
  have hlog : Real.log level / 6 ≤ Real.log (p : Real) := by linarith
  have hlower : Real.exp (Real.log level / 6) ≤ (p : Real) := by
    have hh := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hp0] at hh
  exact (mem_iwaniecClosedPrimeBand (Real.exp_pos _).le p).mpr
    ⟨hpPrime, hlower, iwaniecPaperD2_prime_upper hy hs hp⟩

theorem iwaniecPaperD2_inner_subset_control {level s : Real} (hy : 1 < level) (hs : 2 ≤ s)
    {p : Nat} (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    iwaniecPaperD2InnerPool level p ⊆ iwaniecPaperD2ControlBand level := by
  intro q hq
  obtain ⟨hq, hfail⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqPrime, hqp⟩ := mem_iwaniecStrictPrimePool.mp hq
  have hq0 : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hl := iwaniecPaperD2_support_log_sixth hy hs hp hq hfail
  have hlower : Real.exp (Real.log level / 6) ≤ (q : Real) := by
    have hh := Real.exp_le_exp.mpr hl
    rwa [Real.exp_log hq0] at hh
  exact (mem_iwaniecClosedPrimeBand (Real.exp_pos _).le q).mpr
    ⟨hqPrime, hlower, hqp.le.trans (iwaniecPaperD2_prime_upper hy hs hp)⟩

/-- Exact filtered-pool form of the canonical double sum. Both the
quartic outer band and the failed cubic inner condition are retained. -/
theorem iwaniecPaperD2_eq_mass_carrier (level s : Real) :
    iwaniecPaperD2 level s = ∑ p ∈ iwaniecPaperD2OuterBand level s,
      ∑ q ∈ iwaniecPaperD2InnerPool level p, iwaniecPaperR (q : Real) / ((p : Real) * q) := by
  classical
  unfold iwaniecPaperD2
  rw [iwaniecPaperD2At_eq_quartic_band]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [iwaniecPaperD2InnerPool, Finset.sum_filter]

theorem iwaniecPaperD2LogInner_eq_pool (level : Real) (p : Nat) :
    iwaniecPaperD2LogInner level p =
      ∑ q ∈ iwaniecPaperD2InnerPool level p, 1 / ((q : Real) * Real.log (q : Real)) := by
  classical
  simp only [iwaniecPaperD2LogInner, iwaniecPaperD2InnerPool, Finset.sum_filter]

end

end Erdos1212Kernel
