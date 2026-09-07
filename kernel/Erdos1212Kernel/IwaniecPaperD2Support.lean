import Erdos1212Kernel.IwaniecPaperD2Exact

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Every nonzero pair lies strictly beyond the fourth-root threshold. -/
theorem iwaniecPaperD2_support_quartic {level : Real} {p q : Nat}
    (hp : p.Prime) (hq : q ∈ iwaniecStrictPrimePool (p : Real))
    (hfail : level / p ≤ (q : Real) ^ 3) : level < (p : Real) ^ 4 := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqp := (mem_iwaniecStrictPrimePool.mp hq).2
  have hcube : (q : Real) ^ 3 < (p : Real) ^ 3 :=
    pow_lt_pow_left₀ hqp (Nat.cast_nonneg _) (by norm_num)
  calc
    level ≤ (q : Real) ^ 3 * p := (div_le_iff₀ hp0).mp hfail
    _ < (p : Real) ^ 3 * p := mul_lt_mul_of_pos_right hcube hp0
    _ = (p : Real) ^ 4 := by ring

/-- Remove only terms proved to vanish, retaining the strict prime pool
and every inner second-prime condition. -/
theorem iwaniecPaperD2At_eq_quartic_band (level z : Real) :
    iwaniecPaperD2At level z =
      ∑ p ∈ (iwaniecStrictPrimePool z).filter (fun p : Nat => level < (p : Real) ^ 4),
        ∑ q ∈ iwaniecStrictPrimePool (p : Real),
          if level / p ≤ (q : Real) ^ 3 then
            iwaniecPaperR (q : Real) / ((p : Real) * q) else 0 := by
  classical
  unfold iwaniecPaperD2At
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hb : level < (p : Real) ^ 4
  · rw [if_pos hb]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro q hq
    have hn : ¬ level / p ≤ (q : Real) ^ 3 := fun hf =>
      hb (iwaniecPaperD2_support_quartic (mem_iwaniecStrictPrimePool.mp hp).1 hq hf)
    rw [if_neg hn]

theorem iwaniecPaperCutoff_prime_quartic_lt {level s : Real}
    (hy : 1 < level) (hs : 4 ≤ s) {p : Nat}
    (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    (p : Real) ^ 4 < level := by
  have hpd := mem_iwaniecStrictPrimePool.mp hp
  have hpow : (p : Real) ^ 4 < Real.exp (Real.log level / s) ^ 4 :=
    pow_lt_pow_left₀ hpd.2 (Nat.cast_nonneg _) (by norm_num)
  apply hpow.trans_le
  calc
    _ = Real.exp (4 * (Real.log level / s)) := (Real.exp_nat_mul _ 4).symm
    _ ≤ Real.exp (Real.log level) := by
      apply Real.exp_le_exp.mpr
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < s)]
      nlinarith [Real.log_pos hy]
    _ = level := Real.exp_log (zero_lt_one.trans hy)

theorem iwaniecPaperD2_eq_zero_of_four_le {level s : Real}
    (hy : 1 < level) (hs : 4 ≤ s) : iwaniecPaperD2 level s = 0 := by
  classical
  unfold iwaniecPaperD2
  rw [iwaniecPaperD2At_eq_quartic_band]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp, hband⟩ := Finset.mem_filter.mp hp
  exact ((not_lt_of_ge (iwaniecPaperCutoff_prime_quartic_lt hy hs hp).le) hband).elim

/-- On the actual d₂ support with s≥2, the last prime is at least y^(1/6)
in logarithmic coordinates. This is the source's exponential-error scale. -/
theorem iwaniecPaperD2_support_log_sixth {level s : Real} {p q : Nat}
    (hy : 1 < level) (hs : 2 ≤ s)
    (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)))
    (hq : q ∈ iwaniecStrictPrimePool (p : Real))
    (hfail : level / p ≤ (q : Real) ^ 3) : Real.log level / 6 ≤ Real.log (q : Real) := by
  have hpPrime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hy0 : 0 < level := zero_lt_one.trans hy
  have hlogp : Real.log (p : Real) < Real.log level / s := by
    have hh := Real.log_lt_log hp0 (mem_iwaniecStrictPrimePool.mp hp).2
    simpa only [Real.log_exp] using hh
  have hhalf : Real.log (p : Real) ≤ Real.log level / 2 :=
    hlogp.le.trans (div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num) hs)
  have hlog := Real.log_le_log (div_pos hy0 hp0) hfail
  rw [Real.log_div hy0.ne' hp0.ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- The proven Euler-product remainder at the literal last prime has
the uniform decay needed in Lemma 16. No new analytic premise is supplied. -/
theorem exists_iwaniecPaperD2_lastPrime_unit_error :
    ∃ C : Real, 0 < C ∧ ∀ (level s : Real) (p q : Nat),
      1 < level → 2 ≤ s →
      p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)) →
      q ∈ iwaniecStrictPrimePool (p : Real) → level / p ≤ (q : Real) ^ 3 →
      |iwaniecPaperR (q : Real) - Real.exp (-Real.eulerMascheroniConstant) / Real.log (q : Real)| ≤
        C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨C, hC, hR⟩ := exists_iwaniecPaperR_unit_error
  refine ⟨C, hC, ?_⟩
  intro level s p q hy hs hp hq hf
  have hq2 : (2 : Real) ≤ q := by exact_mod_cast (mem_iwaniecStrictPrimePool.mp hq).1.two_le
  apply (hR q hq2).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Real.sqrt_le_sqrt (iwaniecPaperD2_support_log_sixth hy hs hp hq hf))

end

end Erdos1212Kernel
