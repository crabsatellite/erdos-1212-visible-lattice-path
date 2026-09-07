import Erdos1212Kernel.AlgebraicCorridorBonferroniErrorScale
import Erdos1212Kernel.AlgebraicCorridorBlockSelection

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

theorem mem_corridorMediumWitnessCandidates
    {N : ℝ} {lower T n : ℕ} :
    n ∈ corridorMediumWitnessCandidates
        (smallPrimePool N) (mediumPrimePool N) lower T ↔
      lower ≤ n ∧ n < lower + T ∧
        corridorAvoidsPrimeState (smallPrimePool N) n ∧
        ∃ q ∈ mediumPrimePool N, q ∣ n := by
  classical
  unfold corridorMediumWitnessCandidates
  rw [corridorInterval_eq_Ico]
  simp only [Finset.mem_filter, Finset.mem_Ico]
  aesop

theorem mediumWitness_corridorRough
    {N : ℝ} {n : ℕ}
    (havoid : corridorAvoidsPrimeState (smallPrimePool N) n) :
    CorridorRough (z N) n := by
  intro p hp hpn
  by_contra hnot
  have hpz : (p : ℝ) ≤ z N := le_of_not_gt hnot
  exact havoid p (mem_smallPrimePool.mpr ⟨hp, hpz⟩) hpn

theorem mediumWitness_composite
    {N : ℝ} {lower n q : ℕ}
    (hlower : (2 * z N : ℝ) < lower) (hnLower : lower ≤ n)
    (hq : q ∈ mediumPrimePool N) (hqn : q ∣ n) : Composite n := by
  have hqLtR : (q : ℝ) < n :=
    (mem_mediumPrimePool.mp hq).2.2.trans_lt
      (hlower.trans_le (by exact_mod_cast hnLower))
  have hqLt : q < n := by exact_mod_cast hqLtR
  obtain ⟨b, hnb⟩ := hqn
  refine ⟨q, b, (prime_of_mem_mediumPrimePool hq).one_lt, ?_, hnb⟩
  by_contra hb
  have hbLe : b ≤ 1 := Nat.le_of_not_gt hb
  interval_cases b <;> simp_all

theorem mediumWitnessCandidates_subset_roughComposite
    {N : ℝ} {lower T : ℕ} (hlower : (2 * z N : ℝ) < lower) :
    corridorMediumWitnessCandidates
        (smallPrimePool N) (mediumPrimePool N) lower T ⊆
      corridorRoughCompositeCandidates (z N) lower T := by
  intro n hn
  obtain ⟨hnLower, hnUpper, havoid, q, hq, hqn⟩ :=
    mem_corridorMediumWitnessCandidates.mp hn
  apply mem_corridorRoughCompositeCandidates.mpr
  exact ⟨hnLower, hnUpper,
    mediumWitness_composite hlower hnLower hq hqn,
    mediumWitness_corridorRough havoid⟩

theorem eventually_corridorRoughCompositeCandidates_card_lower :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      (2 * z N : ℝ) < lower → N ^ (9 / 10 : ℝ) ≤ 2 * (T : ℝ) →
      (T : ℝ) *
          (corridorRoughDensityConstant /
            (2 * Real.log (z N) ^ 2)) ≤
        ((corridorRoughCompositeCandidates (z N) lower T).card : ℝ) := by
  filter_upwards [eventually_corridorMediumCandidates_card_half_main_lower]
      with N hcount
  intro lower T hlower hfar hT
  have hlowerCount := hcount lower T hlower hT
  have hsubset := mediumWitnessCandidates_subset_roughComposite
    (N := N) (T := T) hfar
  exact hlowerCount.trans (by exact_mod_cast Finset.card_le_card hsubset)

theorem eventually_corridorRoughCompositeCandidates_paper_lower :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      (2 * z N : ℝ) < lower → N ^ (9 / 10 : ℝ) ≤ (T : ℝ) →
      (T : ℝ) / (100 * Real.log (z N) ^ 2) ≤
        ((corridorRoughCompositeCandidates (z N) lower T).card : ℝ) := by
  filter_upwards [eventually_corridorRoughCompositeCandidates_card_lower]
      with N hcount
  intro lower T hlower hfar hT
  have hTtwo : N ^ (9 / 10 : ℝ) ≤ 2 * (T : ℝ) := by
    have hTNonneg : 0 ≤ (T : ℝ) := by positivity
    linarith
  convert hcount lower T hlower hfar hTtwo using 1 <;>
    simp [corridorRoughDensityConstant] <;> ring

/-- Lemmas 3.1 and 3.2 composed at the paper's actual scale: every sufficiently
large full-block interval of length at least `N^(9/10)` contains one band of
`rows N` distinct composite `z N`-rough ordinates. -/
theorem eventually_exists_corridor_rough_composite_block_rows_at_scale :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      (2 * z N : ℝ) < lower → 0 < T / band N →
      N ^ (9 / 10 : ℝ) ≤
        2 * (((T / band N) * band N : ℕ) : ℝ) →
      ∃ blockLower : ℕ, ∃ row : Fin (rows N) → ℕ,
        Function.Injective row ∧
        (lower ≤ blockLower ∧ blockLower + band N ≤ lower + T) ∧
        (∀ i, blockLower ≤ row i ∧ row i < blockLower + band N) ∧
        (∀ i, Composite (row i)) ∧
        (∀ i, CorridorRough (z N) (row i)) := by
  filter_upwards [eventually_large_domain,
    eventually_corridorRoughCompositeCandidates_card_lower,
    eventually_rows_le_band_mul_rough_density] with
      N hdom hcount hrowDensity
  intro lower T hlower hfar hblocks hfull
  have hBReal : 0 < (band N : ℝ) := by
    have hceil : 10000 * ell N ^ 2 ≤ (band N : ℝ) := Nat.le_ceil _
    have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
    have : 0 < 10000 * ell N ^ 2 := by positivity
    linarith
  have hB : 0 < band N := by exact_mod_cast hBReal
  have hcandidate := hcount lower ((T / band N) * band N)
    hlower hfar hfull
  have hblocksNonneg : 0 ≤ ((T / band N : ℕ) : ℝ) := by positivity
  have hscaledRows := mul_le_mul_of_nonneg_left hrowDensity hblocksNonneg
  have hreal : (((T / band N) * rows N : ℕ) : ℝ) ≤
      ((corridorRoughCompositeCandidates (z N) lower
        ((T / band N) * band N)).card : ℝ) := by
    push_cast
    exact hscaledRows.trans (by
      simpa [mul_assoc] using hcandidate)
  have hnat : (T / band N) * rows N ≤
      (corridorRoughCompositeCandidates (z N) lower
        ((T / band N) * band N)).card := by
    exact_mod_cast hreal
  exact exists_corridor_rough_composite_block_rows
    hB hblocks hnat

/-- Literal Lemma 3.2 for an arbitrary interval of paper length.  The final
incomplete `band N` block is removed inside the proof. -/
theorem eventually_exists_corridor_band_rows_in_interval :
    ∀ᶠ N : ℝ in atTop, ∀ (lower T : ℕ), 0 < lower →
      (2 * z N : ℝ) < lower → N ^ (9 / 10 : ℝ) ≤ (T : ℝ) →
      ∃ blockLower : ℕ, ∃ row : Fin (rows N) → ℕ,
        Function.Injective row ∧
        (lower ≤ blockLower ∧ blockLower + band N ≤ lower + T) ∧
        (∀ i, blockLower ≤ row i ∧ row i < blockLower + band N) ∧
        (∀ i, Composite (row i)) ∧
        (∀ i, CorridorRough (z N) (row i)) := by
  filter_upwards [eventually_large_domain,
    eventually_two_band_le_N_nine_tenths,
    eventually_exists_corridor_rough_composite_block_rows_at_scale] with
      N hdom hbandSmall hblocksTheorem
  intro lower T hlower hfar hT
  have hBReal : 0 < (band N : ℝ) := by
    have hceil : 10000 * ell N ^ 2 ≤ (band N : ℝ) := Nat.le_ceil _
    have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
    have : 0 < 10000 * ell N ^ 2 := by positivity
    linarith
  have hB : 0 < band N := by exact_mod_cast hBReal
  have htwoBReal : ((2 * band N : ℕ) : ℝ) ≤ (T : ℝ) :=
    hbandSmall.trans hT
  have htwoB : 2 * band N ≤ T := by exact_mod_cast htwoBReal
  have hblocks : 0 < T / band N :=
    Nat.div_pos (by omega) hB
  have hrem := Nat.mod_lt T hB
  have hdecomp := Nat.mod_add_div T (band N)
  rw [Nat.mul_comm (band N) (T / band N)] at hdecomp
  have hfullNat : T ≤ 2 * ((T / band N) * band N) := by omega
  have hfullReal : (T : ℝ) ≤
      2 * (((T / band N) * band N : ℕ) : ℝ) := by
    exact_mod_cast hfullNat
  exact hblocksTheorem lower T hlower hfar hblocks (hT.trans hfullReal)

end

end Erdos1212Kernel.CorridorScale
