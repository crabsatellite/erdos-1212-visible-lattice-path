import Erdos1212Kernel.PrimeCorridorCriterion

namespace Erdos1212Kernel

open Filter Topology

/-!
The high prime corridor used to keep the canonical separator away from the
height-one boundary.  Its height parameter satisfies
`ceil (N / 4) <= k <= floor (N / 2)`, so the lattice height `2 * k` is at
least `N / 2` while the family still has order `N^2 / log N`.
-/

def highCorridorHeights (N : Nat) : Finset Nat :=
  Finset.Icc (max 2 ((N + 3) / 4)) (N / 2)

def highPrimeCorridorRoots (N : Nat) : Finset (Nat × Nat) :=
  corridorPrimes N ×ˢ highCorridorHeights N

theorem highCorridorHeights_subset (N : Nat) :
    highCorridorHeights N ⊆ corridorHeights N := by
  intro k hk
  rw [highCorridorHeights, Finset.mem_Icc] at hk
  rw [corridorHeights, Finset.mem_Icc]
  exact ⟨le_trans (le_max_left _ _) hk.1, hk.2⟩

theorem highPrimeCorridorRoots_subset (N : Nat) :
    highPrimeCorridorRoots N ⊆ primeCorridorRoots N := by
  intro r hr
  rcases Finset.mem_product.mp hr with ⟨hp, hk⟩
  exact Finset.mem_product.mpr ⟨hp, highCorridorHeights_subset N hk⟩

theorem highPrimeCorridorPoint_safe {N : Nat} {r : Nat × Nat}
    (hr : r ∈ highPrimeCorridorRoots N) :
    SafePoint (primeCorridorPoint r) :=
  primeCorridorPoint_safe (highPrimeCorridorRoots_subset N hr)

theorem highCorridorHeights_card_eventually :
    ∀ᶠ N : Nat in atTop,
      (highCorridorHeights N).card =
        N / 2 + 1 - (N + 3) / 4 := by
  filter_upwards [eventually_ge_atTop 8] with N hN
  have hceil : 2 ≤ (N + 3) / 4 := by omega
  simp [highCorridorHeights, max_eq_right hceil]

theorem highCorridorHeights_eventually_lower :
    ∀ᶠ N : Nat in atTop,
      (N : Real) / 5 ≤ ((highCorridorHeights N).card : Real) := by
  filter_upwards [highCorridorHeights_card_eventually,
      eventually_ge_atTop 20] with N hcard hN
  have hnat : N / 5 + 1 ≤ (highCorridorHeights N).card := by
    rw [hcard]
    omega
  have hmod : N % 5 < 5 := Nat.mod_lt N (by omega)
  have hdecomp : N % 5 + 5 * (N / 5) = N := Nat.mod_add_div N 5
  have hmodReal : ((N % 5 : Nat) : Real) < 5 := by exact_mod_cast hmod
  have hdecompReal :
      ((N % 5 : Nat) : Real) + 5 * ((N / 5 : Nat) : Real) = (N : Real) := by
    exact_mod_cast hdecomp
  have hfloor : (N : Real) / 5 ≤ (N / 5 : Nat) + 1 := by
    nlinarith
  exact hfloor.trans (by exact_mod_cast hnat)

theorem highPrimeCorridorRoots_eventually_lower :
    ∀ᶠ N : Nat in atTop,
      (N : Real) ^ 2 / (60 * Real.log (N : Real)) ≤
        ((highPrimeCorridorRoots N).card : Real) := by
  filter_upwards [corridorPrimes_eventually_lower,
      highCorridorHeights_eventually_lower, eventually_ge_atTop 2000]
      with N hprime hheight hN
  have hNpos : 0 < (N : Real) := by positivity
  have hlogNpos : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [show (highPrimeCorridorRoots N).card =
      (corridorPrimes N).card * (highCorridorHeights N).card by
        simp [highPrimeCorridorRoots]]
  push_cast
  calc
    (N : Real) ^ 2 / (60 * Real.log (N : Real))
        ≤ ((N : Real) / (10 * Real.log (N : Real))) * ((N : Real) / 5) := by
          field_simp [ne_of_gt hlogNpos]
          nlinarith [sq_nonneg (N : Real)]
    _ ≤ ((corridorPrimes N).card : Real) *
          ((highCorridorHeights N).card : Real) := by
        exact mul_le_mul hprime hheight (by positivity) (by positivity)

def highPrimeCorridorBaselineScale (N : Nat) : NNReal :=
  (highPrimeCorridorRoots N).card

theorem highPrimeCorridorBaselineScale_eventually_pos :
    ∀ᶠ N : Nat in atTop, 0 < highPrimeCorridorBaselineScale N := by
  filter_upwards [highPrimeCorridorRoots_eventually_lower,
      eventually_ge_atTop 2000] with N hlower hN
  have hlogNpos : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlowerPos :
      0 < (N : Real) ^ 2 / (60 * Real.log (N : Real)) := by positivity
  have hcardReal : 0 < ((highPrimeCorridorRoots N).card : Real) :=
    hlowerPos.trans_le hlower
  simpa [highPrimeCorridorBaselineScale] using hcardReal

theorem primePair_over_highCorridor_tendsto_zero_real :
    Tendsto
      (fun N : Nat =>
        (Nat.primeCounting (4 * N) : Real) ^ 2 /
          ((highPrimeCorridorRoots N).card : Real))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajorant :
      Tendsto (fun N : Nat => (8640 : Real) / Real.log (N : Real))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds 0) from
        tendsto_const_nhds)
      hmajorant
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · filter_upwards [highPrimeCorridorRoots_eventually_lower,
        primeCounting_four_eventually_upper, eventually_ge_atTop 2000]
      with N hbase hpi hN
    have hNpos : 0 < (N : Real) := by positivity
    have hlogNpos : 0 < Real.log (N : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hbaseLowerPos :
        0 < (N : Real) ^ 2 / (60 * Real.log (N : Real)) := by positivity
    have hbasePos : 0 < ((highPrimeCorridorRoots N).card : Real) :=
      hbaseLowerPos.trans_le hbase
    have hpiNonneg : 0 ≤ (Nat.primeCounting (4 * N) : Real) := by positivity
    have hpiMajorantNonneg :
        0 ≤ 12 * (N : Real) / Real.log (N : Real) := by positivity
    have hpiSq :
        (Nat.primeCounting (4 * N) : Real) ^ 2 ≤
          (12 * (N : Real) / Real.log (N : Real)) ^ 2 := by
      nlinarith
    calc
      (Nat.primeCounting (4 * N) : Real) ^ 2 /
            ((highPrimeCorridorRoots N).card : Real)
          ≤ (12 * (N : Real) / Real.log (N : Real)) ^ 2 /
              ((highPrimeCorridorRoots N).card : Real) := by gcongr
      _ ≤ (12 * (N : Real) / Real.log (N : Real)) ^ 2 /
              ((N : Real) ^ 2 / (60 * Real.log (N : Real))) := by gcongr
      _ = (8640 : Real) / Real.log (N : Real) := by
            field_simp [ne_of_gt hNpos, ne_of_gt hlogNpos]
            ring

theorem primePair_over_highCorridor_tendsto_zero :
    Tendsto
      (fun N : Nat =>
        primeCorridorTwoPrimeScale N / highPrimeCorridorBaselineScale N)
      atTop (nhds 0) := by
  apply NNReal.tendsto_coe.mp
  simpa [primeCorridorTwoPrimeScale, highPrimeCorridorBaselineScale]
    using primePair_over_highCorridor_tendsto_zero_real

def highCorridorGeometricBoundaryMass
    (prefactor decay : NNReal) (N : Nat) : NNReal :=
  (N : NNReal) ^ 2 * prefactor * decay ^ N

theorem geometricBoundary_over_highCorridor_tendsto_zero
    (prefactor decay : NNReal) (hdecay : decay < 1) :
    Tendsto
      (fun N : Nat =>
        highCorridorGeometricBoundaryMass prefactor decay N /
          highPrimeCorridorBaselineScale N)
      atTop (nhds 0) := by
  apply NNReal.tendsto_coe.mp
  have hdecayReal : ‖(decay : Real)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg decay.coe_nonneg] using hdecay
  have hsum :
      Summable (fun N : Nat => (N : Real) * (decay : Real) ^ N) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := Real) 1 hdecayReal)
  have hmajorant :
      Tendsto
        (fun N : Nat =>
          (60 * (prefactor : Real)) *
            ((N : Real) * (decay : Real) ^ N))
        atTop (nhds 0) := by
    simpa using hsum.tendsto_atTop_zero.const_mul (60 * (prefactor : Real))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds 0) from
        tendsto_const_nhds)
      hmajorant
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · filter_upwards [highPrimeCorridorRoots_eventually_lower,
        eventually_ge_atTop 2000] with N hbase hN
    have hNpos : 0 < (N : Real) := by positivity
    have hlogNpos : 0 < Real.log (N : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hbaseLowerPos :
        0 < (N : Real) ^ 2 / (60 * Real.log (N : Real)) := by positivity
    have hbasePos : 0 < ((highPrimeCorridorRoots N).card : Real) :=
      hbaseLowerPos.trans_le hbase
    have hlogLeN : Real.log (N : Real) ≤ (N : Real) := by
      have hlog := Real.log_le_sub_one_of_pos hNpos
      linarith
    change
      (N : Real) ^ 2 * (prefactor : Real) * (decay : Real) ^ N /
          ((highPrimeCorridorRoots N).card : Real) ≤
        (60 * (prefactor : Real)) *
          ((N : Real) * (decay : Real) ^ N)
    calc
      (N : Real) ^ 2 * (prefactor : Real) * (decay : Real) ^ N /
            ((highPrimeCorridorRoots N).card : Real)
          ≤ (N : Real) ^ 2 * (prefactor : Real) * (decay : Real) ^ N /
              ((N : Real) ^ 2 / (60 * Real.log (N : Real))) := by
                gcongr
      _ = 60 * (prefactor : Real) *
            (Real.log (N : Real) * (decay : Real) ^ N) := by
          field_simp [ne_of_gt hNpos, ne_of_gt hlogNpos]
      _ ≤ (60 * (prefactor : Real)) *
            ((N : Real) * (decay : Real) ^ N) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogLeN (by positivity)) (by positivity)

noncomputable def boundedHighPrimeCorridorRoots (N : Nat) :
    Finset (Nat × Nat) := by
  letI := Classical.propDecidable
  exact (highPrimeCorridorRoots N).filter fun r =>
    ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint r)

noncomputable def boundedHighPrimeCorridorRootMass (N : Nat) : NNReal :=
  (boundedHighPrimeCorridorRoots N).card

theorem boundedHighPrimeCorridorRoots_eq_of_all_bounded
    (hbounded : AllSafeComponentsBounded) (N : Nat) :
    boundedHighPrimeCorridorRoots N = highPrimeCorridorRoots N := by
  letI := Classical.propDecidable
  unfold boundedHighPrimeCorridorRoots
  apply Finset.filter_eq_self.mpr
  intro r _hr
  exact hbounded (primeCorridorPoint r)

noncomputable def highPrimeCorridorEscapeCriterion :
    RelativeContourEscapeCriterion where
  baselineMass := highPrimeCorridorBaselineScale
  escapeMass := boundedHighPrimeCorridorRootMass
  baselinePositive := highPrimeCorridorBaselineScale_eventually_pos
  boundedComponentsForceEscape := by
    intro hbounded N
    rw [boundedHighPrimeCorridorRootMass, highPrimeCorridorBaselineScale,
      boundedHighPrimeCorridorRoots_eq_of_all_bounded hbounded N]

@[simp] theorem highPrimeCorridorEscapeCriterion_baselineMass (N : Nat) :
    highPrimeCorridorEscapeCriterion.baselineMass N =
      highPrimeCorridorBaselineScale N := rfl

@[simp] theorem highPrimeCorridorEscapeCriterion_escapeMass (N : Nat) :
    highPrimeCorridorEscapeCriterion.escapeMass N =
      boundedHighPrimeCorridorRootMass N := rfl

end Erdos1212Kernel
