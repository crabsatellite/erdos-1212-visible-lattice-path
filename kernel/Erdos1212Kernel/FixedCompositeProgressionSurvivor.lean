import Erdos1212Kernel.UniformCompositeSurvivor

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

def fixedProgressionBase (step residue lower : Nat) : Nat :=
  ((lower + (step - residue)) / step) * step + residue

def fixedProgressionCandidate
    (step residue lower index : Nat) : Nat :=
  fixedProgressionBase step residue lower + index * step

theorem fixedProgressionCandidate_eq
    (step residue lower index : Nat) :
    fixedProgressionCandidate step residue lower index =
      step * (((lower + (step - residue)) / step) + index) + residue := by
  unfold fixedProgressionCandidate fixedProgressionBase
  ring

theorem not_dvd_fixedProgressionCandidate
    {step residue lower index q : Nat}
    (hqStep : q ∣ step) (hqResidue : ¬ q ∣ residue) :
    ¬ q ∣ fixedProgressionCandidate step residue lower index := by
  intro hcandidate
  rw [fixedProgressionCandidate_eq] at hcandidate
  have hproduct :
      q ∣ step * (((lower + (step - residue)) / step) + index) :=
    dvd_mul_of_dvd_left hqStep _
  exact hqResidue ((Nat.dvd_add_iff_right hproduct).mpr hcandidate)

theorem fixedProgressionBase_gt
    {step residue lower : Nat}
    (hstep : 0 < step) (hresidueStep : residue < step) :
    lower < fixedProgressionBase step residue lower := by
  have hmod : (lower + (step - residue)) % step < step :=
    Nat.mod_lt _ hstep
  have hdecompose :
      (lower + (step - residue)) % step +
          step * ((lower + (step - residue)) / step) =
        lower + (step - residue) := Nat.mod_add_div _ _
  unfold fixedProgressionBase
  rw [Nat.mul_comm ((lower + (step - residue)) / step) step]
  omega

theorem fixedProgressionBase_le
    {step residue lower : Nat}
    (hresidueStep : residue ≤ step) :
    fixedProgressionBase step residue lower ≤ lower + step := by
  have hfloor :
      ((lower + (step - residue)) / step) * step ≤
        lower + (step - residue) := Nat.div_mul_le_self _ _
  unfold fixedProgressionBase
  omega

theorem fixedProgressionCandidate_gt
    {step residue lower index : Nat}
    (hstep : 0 < step) (hresidueStep : residue < step) :
    lower < fixedProgressionCandidate step residue lower index :=
  (fixedProgressionBase_gt hstep hresidueStep).trans_le
    (Nat.le_add_right _ _)

theorem fixedProgressionCandidate_le
    {step residue lower K index : Nat}
    (hresidueStep : residue ≤ step) (hindex : index ≤ K) :
    fixedProgressionCandidate step residue lower index ≤
      lower + step * (K + 1) := by
  unfold fixedProgressionCandidate
  have hbase := fixedProgressionBase_le
    (lower := lower) hresidueStep
  have hmul := Nat.mul_le_mul_right step hindex
  calc
    fixedProgressionBase step residue lower + index * step ≤
        (lower + step) + index * step := Nat.add_le_add_right hbase _
    _ ≤ (lower + step) + K * step := Nat.add_le_add_left hmul _
    _ = lower + step * (K + 1) := by ring

def fixedProgressionKilledIndices
    (step residue lower K q : Nat) : Finset Nat :=
  (Finset.range (K + 1)).filter fun index =>
    q ∣ fixedProgressionCandidate step residue lower index

theorem fixedProgressionKilledIndices_card_le_one
    {step residue lower K q : Nat}
    (hqPrime : Nat.Prime q) (hKq : K < q)
    (hqStep : ¬ q ∣ step) :
    (fixedProgressionKilledIndices step residue lower K q).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  have hleftData := Finset.mem_filter.mp hleft
  have hrightData := Finset.mem_filter.mp hright
  have hleftBound : left ≤ K := by
    have := Finset.mem_range.mp hleftData.1
    omega
  have hrightBound : right ≤ K := by
    have := Finset.mem_range.mp hrightData.1
    omega
  rcases le_total left right with hle | hle
  · have hqDifference :
        q ∣ fixedProgressionCandidate step residue lower right -
          fixedProgressionCandidate step residue lower left :=
      Nat.dvd_sub hrightData.2 hleftData.2
    have hdifferenceEq :
        fixedProgressionCandidate step residue lower right -
            fixedProgressionCandidate step residue lower left =
          (right - left) * step := by
      unfold fixedProgressionCandidate
      rw [Nat.add_sub_add_left, Nat.sub_mul]
    rw [hdifferenceEq] at hqDifference
    rcases hqPrime.dvd_mul.mp hqDifference with hqIndex | hqStep'
    · by_contra hne
      have hpositive : 0 < right - left :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle hne)
      have hqLe : q ≤ right - left := Nat.le_of_dvd hpositive hqIndex
      omega
    · exact False.elim (hqStep hqStep')
  · have hqDifference :
        q ∣ fixedProgressionCandidate step residue lower left -
          fixedProgressionCandidate step residue lower right :=
      Nat.dvd_sub hleftData.2 hrightData.2
    have hdifferenceEq :
        fixedProgressionCandidate step residue lower left -
            fixedProgressionCandidate step residue lower right =
          (left - right) * step := by
      unfold fixedProgressionCandidate
      rw [Nat.add_sub_add_left, Nat.sub_mul]
    rw [hdifferenceEq] at hqDifference
    rcases hqPrime.dvd_mul.mp hqDifference with hqIndex | hqStep'
    · by_contra hne
      have hpositive : 0 < left - right :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
      have hqLe : q ≤ left - right := Nat.le_of_dvd hpositive hqIndex
      omega
    · exact False.elim (hqStep hqStep')

def fixedProgressionKilledIndicesRange
    (step residue lower length q : Nat) : Finset Nat :=
  (Finset.range length).filter fun index =>
    q ∣ fixedProgressionCandidate step residue lower index

/-- In a progression whose step is invertible modulo `q`, each quotient block
of `q` consecutive indices contains at most one killed index. -/
theorem fixedProgressionKilledIndicesRange_card_le
    {step residue lower length q : Nat}
    (hqPrime : Nat.Prime q) (hqStep : ¬ q ∣ step) :
    (fixedProgressionKilledIndicesRange
        step residue lower length q).card ≤ length / q + 1 := by
  let killed := fixedProgressionKilledIndicesRange
    step residue lower length q
  calc
    killed.card ≤ (Finset.range (length / q + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun index => index / q)
      · intro index hindex
        have hi : index < length :=
          Finset.mem_range.mp (Finset.mem_filter.mp hindex).1
        apply Finset.mem_range.mpr
        have hdiv := Nat.div_le_div_right (c := q) (Nat.le_of_lt hi)
        exact Nat.lt_succ_of_le hdiv
      · intro first hfirst second hsecond hquotient
        change first / q = second / q at hquotient
        have hfirstData := Finset.mem_filter.mp hfirst
        have hsecondData := Finset.mem_filter.mp hsecond
        have hfirstDecompose :
            first % q + q * (first / q) = first := Nat.mod_add_div first q
        have hsecondDecompose :
            second % q + q * (second / q) = second := Nat.mod_add_div second q
        have hfirstMod : first % q < q := Nat.mod_lt _ hqPrime.pos
        have hsecondMod : second % q < q := Nat.mod_lt _ hqPrime.pos
        have hqpart : q * (first / q) = q * (second / q) := by
          rw [hquotient]
        rcases le_total first second with hle | hle
        · have hqDifference :
              q ∣ fixedProgressionCandidate step residue lower second -
                fixedProgressionCandidate step residue lower first :=
            Nat.dvd_sub hsecondData.2 hfirstData.2
          have hdifferenceEq :
              fixedProgressionCandidate step residue lower second -
                  fixedProgressionCandidate step residue lower first =
                (second - first) * step := by
            unfold fixedProgressionCandidate
            rw [Nat.add_sub_add_left, Nat.sub_mul]
          rw [hdifferenceEq] at hqDifference
          have hqIndex : q ∣ second - first := by
            rcases hqPrime.dvd_mul.mp hqDifference with hindex | hstep
            · exact hindex
            · exact False.elim (hqStep hstep)
          have hdifferenceLt : second - first < q := by
            omega
          have hzero : second - first = 0 :=
            Nat.eq_zero_of_dvd_of_lt hqIndex hdifferenceLt
          omega
        · have hqDifference :
              q ∣ fixedProgressionCandidate step residue lower first -
                fixedProgressionCandidate step residue lower second :=
            Nat.dvd_sub hfirstData.2 hsecondData.2
          have hdifferenceEq :
              fixedProgressionCandidate step residue lower first -
                  fixedProgressionCandidate step residue lower second =
                (first - second) * step := by
            unfold fixedProgressionCandidate
            rw [Nat.add_sub_add_left, Nat.sub_mul]
          rw [hdifferenceEq] at hqDifference
          have hqIndex : q ∣ first - second := by
            rcases hqPrime.dvd_mul.mp hqDifference with hindex | hstep
            · exact hindex
            · exact False.elim (hqStep hstep)
          have hdifferenceLt : first - second < q := by
            omega
          have hzero : first - second = 0 :=
            Nat.eq_zero_of_dvd_of_lt hqIndex hdifferenceLt
          omega
    _ = length / q + 1 := by simp
def fixedProgressionBadIndices
    (step residue lower K : Nat) (R : Finset Nat) : Finset Nat :=
  (Finset.range (K + 1)).filter fun index =>
    ∃ q ∈ R, q ∣ fixedProgressionCandidate step residue lower index

theorem fixedProgressionBadIndices_eq_biUnion
    (step residue lower K : Nat) (R : Finset Nat) :
    fixedProgressionBadIndices step residue lower K R =
      R.biUnion (fixedProgressionKilledIndices step residue lower K) := by
  ext index
  constructor
  · intro hindex
    obtain ⟨hindexRange, q, hq, hqDvd⟩ :=
      Finset.mem_filter.mp hindex
    exact Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_filter.mpr ⟨hindexRange, hqDvd⟩⟩
  · intro hindex
    obtain ⟨q, hq, hindexKilled⟩ := Finset.mem_biUnion.mp hindex
    obtain ⟨hindexRange, hqDvd⟩ := Finset.mem_filter.mp hindexKilled
    exact Finset.mem_filter.mpr ⟨hindexRange, q, hq, hqDvd⟩

theorem fixedProgressionBadIndices_card_le
    {step residue lower K : Nat} {R : Finset Nat}
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hKq : ∀ q ∈ R, K < q)
    (hstep : ∀ q ∈ R, ¬ q ∣ step) :
    (fixedProgressionBadIndices step residue lower K R).card ≤ R.card := by
  rw [fixedProgressionBadIndices_eq_biUnion]
  calc
    (R.biUnion (fixedProgressionKilledIndices step residue lower K)).card ≤
        ∑ q ∈ R,
          (fixedProgressionKilledIndices step residue lower K q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ R, 1 := by
      exact Finset.sum_le_sum fun q hq =>
        fixedProgressionKilledIndices_card_le_one
          (hprime q hq) (hKq q hq) (hstep q hq)
    _ = R.card := by simp

/-- Generic `K+1`-candidate survivor for a fixed arithmetic progression.
Composite and permanent-prime properties are supplied separately by the
chosen progression. -/
theorem exists_fixedProgressionPaidSurvivor
    {step residue lower K : Nat} {R : Finset Nat}
    (hstepPos : 0 < step) (hresidueStep : residue < step)
    (hcard : R.card ≤ K)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hKq : ∀ q ∈ R, K < q)
    (hstepAvoid : ∀ q ∈ R, ¬ q ∣ step) :
    ∃ index,
      index ≤ K ∧
      lower < fixedProgressionCandidate step residue lower index ∧
      fixedProgressionCandidate step residue lower index ≤
        lower + step * (K + 1) ∧
      ∀ q ∈ R,
        ¬ q ∣ fixedProgressionCandidate step residue lower index := by
  have hbadCard :
      (fixedProgressionBadIndices step residue lower K R).card ≤ K :=
    (fixedProgressionBadIndices_card_le hprime hKq hstepAvoid).trans hcard
  have hbadLt :
      (fixedProgressionBadIndices step residue lower K R).card <
        (Finset.range (K + 1)).card := by
    simpa using Nat.lt_of_le_of_lt hbadCard (Nat.lt_succ_self K)
  obtain ⟨index, hindexRange, hindexGood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadLt
  have hindex : index ≤ K := by
    have := Finset.mem_range.mp hindexRange
    omega
  refine ⟨index, hindex,
    fixedProgressionCandidate_gt hstepPos hresidueStep,
    fixedProgressionCandidate_le (Nat.le_of_lt hresidueStep) hindex, ?_⟩
  intro q hq hqDvd
  apply hindexGood
  rw [fixedProgressionBadIndices, Finset.mem_filter]
  exact ⟨hindexRange, q, hq, hqDvd⟩

end


end Erdos1212Kernel
