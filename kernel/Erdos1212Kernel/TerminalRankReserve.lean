import Erdos1212Kernel.ExactRankOuterBoundaryHistory

namespace Erdos1212Kernel

/-!
# The complementary exact-rank reserve

The canonical outer-boundary history splits the exact nonpermanent label rank
into the labels recruited by the unchanged trace and the complementary labels
which were not recruited there.  This file records the arithmetic content of
the complementary branch.  A finite set of distinct labels all exceeding the
permanent cutoff `11` cannot be numerically cheap: after ordering them, its
`j`-th member is at least `12 + j`.  Consequently its Euler denominator has
factorial (indeed shifted-factorial) growth in the complementary rank.

This is the exact finite reserve used by the terminal rank split.  It does not
introduce a probabilistic independence hypothesis or move the contour cut.
-/

/-- The least possible product of `r` distinct natural labels greater than
eleven. -/
def complementaryRankReserve (r : Nat) : Nat :=
  ∏ j ∈ Finset.range r, (12 + j)

/-- Distinct labels above eleven have at least the shifted-factorial product.
The proof removes the largest label.  Cardinality inside the integer interval
`[12, qmax]` forces that label to pay the final factor. -/
theorem complementaryRankReserve_le_prod
    (labels : Finset Nat)
    (hlarge : ∀ q ∈ labels, 11 < q) :
    complementaryRankReserve labels.card ≤ ∏ q ∈ labels, q := by
  classical
  induction labels using Finset.strongInductionOn with
  | _ labels ih =>
      by_cases hnonempty : labels.Nonempty
      · let qmax := labels.max' hnonempty
        have hqmaxMem : qmax ∈ labels := Finset.max'_mem labels hnonempty
        have heraseStrict : labels.erase qmax ⊂ labels :=
          Finset.erase_ssubset hqmaxMem
        have heraseLarge : ∀ q ∈ labels.erase qmax, 11 < q := by
          intro q hq
          exact hlarge q (Finset.mem_of_mem_erase hq)
        have hinduction :
            complementaryRankReserve (labels.erase qmax).card ≤
              ∏ q ∈ labels.erase qmax, q :=
          ih (labels.erase qmax) heraseStrict heraseLarge
        have hsubset : labels ⊆ Finset.Icc 12 qmax := by
          intro q hq
          have hqLarge := hlarge q hq
          exact Finset.mem_Icc.mpr
            ⟨by omega, Finset.le_max' labels q hq⟩
        have hcardInterval :
            labels.card ≤ (Finset.Icc 12 qmax).card :=
          Finset.card_le_card hsubset
        have hqmaxLower : 12 + (labels.erase qmax).card ≤ qmax := by
          rw [Nat.card_Icc] at hcardInterval
          have heraseCard := Finset.card_erase_add_one hqmaxMem
          omega
        have heraseCard := Finset.card_erase_add_one hqmaxMem
        rw [← heraseCard, complementaryRankReserve, Finset.prod_range_succ]
        calc
          complementaryRankReserve (labels.erase qmax).card *
                (12 + (labels.erase qmax).card)
              ≤ (∏ q ∈ labels.erase qmax, q) * qmax :=
            Nat.mul_le_mul hinduction hqmaxLower
          _ = ∏ q ∈ labels, q :=
            Finset.prod_erase_mul labels id hqmaxMem
      · have hempty : labels = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
        simp [hempty, complementaryRankReserve]

/-- The shifted reserve dominates the ordinary factorial. -/
theorem factorial_le_complementaryRankReserve (r : Nat) :
    r.factorial ≤ complementaryRankReserve r := by
  rw [Nat.factorial_eq_prod_range_add_one, complementaryRankReserve]
  apply Finset.prod_le_prod
  · intro j _hj
    omega
  · intro j _hj
    omega

/-- In particular, the product of `r` distinct labels above eleven has
factorial growth in `r`. -/
theorem factorial_card_le_prod
    (labels : Finset Nat)
    (hlarge : ∀ q ∈ labels, 11 < q) :
    labels.card.factorial ≤ ∏ q ∈ labels, q :=
  (factorial_le_complementaryRankReserve labels.card).trans
    (complementaryRankReserve_le_prod labels hlarge)

/-- The reciprocal Euler weight of a complementary label set is bounded by
the inverse factorial of its cardinality. -/
theorem inverse_prod_le_inverse_factorial_card
    (labels : Finset Nat)
    (hlarge : ∀ q ∈ labels, 11 < q) :
    (∏ q ∈ labels, (q : NNReal))⁻¹ ≤
      ((labels.card.factorial : NNReal))⁻¹ := by
  have hnat := factorial_card_le_prod labels hlarge
  have hcast :
      (labels.card.factorial : NNReal) ≤
        ∏ q ∈ labels, (q : NNReal) := by
    have hcastNat :
        (labels.card.factorial : NNReal) ≤
          ((∏ q ∈ labels, q : Nat) : NNReal) :=
      Nat.cast_le.mpr hnat
    simpa only [Nat.cast_prod] using hcastNat
  exact inv_anti₀ (by positivity) hcast

/-- Arbitrary exponential bookkeeping is summable against the complementary
factorial reserve. -/
theorem complementaryFactorialMajorant_summable (growth : NNReal) :
    Summable
      (fun r : Nat ↦
        growth ^ r * ((r.factorial : NNReal))⁻¹) := by
  rw [← NNReal.summable_coe]
  simpa [div_eq_mul_inv] using
    (Real.summable_pow_div_factorial (growth : Real))

/-- Even after the exact rank is only known to be at most twice the charged
cardinality, arbitrary exponential bookkeeping remains summable. -/
theorem halfRankFactorialMajorant_summable (growth : NNReal) :
    Summable
      (fun K : Nat ↦
        growth ^ K * ((((K + 1) / 2).factorial : NNReal))⁻¹) := by
  let f : Nat → NNReal := fun K ↦
    growth ^ K * ((((K + 1) / 2).factorial : NNReal))⁻¹
  apply (Equiv.natSumNatEquivNat.summable_iff).mp
  apply Summable.sum
  · change Summable (fun r : Nat ↦ f (2 * r))
    convert complementaryFactorialMajorant_summable (growth ^ 2) using 1
    funext r
    have hhalf : (2 * r + 1) / 2 = r := by omega
    dsimp [f]
    rw [hhalf, pow_mul]
  · change Summable (fun r : Nat ↦ f (2 * r + 1))
    have hmajorant :
        Summable
          (fun r : Nat ↦
            growth *
              ((growth ^ 2) ^ r * ((r.factorial : NNReal))⁻¹)) :=
      (complementaryFactorialMajorant_summable (growth ^ 2)).mul_left growth
    apply NNReal.summable_of_le _ hmajorant
    intro r
    have hhalf : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    have hfactorial :
        (r.factorial : NNReal) ≤ ((r + 1).factorial : NNReal) := by
      exact Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ r))
    have hinverse :
        (((r + 1).factorial : NNReal))⁻¹ ≤
          ((r.factorial : NNReal))⁻¹ :=
      inv_anti₀ (by positivity) hfactorial
    dsimp [f]
    rw [hhalf, pow_succ, pow_mul]
    calc
      (growth ^ 2) ^ r * growth *
            (((r + 1).factorial : NNReal))⁻¹
          = growth *
              ((growth ^ 2) ^ r *
                (((r + 1).factorial : NNReal))⁻¹) := by
            ac_rfl
      _ ≤ growth *
            ((growth ^ 2) ^ r * ((r.factorial : NNReal))⁻¹) := by
          exact mul_le_mul_left' (mul_le_mul_left' hinverse _) _

/-- A quarter-rank factorial still absorbs arbitrary exponential records. -/
theorem quarterRankFactorialMajorant_summable (growth : NNReal) :
    Summable
      (fun K : Nat ↦
        growth ^ K * (((K / 4).factorial : NNReal))⁻¹) := by
  let f : Nat → NNReal := fun K ↦
    growth ^ K * (((K / 4).factorial : NNReal))⁻¹
  have hresidue : ∀ c : Nat, c < 4 →
      Summable (fun s : Nat ↦ f (4 * s + c)) := by
    intro c hc
    convert
      (complementaryFactorialMajorant_summable (growth ^ 4)).mul_left
        (growth ^ c) using 1
    funext s
    have hdiv : (4 * s + c) / 4 = s := by omega
    dsimp [f]
    rw [hdiv, pow_add, pow_mul]
    ac_rfl
  let e : Equiv (Fin 4 × Nat) Nat :=
    (Equiv.prodComm (Fin 4) Nat).trans (Nat.divModEquiv 4).symm
  rw [← NNReal.summable_coe]
  apply e.summable_iff.mp
  apply (summable_prod_of_nonneg
    (fun p ↦ (f (e p)).coe_nonneg)).2
  constructor
  · intro c
    have hc := hresidue c.val c.isLt
    rw [← NNReal.summable_coe] at hc
    convert hc using 1
    funext s
    simp [e, f, Nat.divModEquiv_symm_apply, mul_comm]
  · exact Summable.of_finite

/-- Squaring a quarter-rank factorial never exceeds the half-rank
factorial. -/
theorem quarterRank_factorial_sq_le_halfRank_factorial (K : Nat) :
    (K / 4).factorial ^ 2 ≤ ((K + 1) / 2).factorial := by
  have hfactorialPow :
      (K / 4).factorial ≤ (K / 4) ^ (K / 4) :=
    Nat.factorial_le_pow (K / 4)
  have hdouble : K / 4 ≤ 2 * (K / 4) := by omega
  have hfactorialDouble :=
    Nat.factorial_mul_pow_sub_le_factorial hdouble
  have hsquare :
      (K / 4).factorial ^ 2 ≤ (2 * (K / 4)).factorial := by
    calc
      (K / 4).factorial ^ 2 =
          (K / 4).factorial * (K / 4).factorial := by
            rw [pow_two]
      _ ≤ (K / 4).factorial * (K / 4) ^ (K / 4) :=
        Nat.mul_le_mul_left _ hfactorialPow
      _ ≤ (2 * (K / 4)).factorial := by
        have hsub : 2 * (K / 4) - K / 4 = K / 4 := by omega
        simpa only [hsub] using hfactorialDouble
  have hquarterHalf : 2 * (K / 4) ≤ (K + 1) / 2 := by
    omega
  exact hsquare.trans (Nat.factorial_le hquarterHalf)

/-- The source-independent terminal majorant after the half-rank factorial
charge, including one global prefactor and arbitrary exponential records. -/
noncomputable def terminalRankMajorant
    (prefactor growth : NNReal) (K : Nat) : NNReal :=
  prefactor *
    (growth ^ K * ((((K + 1) / 2).factorial : NNReal))⁻¹)

theorem terminalRankMajorant_summable
    (prefactor growth : NNReal) :
    Summable (terminalRankMajorant prefactor growth) := by
  simpa [terminalRankMajorant] using
    (halfRankFactorialMajorant_summable growth).mul_left prefactor

/-- A concrete terminal charging inequality against the factorial majorant
implies the exact order-of-limits rank tightness needed by the original
high-corridor coefficient. -/
theorem asymptoticRankTight_of_terminalRankMajorant
    (prefactor growth : NNReal)
    (hcharge : ∀ N K,
      highCorridorRankMass N K ≤
        terminalRankMajorant prefactor growth K) :
    AsymptoticRankTight highCorridorRankMass := by
  intro ε hε
  let majorant := terminalRankMajorant prefactor growth
  have hsummable : Summable majorant :=
    terminalRankMajorant_summable prefactor growth
  have htendsto :
      Filter.Tendsto (tailMass majorant) Filter.atTop (nhds 0) :=
    tailMass_tendsto_zero majorant hsummable
  have heventually :
      ∀ᶠ M : Nat in Filter.atTop, tailMass majorant M < ε :=
    (tendsto_order.1 htendsto).2 ε hε
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨K, hK⟩ := heventually
  refine ⟨K, Filter.Eventually.of_forall ?_⟩
  intro N
  have htailLe :
      rankTail highCorridorRankMass N K ≤
        tailMass majorant (K + 1) := by
    unfold rankTail tailMass
    apply Summable.tsum_le_tsum
    · intro n
      exact hcharge N n
    · exact NNReal.summable_comp_injective
        (highCorridorRankMass_summable N) Subtype.val_injective
    · exact NNReal.summable_comp_injective
        hsummable Subtype.val_injective
  exact htailLe.trans_lt (hK (K + 1) (by omega))

/-- Every complementary member in an exact-rank partition remains an actual
nonpermanent boundary label and therefore exceeds the permanent cutoff. -/
theorem residualLabels_large_of_exactRank_partition
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {labels : List Nat}
    {residualLabels : Finset Nat}
    (hpartition :
      labels.toFinset ∪ residualLabels =
        exactNonpermanentBoundaryLabels start hbounded) :
    ∀ q ∈ residualLabels, 11 < q := by
  intro q hq
  have hqExact :
      q ∈ exactNonpermanentBoundaryLabels start hbounded := by
    rw [← hpartition]
    exact Finset.mem_union_right labels.toFinset hq
  exact (Finset.mem_filter.mp hqExact).2

/-- The actual unchanged outer trace together with the exact terminal rank
partition and its complementary factorial reserve. -/
structure ExactRankTerminalHistory
    (N K : Nat) (root : Nat × Nat) where
  hbounded :
    ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)
  hrootCorridor : root ∈ primeCorridorRoots N
  period : Nat
  anchor : LatticePoint
  walk : starLatticeGraph.Walk anchor anchor
  labels : List Nat
  residualLabels : Finset Nat
  anchor_eq :
    anchor = primeCorridorOuterBoundaryAnchor hrootCorridor hbounded
  period_pos : 0 < period
  history :
    ActualPromotedExitHistory (Nat.primesLE 11) walk.support labels
  labels_nodup : labels.Nodup
  labels_length_le : labels.length ≤ K
  rank_partition :
    labels.toFinset ∪ residualLabels =
      exactNonpermanentBoundaryLabels
        (primeCorridorPoint root) hbounded
  rank_disjoint : Disjoint labels.toFinset residualLabels
  rank_eq : labels.length + residualLabels.card = K
  rank_dichotomy :
    K ≤ 2 * labels.length ∨ K ≤ 2 * residualLabels.card
  residual_large : ∀ q ∈ residualLabels, 11 < q
  residual_reserve :
    complementaryRankReserve residualLabels.card ≤
      ∏ q ∈ residualLabels, q
  frontier :
    ∀ point ∈ walk.support,
      point ∈ safeComponentFrontier (primeCorridorPoint root)
  one_final_window :
    ∀ point ∈ walk.support,
      point ∈ latticeWindow (primeCorridorPoint root)
        (componentRankGap K + 1)
  reachable_in_final_state :
    ∀ point ∈ walk.support,
      ActualPromotedStarReachable
        (promotedExitFinalLabels (Nat.primesLE 11) labels)
        anchor
        point

/-- Every bounded high-corridor root of exact rank has one literal terminal
history object with the complementary Euler reserve already attached. -/
theorem exists_exactRankTerminalHistory
    {N K : Nat} {root : Nat × Nat}
    (hN : 4 * componentRankThreshold K ≤ N)
    (hroot : root ∈ boundedHighCorridorRootsOfRank N K) :
    Nonempty (ExactRankTerminalHistory N K root) := by
  obtain ⟨hbounded, hrootCorridor, period, anchor, walk, labels,
    residualLabels, hanchor, hperiod, hhistory, hnodup, hlength,
    hpartition, hdisjoint, hrank, hdichotomy, hfrontier, hwindow,
    hreachable⟩ :=
    exists_exactRankCanonicalOuterBoundaryHistory hN hroot
  have hlarge : ∀ q ∈ residualLabels, 11 < q :=
    residualLabels_large_of_exactRank_partition hpartition
  have hreserve :
      complementaryRankReserve residualLabels.card ≤
        ∏ q ∈ residualLabels, q :=
    complementaryRankReserve_le_prod residualLabels hlarge
  exact ⟨⟨hbounded, hrootCorridor, period, anchor, walk, labels,
    residualLabels, hanchor, hperiod, hhistory, hnodup, hlength,
    hpartition, hdisjoint, hrank, hdichotomy, hlarge, hreserve,
    hfrontier, hwindow, hreachable⟩⟩

/-- On the complementary half of the exact-rank dichotomy, the actual
residual product pays a factorial at half the full rank. -/
theorem ExactRankTerminalHistory.halfRank_factorial_le_residual_prod
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root)
    (hresidual : K ≤ 2 * H.residualLabels.card) :
    ((K + 1) / 2).factorial ≤
      ∏ q ∈ H.residualLabels, q := by
  have hhalf : (K + 1) / 2 ≤ H.residualLabels.card := by
    omega
  exact (Nat.factorial_le hhalf).trans
    (factorial_card_le_prod H.residualLabels H.residual_large)

/-- Every label actually recruited by the terminal scan is also above the
permanent cutoff. -/
theorem ExactRankTerminalHistory.recruited_large
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root) :
    ∀ q ∈ H.labels.toFinset, 11 < q := by
  intro q hq
  have hqList : q ∈ H.labels := List.mem_toFinset.mp hq
  have hqPrime : Nat.Prime q := H.history.labels_prime q hqList
  have hqFresh : q ∉ Nat.primesLE 11 :=
    H.history.labels_fresh_from_initial q hqList
  by_contra hnotLarge
  exact hqFresh (Nat.mem_primesLE.mpr ⟨by omega, hqPrime⟩)

/-- On the recruited half of the exact-rank dichotomy, the without-
replacement scan itself pays a factorial at half the full rank. -/
theorem ExactRankTerminalHistory.halfRank_factorial_le_recruited_prod
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root)
    (hrecruited : K ≤ 2 * H.labels.length) :
    ((K + 1) / 2).factorial ≤
      ∏ q ∈ H.labels.toFinset, q := by
  have hhalf : (K + 1) / 2 ≤ H.labels.length := by
    omega
  have hcard : H.labels.toFinset.card = H.labels.length :=
    List.toFinset_card_of_nodup H.labels_nodup
  have hfactorial :
      H.labels.length.factorial ≤
        ∏ q ∈ H.labels.toFinset, q := by
    rw [← hcard]
    exact factorial_card_le_prod H.labels.toFinset H.recruited_large
  exact (Nat.factorial_le hhalf).trans hfactorial

/-- The exact terminal split always exposes a genuine half-rank factorial
Euler denominator, on the recruited side or on the complementary side. -/
theorem ExactRankTerminalHistory.halfRank_factorial_dichotomy
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root) :
    (K ≤ 2 * H.labels.length ∧
        ((K + 1) / 2).factorial ≤
          ∏ q ∈ H.labels.toFinset, q) ∨
      (K ≤ 2 * H.residualLabels.card ∧
        ((K + 1) / 2).factorial ≤
          ∏ q ∈ H.residualLabels, q) := by
  rcases H.rank_dichotomy with hrecruited | hresidual
  · exact Or.inl
      ⟨hrecruited, H.halfRank_factorial_le_recruited_prod hrecruited⟩
  · exact Or.inr
      ⟨hresidual, H.halfRank_factorial_le_residual_prod hresidual⟩

end Erdos1212Kernel
