import Mathlib.Data.Nat.ChineseRemainder
import Erdos1212Kernel.TerminalRankReserve

namespace Erdos1212Kernel

/-!
# Exact CRT charge on one unchanged translation fibre

A paid history may use a fresh prime phase only when all histories being
compared live in the same translation fibre.  This file supplies the literal
finite counting statement behind that phrase.  For a fixed relative record,
distinct prime labels impose one residue in each translation coordinate.
Their conjunction is one residue modulo the product, so on a torus whose
period is divisible by that product the fibre has density at most the inverse
square of the product.

This is a set-theoretic count.  It contains no independence assumption and
does not condition a translation coordinate to be prime.
-/

/-- One coordinate of a fixed relative phase record inside `[0, period)`. -/
def translationCoordinatePhaseCell
    (period : Nat) (labels : Finset Nat) (residue : Nat → Nat) : Finset Nat :=
  (Finset.range period).filter fun x =>
    ∀ q ∈ labels, x ≡ residue q [MOD q]

/-- The two-coordinate translation cell of one fixed relative record. -/
def translationPhaseCell
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat) : Finset (Nat × Nat) :=
  translationCoordinatePhaseCell period labels residueX ×ˢ
    translationCoordinatePhaseCell period labels residueY

/-- Distinct prime moduli combine into the product modulus. -/
theorem modEq_prod_of_prime_constraints
    (labels : Finset Nat)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    {x y : Nat}
    (hxy : ∀ q ∈ labels, x ≡ y [MOD q]) :
    x ≡ y [MOD ∏ q ∈ labels, q] := by
  classical
  induction labels using Finset.induction_on with
  | empty =>
      change x % 1 = y % 1
      simp only [Nat.mod_one]
  | @insert q labels hq ih =>
      rw [Finset.prod_insert hq]
      have hqPrime : Nat.Prime q := hprime q (Finset.mem_insert_self q labels)
      have hrestPrime : ∀ r ∈ labels, Nat.Prime r := by
        intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      have hcoprime : Nat.Coprime q (∏ r ∈ labels, r) := by
        rw [Nat.coprime_prod_right_iff]
        intro r hr
        have hne : q ≠ r := by
          intro hqr
          apply hq
          simpa [hqr] using hr
        exact (Nat.coprime_primes hqPrime (hrestPrime r hr)).mpr
          hne
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
        ⟨hxy q (Finset.mem_insert_self q labels),
          ih hrestPrime (fun r hr => hxy r (Finset.mem_insert_of_mem hr))⟩

/-- A fixed one-coordinate phase record occupies at most one point per
quotient block. -/
theorem translationCoordinatePhaseCell_card_le
    (period : Nat) (labels : Finset Nat) (residue : Nat → Nat)
    (hprime : ∀ q ∈ labels, Nat.Prime q) :
    (translationCoordinatePhaseCell period labels residue).card ≤
      period / (∏ q ∈ labels, q) + 1 := by
  classical
  let modulus := ∏ q ∈ labels, q
  let cell := translationCoordinatePhaseCell period labels residue
  change cell.card ≤ period / modulus + 1
  calc
    cell.card ≤ (Finset.range (period / modulus + 1)).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => x / modulus) ?_ ?_
      · intro x hx
        have hxData := Finset.mem_filter.mp hx
        have hxPeriod := Finset.mem_range.mp hxData.1
        apply Finset.mem_range.mpr
        have hdiv : x / modulus ≤ period / modulus :=
          Nat.div_le_div_right (Nat.le_of_lt hxPeriod)
        simpa using Nat.lt_succ_of_le hdiv
      · intro x hx y hy hquotient
        change x / modulus = y / modulus at hquotient
        have hxData := Finset.mem_filter.mp hx
        have hyData := Finset.mem_filter.mp hy
        have hxyEach : ∀ q ∈ labels, x ≡ y [MOD q] := by
          intro q hq
          exact (hxData.2 q hq).trans (hyData.2 q hq).symm
        have hxyProduct :=
          modEq_prod_of_prime_constraints labels hprime hxyEach
        have hremainder : x % modulus = y % modulus := hxyProduct
        calc
          x = modulus * (x / modulus) + x % modulus :=
            (Nat.div_add_mod x modulus).symm
          _ = modulus * (y / modulus) + y % modulus := by
            rw [hquotient, hremainder]
          _ = y := Nat.div_add_mod y modulus
    _ = period / modulus + 1 := Finset.card_range _

/-- The literal two-coordinate count in an arbitrary finite box.  Unlike the
torus form below, this keeps both quotient-boundary contributions and hence
does not assume that the growing prime product divides the box side. -/
theorem translationPhaseCell_card_le
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hprime : ∀ q ∈ labels, Nat.Prime q) :
    (translationPhaseCell period labels residueX residueY).card ≤
      (period / (∏ q ∈ labels, q) + 1) ^ 2 := by
  rw [translationPhaseCell, Finset.card_product, pow_two]
  exact Nat.mul_le_mul
    (translationCoordinatePhaseCell_card_le
      period labels residueX hprime)
    (translationCoordinatePhaseCell_card_le
      period labels residueY hprime)

private theorem natCast_natDiv_le_nnrealDiv
    (a b : Nat) (hb : 0 < b) :
    ((a / b : Nat) : NNReal) ≤ (a : NNReal) / (b : NNReal) := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast Nat.div_mul_le_self a b

private theorem nnreal_div_add_one_normalized_sq
    (period modulus : NNReal) (hperiod : period ≠ 0) :
    ((period / modulus + 1) ^ 2) / period ^ 2 =
      (modulus⁻¹ + period⁻¹) ^ 2 := by
  have hcancel : (period / modulus) / period = modulus⁻¹ := by
    simp only [div_eq_mul_inv]
    calc
      (period * modulus⁻¹) * period⁻¹ =
          modulus⁻¹ * (period * period⁻¹) := by ac_rfl
      _ = modulus⁻¹ := by simp [hperiod]
  have hnormalize :
      (period / modulus + 1) / period = modulus⁻¹ + period⁻¹ := by
    rw [add_div, hcancel]
    simp only [one_div]
  rw [← hnormalize, div_pow]

set_option maxHeartbeats 500000 in
/-- Normalized arbitrary-box form of the exact count.  The right side is the
square of the CRT density plus its honest finite-box atom.  In particular,
the final `period⁻¹` term is visible and cannot be discarded when the product
modulus is allowed to grow with the box. -/
theorem translationPhaseCell_density_le_inverse_prod_add_boundary_sq
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hprime : ∀ q ∈ labels, Nat.Prime q) :
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      ((∏ q ∈ labels, (q : NNReal))⁻¹ + (period : NNReal)⁻¹) ^ 2 := by
  let modulus : Nat := ∏ q ∈ labels, q
  have hmodulusPos : 0 < modulus := by
    dsimp [modulus]
    apply Finset.prod_pos
    intro q hq
    exact (hprime q hq).pos
  have hcount :=
    translationPhaseCell_card_le period labels residueX residueY hprime
  have hquotient :
      ((period / modulus : Nat) : NNReal) ≤
        (period : NNReal) / (modulus : NNReal) := by
    exact natCast_natDiv_le_nnrealDiv period modulus hmodulusPos
  have hcountNN :
      ((translationPhaseCell period labels residueX residueY).card : NNReal) ≤
        (((period / modulus : Nat) : NNReal) + 1) ^ 2 := by
    have hcast :
        ((translationPhaseCell period labels residueX residueY).card : NNReal) ≤
          ((((period / modulus + 1) ^ 2 : Nat)) : NNReal) :=
      Nat.cast_le.mpr hcount
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hcast
  have hperiodNe : (period : NNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hperiodPos)
  calc
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
          (period : NNReal) ^ 2
        ≤ ((((period / modulus : Nat) : NNReal) + 1) ^ 2) /
            (period : NNReal) ^ 2 := by
          exact div_le_div_of_nonneg_right hcountNN (by positivity)
    _ ≤ (((period : NNReal) / (modulus : NNReal) + 1) ^ 2) /
            (period : NNReal) ^ 2 := by
          exact div_le_div_of_nonneg_right
            (pow_le_pow_left' (add_le_add hquotient le_rfl) 2)
            (by positivity)
    _ = ((modulus : NNReal)⁻¹ + (period : NNReal)⁻¹) ^ 2 := by
      exact nnreal_div_add_one_normalized_sq _ _ hperiodNe
    _ = ((∏ q ∈ labels, (q : NNReal))⁻¹ +
          (period : NNReal)⁻¹) ^ 2 := by
      simp only [modulus, Nat.cast_prod]

set_option maxHeartbeats 500000 in
/-- Arbitrary finite-box half-rank charge with the single-atom boundary kept
explicitly.  This is the finite-box inequality needed before the sourcewise
word shell can absorb the large-modulus branch. -/
theorem translationPhaseCell_density_le_halfRankFactorial_add_boundary_sq
    (period K : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hlarge : ∀ q ∈ labels, 11 < q)
    (hhalf : K ≤ 2 * labels.card) :
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      (((((K + 1) / 2).factorial : NNReal))⁻¹ +
        (period : NNReal)⁻¹) ^ 2 := by
  have hphase :=
    translationPhaseCell_density_le_inverse_prod_add_boundary_sq
      period labels residueX residueY hperiodPos hprime
  have hproduct := inverse_prod_le_inverse_factorial_card labels hlarge
  have hcard : (K + 1) / 2 ≤ labels.card := by omega
  have hfactorial :
      ((((K + 1) / 2).factorial : NNReal)) ≤
        (labels.card.factorial : NNReal) := by
    exact Nat.cast_le.mpr (Nat.factorial_le hcard)
  have hinverse :
      (∏ q ∈ labels, (q : NNReal))⁻¹ ≤
        ((((K + 1) / 2).factorial : NNReal))⁻¹ :=
    hproduct.trans (inv_anti₀ (by positivity) hfactorial)
  exact hphase.trans (pow_le_pow_left' (add_le_add hinverse le_rfl) 2)

/-- If the torus period contains the complete phase modulus, the harmless
boundary `+1` disappears and the coordinate cell has the exact `period/Q`
upper bound. -/
theorem translationCoordinatePhaseCell_card_le_of_prod_dvd
    (period : Nat) (labels : Finset Nat) (residue : Nat → Nat)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hperiod : (∏ q ∈ labels, q) ∣ period) :
    (translationCoordinatePhaseCell period labels residue).card ≤
      period / (∏ q ∈ labels, q) := by
  classical
  let modulus := ∏ q ∈ labels, q
  let cell := translationCoordinatePhaseCell period labels residue
  have hmodulusPos : 0 < modulus := by
    dsimp [modulus]
    apply Finset.prod_pos
    intro q hq
    exact (hprime q hq).pos
  change cell.card ≤ period / modulus
  calc
    cell.card ≤ (Finset.range (period / modulus)).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => x / modulus) ?_ ?_
      · intro x hx
        have hxData := Finset.mem_filter.mp hx
        have hxPeriod := Finset.mem_range.mp hxData.1
        apply Finset.mem_range.mpr
        rw [Nat.div_lt_iff_lt_mul hmodulusPos]
        rw [Nat.div_mul_cancel hperiod]
        exact hxPeriod
      · intro x hx y hy hquotient
        change x / modulus = y / modulus at hquotient
        have hxData := Finset.mem_filter.mp hx
        have hyData := Finset.mem_filter.mp hy
        have hxyEach : ∀ q ∈ labels, x ≡ y [MOD q] := by
          intro q hq
          exact (hxData.2 q hq).trans (hyData.2 q hq).symm
        have hxyProduct :=
          modEq_prod_of_prime_constraints labels hprime hxyEach
        have hremainder : x % modulus = y % modulus := hxyProduct
        calc
          x = modulus * (x / modulus) + x % modulus :=
            (Nat.div_add_mod x modulus).symm
          _ = modulus * (y / modulus) + y % modulus := by
            rw [hquotient, hremainder]
          _ = y := Nat.div_add_mod y modulus
    _ = period / modulus := Finset.card_range _

/-- The paid two-coordinate charge: a fixed relative record has at most
`(period / Q)^2` translations in the unchanged torus. -/
theorem translationPhaseCell_card_le_of_prod_dvd
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hperiod : (∏ q ∈ labels, q) ∣ period) :
    (translationPhaseCell period labels residueX residueY).card ≤
      (period / (∏ q ∈ labels, q)) ^ 2 := by
  rw [translationPhaseCell, Finset.card_product, pow_two]
  exact Nat.mul_le_mul
    (translationCoordinatePhaseCell_card_le_of_prod_dvd
      period labels residueX hprime hperiod)
    (translationCoordinatePhaseCell_card_le_of_prod_dvd
      period labels residueY hprime hperiod)

/-- In normalized form the preceding count is the literal product
`∏ q⁻²`. -/
theorem translationPhaseCell_density_le_inverse_prod_sq
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hperiod : (∏ q ∈ labels, q) ∣ period) :
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      ((∏ q ∈ labels, (q : NNReal))⁻¹) ^ 2 := by
  let modulus : Nat := ∏ q ∈ labels, q
  have hmodulusPos : 0 < modulus := by
    dsimp [modulus]
    apply Finset.prod_pos
    intro q hq
    exact (hprime q hq).pos
  have hcount :=
    translationPhaseCell_card_le_of_prod_dvd
      period labels residueX residueY hprime hperiod
  have hquotientIdentity :
      ((period / modulus : Nat) : NNReal) =
        (period : NNReal) / (modulus : NNReal) := by
    apply NNReal.eq
    change ((period / modulus : Nat) : Real) =
      (period : Real) / (modulus : Real)
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hmodulusPos)]
    exact_mod_cast Nat.div_mul_cancel hperiod
  have hcountNN :
      ((translationPhaseCell period labels residueX residueY).card : NNReal) ≤
        ((period / modulus : Nat) : NNReal) ^ 2 := by
    exact_mod_cast hcount
  calc
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
          (period : NNReal) ^ 2
        ≤ (((period / modulus : Nat) : NNReal) ^ 2) /
            (period : NNReal) ^ 2 := by gcongr
    _ = ((modulus : NNReal)⁻¹) ^ 2 := by
      rw [hquotientIdentity]
      field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hperiodPos),
        Nat.cast_ne_zero.mpr (ne_of_gt hmodulusPos)]
    _ = ((∏ q ∈ labels, (q : NNReal))⁻¹) ^ 2 := by
      simp only [modulus, Nat.cast_prod]

/-- Distinct nonpermanent prime identities turn the literal CRT product
charge into a factorial charge in the number of identities. -/
theorem translationPhaseCell_density_le_inverse_factorial_sq
    (period : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hlarge : ∀ q ∈ labels, 11 < q)
    (hperiod : (∏ q ∈ labels, q) ∣ period) :
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      (((labels.card.factorial : NNReal))⁻¹) ^ 2 := by
  have hphase := translationPhaseCell_density_le_inverse_prod_sq
    period labels residueX residueY hperiodPos hprime hperiod
  have hinverse := inverse_prod_le_inverse_factorial_card labels hlarge
  exact hphase.trans (pow_le_pow_left' hinverse 2)

/-- If these paid identities carry at least half of an exact rank `K`, the
same unchanged translation fibre pays the half-rank factorial required by
the terminal split. -/
theorem translationPhaseCell_density_le_halfRankFactorial_sq
    (period K : Nat) (labels : Finset Nat)
    (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hprime : ∀ q ∈ labels, Nat.Prime q)
    (hlarge : ∀ q ∈ labels, 11 < q)
    (hhalf : K ≤ 2 * labels.card)
    (hperiod : (∏ q ∈ labels, q) ∣ period) :
    ((translationPhaseCell period labels residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      (((((K + 1) / 2).factorial : NNReal))⁻¹) ^ 2 := by
  have hphase := translationPhaseCell_density_le_inverse_factorial_sq
    period labels residueX residueY hperiodPos hprime hlarge hperiod
  have hcard : (K + 1) / 2 ≤ labels.card := by omega
  have hfactorial :
      ((((K + 1) / 2).factorial : NNReal)) ≤
        (labels.card.factorial : NNReal) := by
    exact Nat.cast_le.mpr (Nat.factorial_le hcard)
  have hinverse :
      ((labels.card.factorial : NNReal))⁻¹ ≤
        ((((K + 1) / 2).factorial : NNReal))⁻¹ :=
    inv_anti₀ (by positivity) hfactorial
  exact hphase.trans (pow_le_pow_left' hinverse 2)

/-- Complementary exact-rank labels are genuine prime identities, not only
large natural labels. -/
theorem ExactRankTerminalHistory.residual_prime
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root) :
    ∀ q ∈ H.residualLabels, Nat.Prime q := by
  intro q hq
  have hqExact :
      q ∈ exactNonpermanentBoundaryLabels
        (primeCorridorPoint root) H.hbounded := by
    rw [← H.rank_partition]
    exact Finset.mem_union_right H.labels.toFinset hq
  have hqData := Finset.mem_filter.mp hqExact
  obtain ⟨point, hpoint, hpointLabel⟩ := Finset.mem_image.mp hqData.1
  have hnotVisible : ¬ Visible point := by
    intro hvisible
    change Nat.gcd point.x point.y = 1 at hvisible
    have hlabelOne : commonPrimeLabel point = 1 := by
      simp [commonPrimeLabel, hvisible]
    rw [hlabelOne] at hpointLabel
    omega
  rw [← hpointLabel]
  exact (commonPrimeLabel_spec_of_not_visible hnotVisible).1

/-- On the recruited half of an actual exact-rank terminal history, every
fixed relative residue record receives the literal paid half-rank CRT
charge. -/
theorem ExactRankTerminalHistory.recruited_phase_density_le
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root)
    (period : Nat) (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hrecruited : K ≤ 2 * H.labels.length)
    (hperiod : (∏ q ∈ H.labels.toFinset, q) ∣ period) :
    ((translationPhaseCell period H.labels.toFinset
          residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      (((((K + 1) / 2).factorial : NNReal))⁻¹) ^ 2 := by
  have hprime : ∀ q ∈ H.labels.toFinset, Nat.Prime q := by
    intro q hq
    exact H.history.labels_prime q (List.mem_toFinset.mp hq)
  have hcard : H.labels.toFinset.card = H.labels.length :=
    List.toFinset_card_of_nodup H.labels_nodup
  apply translationPhaseCell_density_le_halfRankFactorial_sq
    period K H.labels.toFinset residueX residueY
    hperiodPos hprime H.recruited_large
  · simpa [hcard] using hrecruited
  · exact hperiod

/-- The complementary half of the same exact-rank partition carries the
identical paid CRT reserve once its fixed relative record is retained. -/
theorem ExactRankTerminalHistory.residual_phase_density_le
    {N K : Nat} {root : Nat × Nat}
    (H : ExactRankTerminalHistory N K root)
    (period : Nat) (residueX residueY : Nat → Nat)
    (hperiodPos : 0 < period)
    (hresidual : K ≤ 2 * H.residualLabels.card)
    (hperiod : (∏ q ∈ H.residualLabels, q) ∣ period) :
    ((translationPhaseCell period H.residualLabels
          residueX residueY).card : NNReal) /
        (period : NNReal) ^ 2 ≤
      (((((K + 1) / 2).factorial : NNReal))⁻¹) ^ 2 := by
  exact translationPhaseCell_density_le_halfRankFactorial_sq
    period K H.residualLabels residueX residueY
    hperiodPos H.residual_prime H.residual_large hresidual hperiod

end Erdos1212Kernel
