import Erdos1212Kernel.VaughanPrimorialLower
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 800000

/-- The logarithmic nth-prime bound used in the paper's support-column
estimate.  It is derived from the already kernel-checked eventual lower bound
`theta(x) ≥ x/2`, rather than inserted as a literature premise. -/
theorem eventually_nthPrime_le_ceil_sixteen_mul_log :
    ∀ᶠ n : ℕ in atTop,
      Nat.nth Nat.Prime n ≤
        Nat.ceil (16 * ((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)) := by
  obtain ⟨Ntheta, htheta⟩ := Filter.eventually_atTop.1 eventually_chebyshevTheta_ge_half
  filter_upwards [eventually_ge_atTop (max 16 Ntheta)] with n hn
  let m : ℕ := n + 1
  let A : ℝ := 16 * (m : ℝ) * Real.log (m : ℝ)
  let x : ℕ := Nat.ceil A
  have hm17 : 17 ≤ m := by dsimp [m]; omega
  have hmPos : 0 < m := by omega
  have hmRPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlogmPos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmOne : 1 ≤ Real.log (m : ℝ) := by
    apply (Real.le_log_iff_exp_le hmRPos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ m by omega))
  have hAZero : 0 ≤ A := by dsimp [A]; positivity
  have hAx : A ≤ (x : ℝ) := by
    dsimp [x]
    exact Nat.le_ceil A
  have hxUpper : (x : ℝ) ≤ A + 1 := by
    dsimp [x]
    exact (Nat.ceil_lt_add_one hAZero).le
  have hlogmLeM : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hmRPos
    linarith
  have hxSquare : (x : ℝ) ≤ 17 * (m : ℝ) ^ 2 := by
    calc
      (x : ℝ) ≤ A + 1 := hxUpper
      _ ≤ 16 * (m : ℝ) * (m : ℝ) + 1 := by
        dsimp [A]
        nlinarith
      _ ≤ 17 * (m : ℝ) ^ 2 := by nlinarith
  have hmLeXReal : (m : ℝ) ≤ x := by
    have hmLeA : (m : ℝ) ≤ A := by
      dsimp [A]
      nlinarith
    exact hmLeA.trans hAx
  have hmLeX : m ≤ x := by exact_mod_cast hmLeXReal
  have hNthetaX : Ntheta ≤ x := by
    have hNthetaN : Ntheta ≤ n := (le_max_right 16 Ntheta).trans hn
    omega
  have hxPos : (0 : ℝ) < x := by exact_mod_cast (hmPos.trans_le hmLeX)
  have hlog17Le : Real.log (17 : ℝ) ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hm17)
  have hlogSquare : Real.log (17 * (m : ℝ) ^ 2) =
      Real.log 17 + 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (by norm_num : (17 : ℝ) ≠ 0)
      (pow_ne_zero 2 hmRPos.ne'), Real.log_pow]
    norm_num
  have hlogX : Real.log (x : ℝ) ≤ 3 * Real.log (m : ℝ) := by
    have hmono := Real.log_le_log hxPos hxSquare
    rw [hlogSquare] at hmono
    linarith
  have hthetaLower := htheta x hNthetaX
  have hthetaUpper := Chebyshev.theta_le_pi_mul_log x
  have hprimeCount : m ≤ Nat.primeCounting x := by
    by_contra hnot
    have hpiLt : Nat.primeCounting x < m := Nat.lt_of_not_ge hnot
    have hpiLtR : (Nat.primeCounting x : ℝ) < (m : ℝ) := by
      exact_mod_cast hpiLt
    have hlogXNonneg : 0 ≤ Real.log (x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x from (show 1 ≤ m by omega).trans hmLeX))
    have hupper1 : (Nat.primeCounting x : ℝ) * Real.log (x : ℝ) ≤
        (Nat.primeCounting x : ℝ) * (3 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogX (by positivity)
    have hupper2 : (Nat.primeCounting x : ℝ) * (3 * Real.log (m : ℝ)) <
        (m : ℝ) * (3 * Real.log (m : ℝ)) :=
      mul_lt_mul_of_pos_right hpiLtR (by positivity)
    have hthetaStrict : Chebyshev.theta (x : ℝ) <
        3 * (m : ℝ) * Real.log (m : ℝ) := by
      calc
        _ ≤ (Nat.primeCounting x : ℝ) * Real.log (x : ℝ) := hthetaUpper
        _ ≤ (Nat.primeCounting x : ℝ) * (3 * Real.log (m : ℝ)) := hupper1
        _ < (m : ℝ) * (3 * Real.log (m : ℝ)) := hupper2
        _ = 3 * (m : ℝ) * Real.log (m : ℝ) := by ring
    have hAhalf : 8 * (m : ℝ) * Real.log (m : ℝ) ≤ (x : ℝ) / 2 := by
      dsimp [A] at hAx
      linarith
    have hcontr : 8 * (m : ℝ) * Real.log (m : ℝ) <
        3 * (m : ℝ) * Real.log (m : ℝ) :=
      (hAhalf.trans hthetaLower).trans_lt hthetaStrict
    nlinarith
  have hcount : n < Nat.count Nat.Prime (x + 1) := by
    change n < Nat.primeCounting x
    dsimp [m] at hprimeCount
    omega
  have hnth := Nat.nth_lt_of_lt_count hcount
  dsimp [x, A, m] at hnth ⊢
  omega

/-- A global constant form, obtained by absorbing the finitely many indices
before the eventual logarithmic estimate. -/
theorem exists_nthPrime_le_const_mul_succ_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.nth Nat.Prime n : ℝ) ≤
        C * (n + 1 : ℕ) * Real.log (n + 2 : ℕ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    eventually_nthPrime_le_ceil_sixteen_mul_log
  let logTwo : ℝ := Real.log 2
  let Cbig : ℝ := 16 + 1 / logTwo
  let Csmall : ℝ := (Nat.nth Nat.Prime N₀ : ℝ) / logTwo
  let C : ℝ := max Cbig Csmall
  have hlogTwo : 0 < logTwo := by
    dsimp [logTwo]
    exact Real.log_pos (by norm_num)
  have hCbig : 0 < Cbig := by dsimp [Cbig]; positivity
  have hC : 0 < C := hCbig.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n
  let base : ℝ := (n + 1 : ℕ) * Real.log (n + 2 : ℕ)
  have hlogMono : logTwo ≤ Real.log (n + 2 : ℕ) := by
    dsimp [logTwo]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 2 by omega))
  have hlogNonneg : 0 ≤ Real.log (n + 2 : ℕ) := hlogTwo.le.trans hlogMono
  have hbase : logTwo ≤ base := by
    dsimp [base]
    have hnOne : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
    nlinarith
  have hbaseNonneg : 0 ≤ base := hlogTwo.le.trans hbase
  by_cases hn : N₀ ≤ n
  · have hnth := hN₀ n hn
    let A : ℝ := 16 * ((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)
    have hAZero : 0 ≤ A := by
      dsimp [A]
      have hlog : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_natCast_nonneg _
      positivity
    have hnthNat : Nat.nth Nat.Prime n ≤ Nat.ceil A := by
      simpa [A] using hnth
    have hnthR : (Nat.nth Nat.Prime n : ℝ) ≤ (Nat.ceil A : ℝ) := by
      exact_mod_cast hnthNat
    have hceil : (Nat.ceil A : ℝ) ≤ A + 1 :=
      (Nat.ceil_lt_add_one hAZero).le
    have hlogSucc : Real.log (n + 1 : ℕ) ≤ Real.log (n + 2 : ℕ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))
    have hA : A ≤ 16 * base := by
      dsimp [A, base]
      nlinarith
    have hone : (1 : ℝ) ≤ (1 / logTwo) * base := by
      calc
        (1 : ℝ) ≤ base / logTwo :=
          (le_div_iff₀ hlogTwo).2 (by simpa only [one_mul] using hbase)
        _ = (1 / logTwo) * base := by field_simp [hlogTwo.ne']
    have hbig : A + 1 ≤ Cbig * base := by
      dsimp [Cbig]
      calc
        A + 1 ≤ 16 * base + (1 / logTwo) * base := add_le_add hA hone
        _ = (16 + 1 / logTwo) * base := by ring
    calc
      (Nat.nth Nat.Prime n : ℝ) ≤ A + 1 := hnthR.trans hceil
      _ ≤ Cbig * base := hbig
      _ ≤ C * base :=
        mul_le_mul_of_nonneg_right (le_max_left Cbig Csmall) hbaseNonneg
      _ = C * (n + 1 : ℕ) * Real.log (n + 2 : ℕ) := by
        dsimp [base]
        ring
  · have hnlt : n < N₀ := Nat.lt_of_not_ge hn
    have hnthMono : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime N₀ :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (Nat.le_of_lt hnlt)
    have hnthMonoR : (Nat.nth Nat.Prime n : ℝ) ≤
        (Nat.nth Nat.Prime N₀ : ℝ) := by exact_mod_cast hnthMono
    have hsmall : (Nat.nth Nat.Prime N₀ : ℝ) ≤ Csmall * base := by
      dsimp [Csmall]
      have hscaled := mul_le_mul_of_nonneg_left hbase
        (by positivity : (0 : ℝ) ≤ (Nat.nth Nat.Prime N₀ : ℝ) / logTwo)
      field_simp [hlogTwo.ne'] at hscaled ⊢
      nlinarith
    calc
      (Nat.nth Nat.Prime n : ℝ) ≤ (Nat.nth Nat.Prime N₀ : ℝ) := hnthMonoR
      _ ≤ Csmall * base := hsmall
      _ ≤ C * base :=
        mul_le_mul_of_nonneg_right (le_max_right Cbig Csmall) hbaseNonneg
      _ = C * (n + 1 : ℕ) * Real.log (n + 2 : ℕ) := by
        dsimp [base]
        ring

end

end Erdos1212Kernel
