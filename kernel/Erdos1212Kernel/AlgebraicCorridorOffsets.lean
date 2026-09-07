import Erdos1212Kernel.AlgebraicCorridorLocalizedWitness
import Erdos1212Kernel.AlgebraicCorridorScaleProduction
import Mathlib.Data.Int.NatAbs

namespace Erdos1212Kernel

noncomputable section

def corridorCoordNat (p : LatticePoint) : Fin 2 → Nat :=
  Fin.cases p.x (fun _ => p.y)

def corridorOffset (base point : LatticePoint) : Fin 2 → Int :=
  fun k => (corridorCoordNat point k : Int) - corridorCoordNat base k

def corridorRoot (base : LatticePoint) : Fin 2 → Int :=
  fun k => (corridorCoordNat base k : Int)

@[simp] theorem corridorCoordNat_zero (p : LatticePoint) : corridorCoordNat p 0 = p.x := rfl
@[simp] theorem corridorCoordNat_one (p : LatticePoint) : corridorCoordNat p 1 = p.y := rfl

theorem corridorOffset_add_root (base point : LatticePoint) (k : Fin 2) :
    corridorRoot base k + corridorOffset base point k =
      (corridorCoordNat point k : Int) := by
  unfold corridorRoot corridorOffset
  ring

theorem corridorOffset_natAbs_le_of_dist_le {a b B : Nat}
    (hdist : Nat.dist a b ≤ B) :
    Int.natAbs ((a : Int) - (b : Int)) ≤ B := by
  rcases le_total b a with hba | hab
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hba]
    rw [Nat.dist_eq_sub_of_le_right hba] at hdist
    exact hdist
  · have hrewrite : (a : Int) - (b : Int) = -((b : Int) - (a : Int)) := by ring
    rw [hrewrite, Int.natAbs_neg, Int.natAbs_natCast_sub_natCast_of_ge hab]
    rw [Nat.dist_eq_sub_of_le hab] at hdist
    exact hdist

theorem corridorOffset_abs_le_of_dist_le
    {base point : LatticePoint} {B : Nat}
    (hx : Nat.dist point.x base.x ≤ B)
    (hy : Nat.dist point.y base.y ≤ B) :
    ∀ k, |((corridorOffset base point k : Int) : ℝ)| ≤ B := by
  intro k
  fin_cases k
  · have h := corridorOffset_natAbs_le_of_dist_le hx
    have h' : ((point.x : Int) - (base.x : Int)).natAbs ≤ B := by
      exact h
    change |(((point.x : Int) - (base.x : Int) : Int) : ℝ)| ≤ B
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (show
      ((((point.x : Int) - (base.x : Int)).natAbs : ℝ) ≤ B) by exact_mod_cast h')
  · have h := corridorOffset_natAbs_le_of_dist_le hy
    have h' : ((point.y : Int) - (base.y : Int)).natAbs ≤ B := by
      exact h
    change |(((point.y : Int) - (base.y : Int) : Int) : ℝ)| ≤ B
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (show
      ((((point.y : Int) - (base.y : Int)).natAbs : ℝ) ≤ B) by exact_mod_cast h')

theorem corridorRoot_abs_le {base : LatticePoint} {X : Nat}
    (hx : base.x ≤ X) (hy : base.y ≤ X) :
    ∀ k, |(corridorRoot base k : ℝ)| ≤ X := by
  intro k
  fin_cases k <;> simp [corridorRoot, corridorCoordNat]
  · exact_mod_cast hx
  · exact_mod_cast hy

theorem corridorOffset_prime_divisibility
    {base point : LatticePoint} {q : Nat}
    (hqx : q ∣ point.x) (hqy : q ∣ point.y) :
    ∀ k, (q : Int) ∣ corridorRoot base k + corridorOffset base point k := by
  intro k
  rw [corridorOffset_add_root]
  fin_cases k
  · exact_mod_cast hqx
  · exact_mod_cast hqy

/-! The exact localized-to-algebraic consumer. The only scale fact it uses is
the already proved `eventually_algebraic_point` body at the chosen N. -/
theorem corridor_localized_rows_algebraic_point
    {N : Real} {base : LatticePoint}
    (hN : 0 < N)
    (hscale :
      ∀ (root : Fin 2 → Int)
        (point : Fin (CorridorScale.rows N) → Fin 2 → Int)
        (q : Fin (CorridorScale.rows N) → Nat),
        (∀ i k, |(point i k : Real)| ≤ CorridorScale.radius N) →
        (∀ k, |(root k : Real)| ≤ 4 * N) →
        (∀ i, (q i).Prime) → Function.Injective q →
        (∀ i, CorridorScale.z N < (q i : Real)) →
        (∀ i k, (q i : Int) ∣ root k + point i k) →
        ∃ F : MvPolynomial (Fin 2) Int,
          F ≠ 0 ∧ F.totalDegree ≤ CorridorScale.degree N ∧
          MvPolynomial.eval root F = 0 ∧
          corridorPolynomialHeight F ≤ CorridorScale.height N)
    (pointNat : Fin (CorridorScale.rows N) → LatticePoint)
    (hspan : ∀ i, Nat.dist (pointNat i).x base.x ≤ CorridorScale.radius N ∧
      Nat.dist (pointNat i).y base.y ≤ CorridorScale.radius N)
    (hq : Fin (CorridorScale.rows N) → Nat)
    (hqprime : ∀ i, (hq i).Prime) (hqinj : Function.Injective hq)
    (hqlarge : ∀ i, CorridorScale.z N < (hq i : Real))
    (hqdiv : ∀ i, (hq i) ∣ (pointNat i).x ∧ (hq i) ∣ (pointNat i).y)
    (hbase : base.x ≤ Nat.floor (4 * N) ∧ base.y ≤ Nat.floor (4 * N)) :
    ∃ F : MvPolynomial (Fin 2) Int,
      F ≠ 0 ∧ F.totalDegree ≤ CorridorScale.degree N ∧
      MvPolynomial.eval (corridorRoot base) F = 0 ∧
      corridorPolynomialHeight F ≤ CorridorScale.height N := by
  let pointInt : Fin (CorridorScale.rows N) → Fin 2 → Int :=
    fun i k => corridorOffset base (pointNat i) k
  have hpointInt : ∀ i k, |(pointInt i k : Real)| ≤ CorridorScale.radius N := by
    intro i k
    exact corridorOffset_abs_le_of_dist_le (hspan i).1 (hspan i).2 k
  have hrootInt : ∀ k, |(corridorRoot base k : Real)| ≤ 4 * N := by
    intro k
    have hx : base.x ≤ Nat.floor (4 * N) := hbase.1
    have hy : base.y ≤ Nat.floor (4 * N) := hbase.2
    have hfloor : (Nat.floor (4 * N) : Real) ≤ 4 * N := Nat.floor_le (by positivity)
    exact (corridorRoot_abs_le (X := Nat.floor (4 * N)) hx hy k).trans hfloor
  have hdivInt : ∀ i k, (hq i : Int) ∣ corridorRoot base k + pointInt i k := by
    intro i k
    exact corridorOffset_prime_divisibility (hqdiv i).1 (hqdiv i).2 k
  obtain ⟨F, hF, hd, hz, hh⟩ := hscale (corridorRoot base) pointInt hq
    hpointInt hrootInt hqprime hqinj hqlarge hdivInt
  exact ⟨F, hF, hd, hz, hh⟩

end

end Erdos1212Kernel
