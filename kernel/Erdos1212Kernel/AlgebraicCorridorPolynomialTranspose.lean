import Erdos1212Kernel.AlgebraicCorridorTranspose

namespace Erdos1212Kernel
noncomputable section

def corridorSwapIndex : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
def corridorTransposePolynomial (F : MvPolynomial (Fin 2) ℤ) :=
  MvPolynomial.rename corridorSwapIndex F

theorem corridorTransposePolynomial_twice (F : MvPolynomial (Fin 2) ℤ) :
    corridorTransposePolynomial (corridorTransposePolynomial F) = F := by
  unfold corridorTransposePolynomial
  rw [MvPolynomial.rename_rename]
  have h : (corridorSwapIndex ∘ corridorSwapIndex) = id := by
    funext i
    fin_cases i <;> simp [corridorSwapIndex]
  rw [h, MvPolynomial.rename_id_apply]

theorem corridorTransposePolynomial_ne_zero {F : MvPolynomial (Fin 2) ℤ}
    (hF : F ≠ 0) : corridorTransposePolynomial F ≠ 0 := by
  intro h
  have hh := congrArg corridorTransposePolynomial h
  rw [corridorTransposePolynomial_twice] at hh
  exact hF (by simpa [corridorTransposePolynomial] using hh)

theorem corridorTransposePolynomial_totalDegree (F : MvPolynomial (Fin 2) ℤ) :
    (corridorTransposePolynomial F).totalDegree = F.totalDegree := by
  apply le_antisymm (MvPolynomial.totalDegree_rename_le _ _)
  have h := MvPolynomial.totalDegree_rename_le corridorSwapIndex
    (corridorTransposePolynomial F)
  change (corridorTransposePolynomial (corridorTransposePolynomial F)).totalDegree ≤ _ at h
  rwa [corridorTransposePolynomial_twice] at h

theorem corridorTransposePolynomial_eval (F : MvPolynomial (Fin 2) ℤ) (p : LatticePoint) :
    MvPolynomial.eval (corridorRoot p) (corridorTransposePolynomial F) =
      MvPolynomial.eval (corridorRoot (corridorTranspose p)) F := by
  unfold corridorTransposePolynomial
  rw [MvPolynomial.eval_rename]
  have heq : corridorRoot p ∘ corridorSwapIndex = corridorRoot (corridorTranspose p) := by
    funext i
    fin_cases i <;> simp [corridorSwapIndex, corridorRoot, corridorTranspose,
      corridorCoordNat, Function.comp_def] <;> rfl
  rw [heq]

theorem corridorTransposePolynomial_height_le (F : MvPolynomial (Fin 2) ℤ) :
    corridorPolynomialHeight (corridorTransposePolynomial F) ≤ corridorPolynomialHeight F := by
  unfold corridorPolynomialHeight
  apply Finset.sup_le
  intro e he
  have hs := MvPolynomial.support_rename_of_injective
    (p := F) corridorSwapIndex.injective
  change e ∈ (MvPolynomial.rename corridorSwapIndex F).support at he
  rw [hs, Finset.mem_image] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [corridorTransposePolynomial, MvPolynomial.coeff_rename_mapDomain
    corridorSwapIndex corridorSwapIndex.injective]
  exact Finset.le_sup (f := fun e => (MvPolynomial.coeff e F).natAbs) hd

theorem corridorTransposePolynomial_height (F : MvPolynomial (Fin 2) ℤ) :
    corridorPolynomialHeight (corridorTransposePolynomial F) = corridorPolynomialHeight F := by
  apply le_antisymm (corridorTransposePolynomial_height_le F)
  have h := corridorTransposePolynomial_height_le (corridorTransposePolynomial F)
  rwa [corridorTransposePolynomial_twice] at h

theorem CorridorScale.eventually_safe_vertical_crossing :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ (α : ℝ) (R : CorridorRectangle),
      DirectionAvoidance N α →
      2 < R.bottom → 1 < R.left → R.left < R.right →
      Nat.floor (N / 2) ≤ R.left → R.right ≤ Nat.floor (4 * N) →
      N ^ (9 / 10 : ℝ) ≤ ((R.right - R.left + 1 : ℕ) : ℝ) →
      (∀ p, R.Contains p → directionCorridor N α p) →
      R.SafeVerticalCrossing := by
  filter_upwards [eventually_bad_vertical_crossing_algebraic_point,
    Filter.eventually_ge_atTop (8 : ℝ)] with N hcross hN
  intro α R havoid hb hl hwidth hleft hright hsize hcorr
  by_contra hno
  have hn : ¬R.transpose.SafeHorizontalCrossing :=
    fun h => hno (R.safeVertical_of_transpose_horizontal h)
  obtain ⟨a, b, ha, hbe, w, hw⟩ :=
    R.transpose.bad_vertical_crossing_of_no_safe_horizontal hb hl hwidth hn
  have hcor : ∀ p ∈ w.support, directionCorridor N α (corridorTranspose p) := by
    intro p hp
    exact hcorr _ ((R.transpose_contains (corridorTranspose p)).mp
      (by simpa using (hw p hp).1))
  have hcoords : ∀ p ∈ w.support, 1 < p.x ∧ 1 < p.y := by
    intro p hp
    have h := hcor p hp
    have hx : (1 : ℝ) < p.x := by
      have hh := h.2.2.1
      change N / 2 ≤ (p.x : ℝ) at hh
      linarith
    have hy : (1 : ℝ) < p.y := by
      have hh := h.1
      change N / 2 ≤ (p.y : ℝ) at hh
      linarith
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩
  have hxl : ∀ p ∈ w.support, Nat.floor (N / 2) ≤ p.x := by
    intro p hp
    have h := (hcor p hp).2.2.1
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ N / 2)).trans h
  have hbox : ∀ p ∈ w.support,
      p.x ≤ Nat.floor (4 * N) ∧ p.y ≤ Nat.floor (4 * N) := by
    intro p hp
    have h := hcor p hp
    exact ⟨Nat.le_floor h.2.2.2.1, Nat.le_floor h.2.1⟩
  obtain ⟨base, hbase, F, hF, hd, hz, hh⟩ :=
    hcross (lower := R.left) (T := R.right - R.left + 1) w
      hleft (by omega) hsize (by exact ha.le) (by dsimp [CorridorRectangle.transpose] at hbe; omega)
      hcoords hxl (fun p hp => (hw p hp).2) hbox
  have hz' : MvPolynomial.eval (corridorRoot (corridorTranspose base))
      (corridorTransposePolynomial F) = 0 := by
    rw [corridorTransposePolynomial_eval, corridorTranspose_twice]
    exact hz
  have hroot : corridorRoot (corridorTranspose base) =
      ![((corridorTranspose base).x : ℤ), ((corridorTranspose base).y : ℤ)] := by
    funext i
    fin_cases i <;> rfl
  apply havoid _ (hcor base hbase) _ (corridorTransposePolynomial_ne_zero hF)
    (by rwa [corridorTransposePolynomial_totalDegree])
    (by rwa [corridorTransposePolynomial_height])
  rwa [hroot] at hz'

end
end Erdos1212Kernel
