import LOOConcentrationManuscript.Internal.RidgeSlopeBound
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedLinearEstimator
import LOOConcentrationManuscript.Frozen.Definitions.CoordinateClip
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

private noncomputable abbrev addMean {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ i, X i) / (N : ℝ)

private noncomputable abbrev addCov {N : ℕ} (X U : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - addMean X) * (U i - addMean U)) / (N : ℝ)

private theorem addCov_raw {N : ℕ} (hN : 0 < N) (X U : Fin N → ℝ) :
    addCov X U = (∑ i, X i * U i) / (N : ℝ) - addMean X * addMean U := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he : (∑ i, (X i - addMean X) * (U i - addMean U)) =
      (∑ i, X i * U i) - (∑ i, X i) * addMean U -
        addMean X * (∑ i, U i) + (N : ℝ) * addMean X * addMean U := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  dsimp only [addCov]
  rw [he]
  dsimp [addMean]
  field_simp [hn]
  ring

private theorem addMean_snoc {N : ℕ} (X : Fin N → ℝ) (x : ℝ) :
    addMean (Fin.snoc X x) = ((N : ℝ) * addMean X + x) / (N + 1 : ℝ) := by
  dsimp [addMean]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hN : N = 0
  · subst N
    simp
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp [hn]

private theorem addCov_snoc {N : ℕ} (hN : 0 < N) (X U : Fin N → ℝ) (x u : ℝ) :
    addCov (Fin.snoc X x) (Fin.snoc U u) =
      (N : ℝ) / (N + 1 : ℝ) * addCov X U +
        (N : ℝ) / (N + 1 : ℝ) ^ 2 * (x - addMean X) * (u - addMean U) := by
  rw [addCov_raw (by omega), addCov_raw hN, addMean_snoc, addMean_snoc]
  have hsum : (∑ i, Fin.snoc X x i * Fin.snoc U u i) =
      (∑ i, X i * U i) + x * u := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hsum]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hn1 : (N + 1 : ℝ) ≠ 0 := by positivity
  dsimp [addMean]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hn, hn1]
  ring

/-- The literal clipped covariance and feature variance obey the same add-one
updates, with the raw response clipped only in the covariance. -/
theorem ridge_actual_add_one_empirical_updates (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (z : LOOConcentration.Observation 1 1) (b : {t : ℝ // 0 < t}) :
    let N : ℝ := (r + 1 : ℝ)
    let X := fun i : Fin (r + 1) => (D i).1 0
    let U := fun i : Fin (r + 1) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ ((D i).2 0)
    let a := (∑ i, X i) / N
    let c := (∑ i, U i) / N
    let v := (∑ i, (X i - a) ^ 2) / N
    let s := (∑ i, (X i - a) * (U i - c)) / N
    let Xp := fun i : Fin (r + 2) => ((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).1 0
    let Up := fun i : Fin (r + 2) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).2 0)
    let ap := (∑ i, Xp i) / (N + 1)
    let cp := (∑ i, Up i) / (N + 1)
    let vp := (∑ i, (Xp i - ap) ^ 2) / (N + 1)
    let sp := (∑ i, (Xp i - ap) * (Up i - cp)) / (N + 1)
    let d := z.1 0 - a
    let e := LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (z.2 0) - c
    sp = N / (N + 1) * s + N / (N + 1) ^ 2 * d * e ∧
      vp = N / (N + 1) * v + N / (N + 1) ^ 2 * d ^ 2 := by
  intro N X U a c v s Xp Up ap cp vp sp d e
  have hX : Xp = Fin.snoc X (z.1 0) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Xp]
    · simp [Xp, X]
  have hU : Up = Fin.snoc U (LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (z.2 0)) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Up]
    · simp [Up, U]
  have hCov := addCov_snoc (by omega : 0 < r + 1) X U (z.1 0) (LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (z.2 0))
  have hVar := addCov_snoc (by omega : 0 < r + 1) X X (z.1 0) (z.1 0)
  constructor
  · dsimp [sp, s, ap, cp, d, e, a, c, N]
    rw [hX, hU]
    simpa only [addCov, addMean, Nat.cast_add, Nat.cast_one] using hCov
  · dsimp [vp, v, ap, d, a, N]
    rw [hX]
    simpa only [addCov, addMean, Nat.cast_add, Nat.cast_one, pow_two, mul_assoc] using hVar

end LOOConcentration.Manuscript.Internal
