import LOOConcentration.Frozen.Norms.DatasetNorm
import LOOConcentration.Frozen.Norms.ObservationNorm
import Mathlib.Tactic.Positivity

/-!
# Basic facts about the frozen Euclidean norms

These lemmas show that the coordinate formulas are nonnegative and vanish
exactly at the zero vector. In particular, the quotient in a punctured local
slope has a positive denominator.
-/

set_option autoImplicit false

namespace LOOConcentration

theorem observationNormSq_nonneg {k m : ℕ} (z : Observation k m) :
    0 ≤ observationNormSq z := by
  unfold observationNormSq
  positivity

theorem observationNormSq_eq_zero_iff {k m : ℕ} (z : Observation k m) :
    observationNormSq z = 0 ↔ z = 0 := by
  have h1 : 0 ≤ ∑ i : Fin k, (z.1 i)^2 := by positivity
  have h2 : 0 ≤ ∑ j : Fin m, (z.2 j)^2 := by positivity
  constructor
  · intro h
    have hs : (∑ i : Fin k, (z.1 i)^2) = 0 ∧
        (∑ j : Fin m, (z.2 j)^2) = 0 := by
      rw [observationNormSq, add_eq_zero_iff_of_nonneg h1 h2] at h
      exact h
    ext i
    · have hi := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : Fin k => (z.1 i)^2) (by intros; positivity)).mp hs.1 i (by simp)
      simpa using hi
    · have hi := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun j : Fin m => (z.2 j)^2) (by intros; positivity)).mp hs.2 i (by simp)
      simpa using hi
  · rintro rfl
    simp [observationNormSq]

theorem datasetNormSq_nonneg {k m n : ℕ}
    (D : Dataset (Observation k m) n) : 0 ≤ datasetNormSq D := by
  unfold datasetNormSq
  exact Finset.sum_nonneg (fun i _ => observationNormSq_nonneg (D i))

theorem observationNorm_sq {k m : ℕ} (z : Observation k m) :
    observationNorm z ^ 2 = observationNormSq z := by
  exact Real.sq_sqrt (observationNormSq_nonneg z)

theorem datasetNorm_sq {k m n : ℕ}
    (D : Dataset (Observation k m) n) :
    datasetNorm D ^ 2 = datasetNormSq D := by
  exact Real.sq_sqrt (datasetNormSq_nonneg D)

theorem datasetNormSq_eq_zero_iff {k m n : ℕ}
    (D : Dataset (Observation k m) n) : datasetNormSq D = 0 ↔ D = 0 := by
  constructor
  · intro h
    funext i
    apply (observationNormSq_eq_zero_iff (D i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun j : Fin n => observationNormSq (D j))
      (fun j _ => observationNormSq_nonneg (D j))).mp h i (by simp)
  · rintro rfl
    simp [datasetNormSq, observationNormSq]

theorem observationNorm_pos_of_ne {k m : ℕ} {z : Observation k m}
    (hz : z ≠ 0) : 0 < observationNorm z := by
  unfold observationNorm
  apply Real.sqrt_pos.2
  have h0 := observationNormSq_nonneg z
  have hne : observationNormSq z ≠ 0 :=
    fun h => hz ((observationNormSq_eq_zero_iff z).mp h)
  exact lt_of_le_of_ne h0 hne.symm

theorem datasetNorm_pos_of_ne {k m n : ℕ}
    {D : Dataset (Observation k m) n} (hD : D ≠ 0) :
    0 < datasetNorm D := by
  unfold datasetNorm
  apply Real.sqrt_pos.2
  have h0 := datasetNormSq_nonneg D
  have hne : datasetNormSq D ≠ 0 :=
    fun h => hD ((datasetNormSq_eq_zero_iff D).mp h)
  exact lt_of_le_of_ne h0 hne.symm

theorem observationNorm_sub_pos {k m : ℕ}
    {w z : Observation k m} (h : w ≠ z) :
    0 < observationNorm (w - z) :=
  observationNorm_pos_of_ne (sub_ne_zero.mpr h)

theorem datasetNorm_sub_pos {k m n : ℕ}
    {E D : Dataset (Observation k m) n} (h : E ≠ D) :
    0 < datasetNorm (E - D) :=
  datasetNorm_pos_of_ne (sub_ne_zero.mpr h)

end LOOConcentration
