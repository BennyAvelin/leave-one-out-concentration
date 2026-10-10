import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin
import LOOConcentration.Frozen.Foundations.DeleteAt
import LOOConcentration.Frozen.Norms.ObservationNorm
import LOOConcentration.Frozen.Norms.DatasetNorm
import LOOConcentration.Geometry.EuclideanNormFacts

/-!
# Euclidean norm transport

The frozen norms are the Euclidean norms on the corresponding flattened
coordinate spaces. These conversions let later estimates use the norm and
inner-product inequalities of finite-dimensional Euclidean space without
changing the source normalization.
-/

set_option autoImplicit false

namespace LOOConcentration

/-! The coordinate index sets used to flatten observations and datasets. -/

abbrev ObservationCoordinate (k m : ℕ) := Fin k ⊕ Fin m

abbrev DatasetCoordinate (k m n : ℕ) := Fin n × ObservationCoordinate k m

/-- The flattened Euclidean vector of an observation. -/
def observationToEuclidean {k m : ℕ} (z : Observation k m) :
    EuclideanSpace ℝ (ObservationCoordinate k m) :=
  WithLp.toLp 2 (Sum.elim z.1 z.2)

/-- The flattened Euclidean vector of all coordinates in a dataset. -/
def datasetToEuclidean {k m n : ℕ} (D : Dataset (Observation k m) n) :
    EuclideanSpace ℝ (DatasetCoordinate k m n) :=
  WithLp.toLp 2 (fun q => Sum.elim (D q.1).1 (D q.1).2 q.2)

/-- The coordinate inner product of two observations. -/
def observationDot {k m : ℕ} (z w : Observation k m) : ℝ :=
  (∑ i : Fin k, z.1 i * w.1 i) + ∑ j : Fin m, z.2 j * w.2 j

/-- The coordinate inner product of two datasets. -/
def datasetDot {k m n : ℕ} (D E : Dataset (Observation k m) n) : ℝ :=
  ∑ i : Fin n, observationDot (D i) (E i)

/-- The frozen observation norm is exactly the norm on its flattened Euclidean space. -/
theorem observationNorm_eq_euclidean {k m : ℕ} (z : Observation k m) :
    observationNorm z = ‖observationToEuclidean z‖ := by
  unfold observationNorm
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [observationNormSq, observationToEuclidean, Fintype.sum_sum_type,
    Real.norm_eq_abs, sq_abs]

/-- The frozen dataset norm is exactly the norm on its flattened Euclidean space. -/
theorem datasetNorm_eq_euclidean {k m n : ℕ} (D : Dataset (Observation k m) n) :
    datasetNorm D = ‖datasetToEuclidean D‖ := by
  unfold datasetNorm
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [datasetNormSq, observationNormSq, datasetToEuclidean,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs]

theorem observationToEuclidean_add {k m : ℕ} (z w : Observation k m) :
    observationToEuclidean (z + w) = observationToEuclidean z + observationToEuclidean w := by
  ext q
  cases q <;> simp [observationToEuclidean]

theorem datasetToEuclidean_add {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    datasetToEuclidean (D + E) = datasetToEuclidean D + datasetToEuclidean E := by
  apply PiLp.ext
  intro q
  rcases q with ⟨i, c⟩
  cases c <;> simp [datasetToEuclidean]

/-- Triangle inequality for the frozen observation norm. -/
theorem observationNorm_add_le {k m : ℕ} (z w : Observation k m) :
    observationNorm (z + w) ≤ observationNorm z + observationNorm w := by
  calc
    observationNorm (z + w) = ‖observationToEuclidean (z + w)‖ :=
      observationNorm_eq_euclidean _
    _ = ‖observationToEuclidean z + observationToEuclidean w‖ := by
      rw [observationToEuclidean_add]
    _ ≤ ‖observationToEuclidean z‖ + ‖observationToEuclidean w‖ := norm_add_le _ _
    _ = observationNorm z + observationNorm w := by
      rw [← observationNorm_eq_euclidean, ← observationNorm_eq_euclidean]

/-- Triangle inequality for the frozen dataset norm. -/
theorem datasetNorm_add_le {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    datasetNorm (D + E) ≤ datasetNorm D + datasetNorm E := by
  calc
    datasetNorm (D + E) = ‖datasetToEuclidean (D + E)‖ := datasetNorm_eq_euclidean _
    _ = ‖datasetToEuclidean D + datasetToEuclidean E‖ := by rw [datasetToEuclidean_add]
    _ ≤ ‖datasetToEuclidean D‖ + ‖datasetToEuclidean E‖ := norm_add_le _ _
    _ = datasetNorm D + datasetNorm E := by
      rw [← datasetNorm_eq_euclidean, ← datasetNorm_eq_euclidean]

theorem observationToEuclidean_inner {k m : ℕ} (z w : Observation k m) :
    inner ℝ (observationToEuclidean z) (observationToEuclidean w) = observationDot z w := by
  rw [PiLp.inner_apply]
  simp [observationDot, observationToEuclidean, Fintype.sum_sum_type, mul_comm]

theorem datasetToEuclidean_inner {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    inner ℝ (datasetToEuclidean D) (datasetToEuclidean E) = datasetDot D E := by
  rw [PiLp.inner_apply]
  simp [datasetDot, observationDot, datasetToEuclidean, Fintype.sum_prod_type,
    Fintype.sum_sum_type, mul_comm]

/-- Cauchy–Schwarz for the frozen observation coordinate inner product. -/
theorem abs_observationDot_le {k m : ℕ} (z w : Observation k m) :
    |observationDot z w| ≤ observationNorm z * observationNorm w := by
  rw [← observationToEuclidean_inner, observationNorm_eq_euclidean,
    observationNorm_eq_euclidean]
  exact abs_real_inner_le_norm _ _

/-- Cauchy–Schwarz for the frozen dataset coordinate inner product. -/
theorem abs_datasetDot_le {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    |datasetDot D E| ≤ datasetNorm D * datasetNorm E := by
  rw [← datasetToEuclidean_inner, datasetNorm_eq_euclidean, datasetNorm_eq_euclidean]
  exact abs_real_inner_le_norm _ _

/-- Deleting one observation cannot increase the frozen unnormalized norm. -/
theorem datasetNorm_deleteAt_le {k m n : ℕ}
    (D : Dataset (Observation k m) (n + 1)) (i : Fin (n + 1)) :
    datasetNorm (deleteAt D i) ≤ datasetNorm D := by
  unfold datasetNorm
  apply Real.sqrt_le_sqrt
  change (∑ j : Fin n, observationNormSq (D (i.succAbove j))) ≤
    ∑ j : Fin (n + 1), observationNormSq (D j)
  rw [Fin.sum_univ_succAbove (fun j : Fin (n + 1) => observationNormSq (D j)) i]
  exact le_add_of_nonneg_left (observationNormSq_nonneg (D i))

end LOOConcentration
