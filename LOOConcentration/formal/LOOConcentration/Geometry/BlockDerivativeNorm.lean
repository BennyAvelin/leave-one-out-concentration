import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import LOOConcentration.Geometry.NormTransport

/-!
# Collective derivative energy in Euclidean dataset blocks

The coordinate inclusion of one observation block is a linear isometry.
Applying the orthonormal-basis dual norm formula blockwise and reindexing the
finite sums identifies the sum of squared block derivative norms with the
squared norm of the full derivative.
-/

set_option autoImplicit false

namespace LOOConcentration

private def blockCoordinates {k m n : ℕ}
    (i : Fin (n + 1))
    (v : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1))) :
    EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
  WithLp.toLp (2 : ENNReal) (fun q => if q.1 = i then v q.2 else 0)

/-- Include one observation vector as a single block in a flattened dataset. -/
noncomputable def datasetBlockInclusion {k m n : ℕ} (i : Fin (n + 1)) :
    EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) where
  toLinearMap :=
    { toFun := blockCoordinates i
      map_add' := by
        intro v w
        ext q
        rcases q with ⟨j, a⟩
        by_cases hji : j = i <;> simp [blockCoordinates, hji]
      map_smul' := by
        intro c v
        ext q
        rcases q with ⟨j, a⟩
        by_cases hji : j = i <;> simp [blockCoordinates, hji] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [blockCoordinates, Fintype.sum_prod_type]

/-- The block inclusion sends a coordinate basis vector to the corresponding
full-dataset coordinate basis vector. -/
theorem datasetBlockInclusion_single {k m n : ℕ} (i : Fin (n + 1))
    (a : ObservationCoordinate (k + 1) (m + 1)) :
    datasetBlockInclusion (k := k) (m := m) (n := n) i
        (EuclideanSpace.single a (1 : ℝ)) =
      EuclideanSpace.single (i, a) (1 : ℝ) := by
  ext q
  rcases q with ⟨j, b⟩
  by_cases hji : j = i
  · subst j
    simp [datasetBlockInclusion, blockCoordinates]
  · simp [datasetBlockInclusion, blockCoordinates, hji]

/-- The squared operator norms of the observation-block restrictions of a
scalar functional sum to its full squared operator norm. -/
theorem sum_datasetBlock_composition_norm_sq {k m n : ℕ}
    (L : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) →L[ℝ] ℝ) :
    (∑ i : Fin (n + 1),
      ‖L.comp (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ ^ 2) =
      ‖L‖ ^ 2 := by
  let I := ObservationCoordinate (k + 1) (m + 1)
  let E := EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))
  have hblock (i : Fin (n + 1)) :
      ‖L.comp (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ ^ 2 =
        ∑ a : ObservationCoordinate (k + 1) (m + 1),
          (L (datasetBlockInclusion (k := k) (m := m) (n := n) i
            (EuclideanSpace.basisFun
              (ObservationCoordinate (k + 1) (m + 1)) ℝ a))) ^ 2 := by
    simpa only [OrthonormalBasis.norm_dual, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using
      (OrthonormalBasis.norm_dual
        (EuclideanSpace.basisFun (ObservationCoordinate (k + 1) (m + 1)) ℝ)
        (L.comp (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap))
  calc
    (∑ i : Fin (n + 1),
      ‖L.comp (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ ^ 2)
        = ∑ i : Fin (n + 1),
          ∑ a : ObservationCoordinate (k + 1) (m + 1),
            (L (datasetBlockInclusion (k := k) (m := m) (n := n) i
              (EuclideanSpace.basisFun
                (ObservationCoordinate (k + 1) (m + 1)) ℝ a))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hblock i
    _ = ∑ i : Fin (n + 1),
          ∑ a : ObservationCoordinate (k + 1) (m + 1),
            (L (EuclideanSpace.basisFun
              (DatasetCoordinate (k + 1) (m + 1) (n + 1)) ℝ (i, a))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro a ha
          rw [EuclideanSpace.basisFun_apply, datasetBlockInclusion_single,
            EuclideanSpace.basisFun_apply]
    _ = ∑ q : DatasetCoordinate (k + 1) (m + 1) (n + 1),
          (L (EuclideanSpace.basisFun
            (DatasetCoordinate (k + 1) (m + 1) (n + 1)) ℝ q)) ^ 2 := by
          rw [← Fintype.sum_prod_type']
    _ = ‖L‖ ^ 2 := by
          symm
          exact OrthonormalBasis.norm_dual
            (EuclideanSpace.basisFun
              (DatasetCoordinate (k + 1) (m + 1) (n + 1)) ℝ) L

/-- The collective squared-gradient identity for the Fréchet derivative of a
scalar function on the full flattened dataset space. -/
theorem sum_datasetBlock_fderiv_norm_sq {k m n : ℕ}
    (F : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (x : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1))) :
    (∑ i : Fin (n + 1),
      ‖(fderiv ℝ F x).comp
        (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ ^ 2) =
      ‖fderiv ℝ F x‖ ^ 2 :=
  sum_datasetBlock_composition_norm_sq (fderiv ℝ F x)

end LOOConcentration
