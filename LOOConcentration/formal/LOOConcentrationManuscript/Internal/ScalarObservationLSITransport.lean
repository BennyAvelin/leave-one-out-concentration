import LOOConcentrationManuscript.Internal.IsometryLSITransport
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- The two literal zero-coordinate embeddings satisfy the same native LSI bound. -/
theorem scalarObservation_logSobolevConstant_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (response : Bool) :
    let φ := fun x : ℝ => (if response then
      ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x)) else
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => 0)) : LOOConcentration.Observation 1 1)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map
      (by
        have h : Continuous φ := by
          cases response
          · change Continuous (fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))
            fun_prop
          · change Continuous (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
            fun_prop
        exact h.measurable.aemeasurable)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map
      (by fun_prop)
    LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ) ≤
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) := by
  classical
  intro φ scalar
  have hφ : Measurable φ := by
    cases response
    · change Measurable (fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))
      fun_prop
    · change Measurable (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
      fun_prop
  have hs : Measurable scalar := by fun_prop
  let : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map hφ.aemeasurable
  let : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map hs.aemeasurable
  let e : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) :=
    { toLinearMap :=
        { toFun := fun x => WithLp.toLp 2
            (Sum.elim (fun _ : Fin 1 => if response then 0 else x 0)
              (fun _ : Fin 1 => if response then x 0 else 0))
          map_add' := by
            intro x y
            ext q
            cases q <;> cases response <;> simp
          map_smul' := by
            intro a x
            ext q
            cases q <;> cases response <;> simp }
      norm_map' := by
        intro x
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        cases response <;> simp [Fintype.sum_sum_type] }
  have hcomp : LOOConcentration.observationToEuclidean ∘ φ = e ∘ scalar := by
    funext x
    ext q
    cases q <;> cases response <;> rfl
  have hlaw : (μ.map φ).map LOOConcentration.observationToEuclidean =
      (μ.map scalar).map e := by
    rw [Measure.map_map LOOConcentration.Revision.measurable_observationToEuclidean hφ,
      Measure.map_map e.continuous.measurable hs, hcomp]
  have h := logSobolevConstant_map_linearIsometry_le (μ.map scalar) e
  unfold LOOConcentration.Revision.observationLogSobolevConstant
  simpa only [hlaw] using h

end LOOConcentration.Manuscript.Internal
