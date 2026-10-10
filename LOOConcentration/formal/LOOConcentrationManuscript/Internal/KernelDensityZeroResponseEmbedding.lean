import LOOConcentrationManuscript.Internal.ScalarObservationLSITransport
import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The literal KDE embedding x↦(x,0) preserves source second moments and
ordered sample laws and does not increase the native log-Sobolev constant. -/
theorem kde_zeroResponse_moment_law_and_lsi_transport
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x^2) μ) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x),(fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
    (∀ x : ℝ, LOOConcentration.observationNormSq (φ x) = x^2) ∧
      Integrable LOOConcentration.observationNormSq ν ∧
      (∫ z : LOOConcentration.Observation 1 1, LOOConcentration.observationNormSq z ∂ν) =
        (∫ x : ℝ, x^2 ∂μ) ∧
      (∀ r : ℕ,
        (Measure.pi (fun _ : Fin (r+1) => μ)).map
          (fun D : Fin (r+1) → ℝ => fun i => φ (D i)) =
            Measure.pi (fun _ : Fin (r+1) => ν)) ∧
      LOOConcentration.Revision.observationLogSobolevConstant ν ≤
        LOOConcentration.Revision.logSobolevConstant (μ.map scalar) := by
  classical
  intro φ ν scalar
  let e : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) :=
    { toLinearMap :=
        { toFun := fun x => WithLp.toLp 2 (Sum.elim (fun _ : Fin 1 => x) (fun _ : Fin 1 => (0 : ℝ)))
          map_add' := by intro x y; ext q; cases q <;> simp
          map_smul' := by intro a x; ext q; cases q <;> simp }
      norm_map' := by
        intro x
        rw [EuclideanSpace.norm_eq]
        simp [Fintype.sum_sum_type,Real.norm_eq_abs,Real.sqrt_sq_eq_abs] }
  have hφ : φ = LOOConcentration.Revision.observationOfEuclidean ∘ e := rfl
  have hMoment := scalarObservation_moment_product_transport μ hSecond e
  rw [← hφ] at hMoment
  refine ⟨hMoment.1,hMoment.2.1,hMoment.2.2.1,hMoment.2.2.2.1,?_⟩
  exact scalarObservation_logSobolevConstant_le μ false

end LOOConcentration.Manuscript.Internal
