import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

private def scalarObservationIsometry (response : Bool) :
    ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) where
  toFun x := WithLp.toLp 2 (Sum.elim
    (fun _ : Fin 1 => if response then 0 else x)
    (fun _ : Fin 1 => if response then x else 0))
  map_add' x y := by
    ext q
    cases q <;> cases response <;> simp
  map_smul' a x := by
    ext q
    cases q <;> cases response <;> simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq]
    cases response <;> simp [Fintype.sum_sum_type, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/-- Both literal source embeddings retain the same second moment and the ordered
sample law, also when a distinct fresh test coordinate is appended. -/
theorem scalarObservation_sample_and_fresh_test_transport
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (response : Bool) (n : ℕ) :
    let φ := fun x : ℝ => (if response then
      ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x)) else
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => 0)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    (∀ x : ℝ, LOOConcentration.observationNormSq (φ x) = x ^ 2) ∧
    Integrable LOOConcentration.observationNormSq ν ∧
    ((∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.observationNormSq z ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    ((Measure.pi fun _ : Fin (n + 2) => μ).map
      (fun D : Fin (n + 2) → ℝ => fun i => φ (D i)) =
        Measure.pi fun _ : Fin (n + 2) => ν) ∧
    ((Measure.pi fun _ : Fin (n + 3) => μ).map
      (fun D : Fin (n + 3) → ℝ => fun i => φ (D i)) =
        Measure.pi fun _ : Fin (n + 3) => ν) ∧
    (∀ D : Fin (n + 2) → ℝ,
      (∑ i : Fin (n + 2), LOOConcentration.observationNormSq (φ (D i))) =
        ∑ i : Fin (n + 2), (D i) ^ 2) := by
  classical
  intro φ ν
  have hφ : φ = LOOConcentration.Revision.observationOfEuclidean ∘
      scalarObservationIsometry response := by
    funext x
    cases response <;> rfl
  obtain ⟨hnorm, hinter, hintegral, hlaw, hsum⟩ :=
    scalarObservation_moment_product_transport μ hSecond (scalarObservationIsometry response)
  simp only [← hφ] at hnorm hinter hintegral hlaw hsum
  exact ⟨hnorm, hinter, hintegral, hlaw (n + 1), hlaw (n + 2), hsum (n + 1)⟩

end LOOConcentration.Manuscript.Internal
