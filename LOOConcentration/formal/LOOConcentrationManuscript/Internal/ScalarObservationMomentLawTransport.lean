import LOOConcentrationManuscript.Internal.ScalarMomentLawTransport
import LOOConcentrationRevision.Geometry.CoordinateTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- Transport scalar moments and ordered product laws to the actual observation carrier. -/
theorem scalarObservation_moment_product_transport
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (e : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1)) :
    let φ := LOOConcentration.Revision.observationOfEuclidean ∘ e
    let ν := μ.map φ
    (∀ x : ℝ, LOOConcentration.observationNormSq (φ x) = x ^ 2) ∧
    Integrable LOOConcentration.observationNormSq ν ∧
    ((∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.observationNormSq z ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    (∀ r : ℕ,
      (Measure.pi fun _ : Fin (r + 1) => μ).map
        (fun D : Fin (r + 1) → ℝ => fun i => φ (D i)) =
          Measure.pi fun _ : Fin (r + 1) => ν) ∧
    (∀ (r : ℕ) (D : Fin (r + 1) → ℝ),
      (∑ i : Fin (r + 1), LOOConcentration.observationNormSq (φ (D i))) =
        ∑ i : Fin (r + 1), (D i) ^ 2) := by
  classical
  intro φ ν
  let inv := LOOConcentration.Revision.observationOfEuclidean
      (k := 1) (m := 1)
  let νE := μ.map e
  have he : Measurable e := e.continuous.measurable
  have hi : Measurable inv := LOOConcentration.Revision.measurable_observationOfEuclidean
  have hφ : Measurable φ := hi.comp he
  have hν : νE.map inv = ν := Measure.map_map hi he
  have hsq (y : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1)) :
      LOOConcentration.observationNormSq (inv y) = ‖y‖ ^ 2 := by
    rw [← LOOConcentration.observationNorm_sq,
      LOOConcentration.Revision.observationNorm_observationOfEuclidean]
  have hm : Measurable (LOOConcentration.observationNormSq
      (k := 1) (m := 1)) := by
    unfold LOOConcentration.observationNormSq
    fun_prop
  obtain ⟨hnorm, hinter, hintegral, hlaw, hsum⟩ :=
    scalar_linearIsometry_moment_product_transport μ hSecond e
  have hνEprob : IsProbabilityMeasure νE := μ.isProbabilityMeasure_map he.aemeasurable
  have hνprob : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hνsigma : SigmaFinite ν := by
    have hfinite : IsFiniteMeasure ν := ⟨by rw [hνprob.measure_univ]; exact ENNReal.one_lt_top⟩
    exact @IsFiniteMeasure.toSigmaFinite _ _ ν hfinite
  have hνinter : Integrable LOOConcentration.observationNormSq ν := by
    rw [← hν]
    apply (integrable_map_measure hm.aestronglyMeasurable hi.aemeasurable).2
    exact hinter.congr (Filter.Eventually.of_forall fun y => (hsq y).symm)
  refine ⟨fun x => (hsq (e x)).trans (hnorm x), hνinter, ?_, ?_, ?_⟩
  · calc
      (∫ z, LOOConcentration.observationNormSq z ∂ν) =
          ∫ y, LOOConcentration.observationNormSq (inv y) ∂νE := by
        rw [← hν]
        exact integral_map hi.aemeasurable hm.aestronglyMeasurable
      _ = ∫ y, ‖y‖ ^ 2 ∂νE := integral_congr_ae (Filter.Eventually.of_forall hsq)
      _ = ∫ x : ℝ, x ^ 2 ∂μ := hintegral
  · intro r
    have hmE : Measurable (fun D : Fin (r + 1) → ℝ => fun i => e (D i)) := by fun_prop
    have hmI : Measurable (fun D : Fin (r + 1) →
        EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
        fun i => inv (D i)) := by fun_prop
    have hSigmaFamily : ∀ _i : Fin (r + 1), SigmaFinite (νE.map inv) := by
      intro i
      rw [hν]
      exact hνsigma
    calc
      (Measure.pi fun _ : Fin (r + 1) => μ).map
          (fun D : Fin (r + 1) → ℝ => fun i => φ (D i)) =
          ((Measure.pi fun _ : Fin (r + 1) => μ).map
            (fun D : Fin (r + 1) → ℝ => fun i => e (D i))).map
            (fun D => fun i => inv (D i)) := (Measure.map_map hmI hmE).symm
      _ = (Measure.pi fun _ : Fin (r + 1) => νE).map
          (fun D => fun i => inv (D i)) := by rw [hlaw r]
      _ = Measure.pi fun _ : Fin (r + 1) => νE.map inv :=
          Measure.pi_map_pi (hμ := hSigmaFamily) (fun _ => hi.aemeasurable)
      _ = Measure.pi fun _ : Fin (r + 1) => ν := by rw [hν]
  · intro r D
    calc
      (∑ i, LOOConcentration.observationNormSq (φ (D i))) =
          ∑ i : Fin (r + 1), ‖e (D i)‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => hsq (e (D i))
      _ = ∑ i : Fin (r + 1), (D i) ^ 2 := hsum r D

end LOOConcentration.Manuscript.Internal
