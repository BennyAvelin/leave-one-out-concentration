import LOOConcentrationManuscript.Internal.KernelDensityZeroResponseEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The source's actual zero-response dataset has the scalar KDE feature formula,
ordered IID law, finite second moment and finite native log-Sobolev constant. -/
theorem kde_zeroResponse_actual_estimator_standing_inputs
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x^2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : ℝ → ℝ) (h : { t : ℝ // 0 < t }) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x),(fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    Integrable LOOConcentration.observationNormSq ν ∧
      (∫ z : LOOConcentration.Observation 1 1, LOOConcentration.observationNormSq z ∂ν) =
        (∫ x : ℝ, x^2 ∂μ) ∧
      (∀ r : ℕ,
        (Measure.pi (fun _ : Fin (r+1) => μ)).map
          (fun X : Fin (r+1) → ℝ => fun i => φ (X i)) =
            Measure.pi (fun _ : Fin (r+1) => ν) ∧
        (∀ X : Fin (r+1) → ℝ, (∀ i, (φ (X i)).2 0 = 0) ∧
          ∀ t : ℝ,
            (r+1 : ℝ)⁻¹ * (∑ i : Fin (r+1), K ((t-(φ (X i)).1 0)/h.val)/h.val) =
              (r+1 : ℝ)⁻¹ * (∑ i : Fin (r+1), K ((t-X i)/h.val)/h.val))) ∧
      LOOConcentration.Revision.observationLogSobolevConstant ν < ⊤ := by
  intro φ ν
  have hTransport := kde_zeroResponse_moment_law_and_lsi_transport μ hSecond
  refine ⟨hTransport.2.1,hTransport.2.2.1,?_,?_⟩
  · intro r
    refine ⟨hTransport.2.2.2.1 r,?_⟩
    intro X
    exact ⟨fun _ => rfl,fun _ => rfl⟩
  · exact lt_of_le_of_lt hTransport.2.2.2.2 hLSI

end LOOConcentration.Manuscript.Internal
