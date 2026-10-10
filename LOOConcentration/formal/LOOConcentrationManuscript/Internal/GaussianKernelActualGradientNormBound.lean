import LOOConcentrationManuscript.Internal.GaussianKernelGradientVectorConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelCoefficientNormBound
import LOOConcentration.Geometry.NormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- The actual ambient gradient satisfies the source sample-size bound on the
entire paired Euclidean data space, with explicit constants depending only on h and δ. -/
theorem gaussianKernel_predictor_ambient_gradient_norm_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (x : ℝ)
    (D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1))) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹
    let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
      (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
        ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
    ‖gradient T D‖ ≤ ((W/h)/δ)/Real.sqrt (r+1 : ℝ)+
      ((W/h^2)/δ)*(1+(W/h)/δ)*‖D‖/(r+1 : ℝ) := by
  intro Kh W T
  let E : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) :=
    fun i => ((fun _ : Fin 1 => D (i,Sum.inl 0)),(fun _ : Fin 1 => D (i,Sum.inr 0)))
  have hE : LOOConcentration.datasetToEuclidean E = D := by
    apply PiLp.ext
    rintro ⟨j,s⟩
    cases s with
    | inl k => simp [LOOConcentration.datasetToEuclidean,E,Fin.eq_zero k]
    | inr k => simp [LOOConcentration.datasetToEuclidean,E,Fin.eq_zero k]
  have hNorm : LOOConcentration.datasetNorm E = ‖D‖ := by
    rw [LOOConcentration.datasetNorm_eq_euclidean,hE]
  have hBound := gaussianKernel_actualDataset_coefficient_vector_norm_bound h δ hh hδ r E x
  have hVector := gaussianKernel_predictor_ambient_gradient_eq_coefficient_vector h δ hh hδ r x D
  rw [hVector]
  simpa only [E,hNorm] using hBound

end LOOConcentration.Manuscript.Internal
