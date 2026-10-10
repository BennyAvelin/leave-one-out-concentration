import LOOConcentration.Frozen.Norms.ObservationNorm
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

/-- The coordinate map from a real pair to `Observation 1 1`. -/
noncomputable def gaussianPairObservationCLE :
    (ℝ × ℝ) ≃L[ℝ] ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.prodCongr
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm

@[simp]
theorem gaussianPairObservationCLE_apply (p : ℝ × ℝ) :
    gaussianPairObservationCLE p = (fun _ : Fin 1 => p.1, fun _ : Fin 1 => p.2) := by
  ext i <;> simp [gaussianPairObservationCLE]

@[simp]
theorem gaussianPairObservationCLE_symm_apply (z : Observation 1 1) :
    gaussianPairObservationCLE.symm z = (z.1 0, z.2 0) := by
  simp [gaussianPairObservationCLE]

theorem gaussianPairObservationCLE_measurable :
    Measurable (gaussianPairObservationCLE : ℝ × ℝ → Observation 1 1) :=
  gaussianPairObservationCLE.continuous.measurable

theorem gaussianPairObservationCLE_symm_measurable :
    Measurable (gaussianPairObservationCLE.symm : Observation 1 1 → ℝ × ℝ) :=
  gaussianPairObservationCLE.symm.continuous.measurable

theorem gaussianPairObservationCLE_continuous :
    Continuous (gaussianPairObservationCLE : ℝ × ℝ → Observation 1 1) :=
  gaussianPairObservationCLE.continuous

theorem gaussianPairObservationCLE_symm_continuous :
    Continuous (gaussianPairObservationCLE.symm : Observation 1 1 → ℝ × ℝ) :=
  gaussianPairObservationCLE.symm.continuous

/-- The source squared Euclidean norm on a real pair. -/
def gaussianPairNormSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- The coordinate transport preserves the frozen squared Euclidean norm. -/
theorem gaussianPairObservationCLE_observationNormSq (p : ℝ × ℝ) :
    observationNormSq (gaussianPairObservationCLE p) = gaussianPairNormSq p := by
  simp [observationNormSq, gaussianPairNormSq]

/-- The frozen Euclidean norm is the square root of the source pair norm. -/
theorem gaussianPairObservationCLE_observationNorm (p : ℝ × ℝ) :
    observationNorm (gaussianPairObservationCLE p) = Real.sqrt (gaussianPairNormSq p) := by
  rw [observationNorm, gaussianPairObservationCLE_observationNormSq]

/-- One standard real Gaussian noise coordinate. -/
noncomputable abbrev gaussianObservationCoordinateLaw : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The literal product law of two independent standard real Gaussian noises. -/
noncomputable def gaussianObservationPairLaw : Measure (ℝ × ℝ) :=
  gaussianObservationCoordinateLaw.prod gaussianObservationCoordinateLaw

/-- The actual `Observation 1 1` noise law, defined by pushforward of the
independent Gaussian pair law. -/
noncomputable def gaussianObservationLaw : Measure (Observation 1 1) :=
  gaussianObservationPairLaw.map gaussianPairObservationCLE

theorem gaussianObservationCoordinateLaw_isProbability :
    IsProbabilityMeasure gaussianObservationCoordinateLaw := by
  infer_instance

instance gaussianObservationPairLaw_isProbability :
    IsProbabilityMeasure gaussianObservationPairLaw := by
  dsimp [gaussianObservationPairLaw, gaussianObservationCoordinateLaw]
  infer_instance

instance gaussianObservationLaw_isProbability :
    IsProbabilityMeasure gaussianObservationLaw :=
  Measure.isProbabilityMeasure_map gaussianPairObservationCLE_measurable.aemeasurable

private theorem gaussianObservationCoordinate_sq_integrable :
    Integrable (fun x : ℝ => x ^ 2) gaussianObservationCoordinateLaw := by
  change Integrable (fun x : ℝ => x ^ 2)
    (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))
  exact (ProbabilityTheory.memLp_id_gaussianReal
    (μ := 0) (v := (1 : ℝ≥0)) (2 : ℝ≥0)).integrable_sq

private theorem gaussianObservationCoordinate_sq_integral :
    (∫ x : ℝ, x ^ 2 ∂gaussianObservationCoordinateLaw) = 1 := by
  have hv := ProbabilityTheory.variance_id_gaussianReal
    (μ := 0) (v := (1 : ℝ≥0))
  change ProbabilityTheory.variance (fun x : ℝ => x) gaussianObservationCoordinateLaw = 1 at hv
  rw [ProbabilityTheory.variance_eq_integral
    (X := fun x : ℝ => x) (μ := gaussianObservationCoordinateLaw)
    measurable_id'.aemeasurable] at hv
  simpa [gaussianObservationCoordinateLaw, ProbabilityTheory.integral_id_gaussianReal] using hv

private theorem gaussianObservationPairNormSq_integrable :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) gaussianObservationPairLaw := by
  have hfst := gaussianObservationCoordinate_sq_integrable.comp_fst
    gaussianObservationCoordinateLaw
  have hsnd := gaussianObservationCoordinate_sq_integrable.comp_snd
    gaussianObservationCoordinateLaw
  change Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
    (gaussianObservationCoordinateLaw.prod gaussianObservationCoordinateLaw)
  exact hfst.add hsnd

/-- The frozen squared observation norm is integrable under the actual
pushforward Gaussian law. -/
theorem gaussianObservationLaw_observationNormSq_integrable :
    Integrable observationNormSq gaussianObservationLaw := by
  change Integrable observationNormSq
    (Measure.map gaussianPairObservationCLE gaussianObservationPairLaw)
  have hmap : Integrable
      (fun p : ℝ × ℝ => observationNormSq (gaussianPairObservationCLE p))
      gaussianObservationPairLaw := by
    simpa only [gaussianPairObservationCLE_observationNormSq, gaussianPairNormSq] using
      gaussianObservationPairNormSq_integrable
  have hnormMeasurable : Measurable (observationNormSq : Observation 1 1 → ℝ) := by
    fun_prop [observationNormSq]
  exact (integrable_map_measure (f := gaussianPairObservationCLE)
    (g := observationNormSq) hnormMeasurable.aestronglyMeasurable
    gaussianPairObservationCLE_measurable.aemeasurable).2 hmap

/-- The actual transported Gaussian observation law has exact second moment
`M₂ = 2` for the frozen squared Euclidean norm. -/
theorem gaussianObservationLaw_M2 :
    (∫ z : Observation 1 1, observationNormSq z ∂gaussianObservationLaw) = 2 := by
  rw [gaussianObservationLaw]
  rw [integral_map gaussianPairObservationCLE_measurable.aemeasurable
    (by fun_prop [observationNormSq])]
  simp_rw [gaussianPairObservationCLE_observationNormSq]
  simp_rw [gaussianPairNormSq]
  rw [gaussianObservationPairLaw]
  have hfst := gaussianObservationCoordinate_sq_integrable.comp_fst
    gaussianObservationCoordinateLaw
  have hsnd := gaussianObservationCoordinate_sq_integrable.comp_snd
    gaussianObservationCoordinateLaw
  rw [integral_add hfst hsnd]
  rw [MeasureTheory.integral_fun_fst (μ := gaussianObservationCoordinateLaw)
    (ν := gaussianObservationCoordinateLaw) (f := fun x : ℝ => x ^ 2)]
  rw [MeasureTheory.integral_fun_snd (μ := gaussianObservationCoordinateLaw)
    (ν := gaussianObservationCoordinateLaw) (f := fun x : ℝ => x ^ 2)]
  simp [gaussianObservationCoordinateLaw, gaussianObservationCoordinate_sq_integral]
  norm_num

/-- Coordinatewise transport on a finite sample of independent Gaussian pairs. -/
noncomputable def gaussianObservationSampleMap (r : ℕ) :
    (Fin r → ℝ × ℝ) → (Fin r → Observation 1 1) :=
  fun G i => gaussianPairObservationCLE (G i)

/-- The product law of `r` independent Gaussian noise pairs. -/
noncomputable def gaussianObservationPairSampleLaw (r : ℕ) :
    Measure (Fin r → ℝ × ℝ) :=
  Measure.pi fun _ : Fin r => gaussianObservationPairLaw

/-- The product law of `r` independent transported Gaussian observations. -/
noncomputable def gaussianObservationSampleLaw (r : ℕ) :
    Measure (Fin r → Observation 1 1) :=
  Measure.pi fun _ : Fin r => gaussianObservationLaw

theorem gaussianObservationSampleLaw_isProbability (r : ℕ) :
    IsProbabilityMeasure (gaussianObservationSampleLaw r) := by
  change IsProbabilityMeasure (Measure.pi fun _ : Fin r => gaussianObservationLaw)
  infer_instance

theorem gaussianObservationSampleMap_measurable (r : ℕ) :
    Measurable (gaussianObservationSampleMap r) := by
  change Measurable (fun G : Fin r → ℝ × ℝ =>
    fun i : Fin r => gaussianPairObservationCLE (G i))
  exact (MeasureTheory.measurePreserving_pi
    (μ := fun _ : Fin r => gaussianObservationPairLaw)
    (ν := fun _ : Fin r => gaussianObservationLaw)
    (f := fun _ : Fin r => gaussianPairObservationCLE)
    (fun _ => ⟨gaussianPairObservationCLE_measurable, rfl⟩)).measurable

/-- The finite Pi sample/test law is the pushforward under the coordinatewise
real-pair to observation map. -/
theorem gaussianObservationSampleLaw_eq_map (r : ℕ) :
    Measure.map (gaussianObservationSampleMap r) (gaussianObservationPairSampleLaw r) =
      gaussianObservationSampleLaw r := by
  change Measure.map (fun G i => gaussianPairObservationCLE (G i))
      (Measure.pi fun _ : Fin r => gaussianObservationPairLaw) =
    Measure.pi fun _ : Fin r => gaussianObservationLaw
  exact (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin r => gaussianObservationPairLaw)
      (ν := fun _ : Fin r => gaussianObservationLaw)
      (f := fun _ : Fin r => gaussianPairObservationCLE)
      (fun _ => ⟨gaussianPairObservationCLE_measurable, rfl⟩)).map_eq

#print axioms gaussianPairObservationCLE
#print axioms gaussianPairObservationCLE_apply
#print axioms gaussianPairObservationCLE_symm_apply
#print axioms gaussianPairObservationCLE_measurable
#print axioms gaussianPairObservationCLE_symm_measurable
#print axioms gaussianPairObservationCLE_continuous
#print axioms gaussianPairObservationCLE_symm_continuous
#print axioms gaussianPairObservationCLE_observationNormSq
#print axioms gaussianPairObservationCLE_observationNorm
#print axioms gaussianObservationCoordinateLaw_isProbability
#print axioms gaussianObservationPairLaw_isProbability
#print axioms gaussianObservationLaw
#print axioms gaussianObservationLaw_isProbability
#print axioms gaussianObservationLaw_observationNormSq_integrable
#print axioms gaussianObservationLaw_M2
#print axioms gaussianObservationSampleLaw_isProbability
#print axioms gaussianObservationSampleMap_measurable
#print axioms gaussianObservationSampleLaw_eq_map

end LOOConcentration
