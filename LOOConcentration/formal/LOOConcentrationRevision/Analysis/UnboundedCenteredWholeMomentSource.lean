import LOOConcentrationRevision.Analysis.UnboundedCenteredLpLimitInfrastructure
import UnboundedSharpNormMomentSource
import LOOConcentrationRevision.Providers.Bridges.Ae_gradient_segment_estimate
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Probability.ProductLawTransport
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace LOOConcentration.Revision

private theorem locallyLipschitz_ae_differentiableAt_all_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x := by
  classical
  by_cases hI : Nonempty ι
  · exact @LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean
      ι inferInstance hI F hF
  · have hempty (i : ι) : False := hI ⟨i⟩
    have hEq (x y : EuclideanSpace ℝ ι) : x = y := by
      ext i
      exact False.elim (hempty i)
    have hconst : F = fun _ => F 0 := by
      funext x
      exact congrArg F (hEq x 0)
    filter_upwards [] with x
    rw [hconst]
    exact differentiableAt_const _

/-- The unconditional centered source moment on a finite Euclidean carrier.
The local slope segment estimate, finite p norm of the radius, and
integrability of F are all derived internally from the source premises. -/
private theorem unbounded_centered_moment_of_lsi_bound_and_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F)
    (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    {p : ℝ} (hp : 2 ≤ p)
    (hnorm : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)))) :
    Integrable F μ ∧
      MemLp (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal
          (Real.sqrt (C * (p - 1)) *
            ((a : ℝ) + (b : ℝ) *
              Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) +
                C * (p - 2)))) := by
  have hdiff := locallyLipschitz_ae_differentiableAt_all_finite F hF
  have hgradFull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖ :=
    hdiff.and hgrad
  have hseg := Providers.ae_gradient_segment_estimate F hF a b hgradFull
  have hcenter := unbounded_centered_lp_of_norm_memLp μ C hC hLC
    hmoment F hF a b hseg hp hnorm.1
  have hnormRealENN :
      (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
        (ENNReal.ofReal p) μ).toReal ≤
        (ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm.2
  have hnormReal' :
      (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
        (ENNReal.ofReal p) μ).toReal ≤
        Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)) := by
    calc
      _ ≤ (ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)))).toReal := hnormRealENN
      _ = _ := by simp
  have hfactor :
      (a : ℝ) + (b : ℝ) *
          (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
            (ENNReal.ofReal p) μ).toReal ≤
        (a : ℝ) + (b : ℝ) *
          Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)) := by
    calc
      _ = (b : ℝ) *
          (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
            (ENNReal.ofReal p) μ).toReal + (a : ℝ) := by ring
      _ ≤ (b : ℝ) *
          Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)) + (a : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hnormReal' b.property) le_rfl
      _ = _ := by ring
  have hscale :=
    mul_le_mul_of_nonneg_left hfactor
      (Real.sqrt_nonneg (C * (p - 1)))
  refine ⟨hcenter.1, hcenter.2.1, ?_⟩
  have hbound := hcenter.2.2.trans (ENNReal.ofReal_le_ofReal hscale)
  exact hbound

/-- The native-LSI form of the centered source moment estimate. -/
theorem unbounded_centered_moment_of_native_lsi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F)
    (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable F μ ∧
      MemLp (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal
          (Real.sqrt ((logSobolevConstant μ).toReal * (p - 1)) *
            ((a : ℝ) + (b : ℝ) *
              Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) +
                (logSobolevConstant μ).toReal * (p - 2)))) := by
  let C : ℝ := (logSobolevConstant μ).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hfinite.ne).symm.le
  have hnorm := unboundedSharpNormMoment μ C hC hLC hmoment hp
  simpa [C] using
    (unbounded_centered_moment_of_lsi_bound_and_norm μ C hC hLC hmoment
      F hF a b hgrad hp hnorm)

/-- Source moment bound on the actual ordered product of r+1 observations.
The observation's intrinsic LSI constant is used before tensorization;
probability, product LSI, raw product second moment, radius MemLp, and the
centered conclusion are all produced internally. -/
theorem unbounded_centered_observation_product
    {k m r : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable (LOOConcentration.observationNormSq) μ)
    (F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) → ℝ)
    (hF : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable F (datasetLawOfObservation (r := r + 1) μ) ∧
      MemLp (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := r + 1) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := r + 1) μ) ∧
      eLpNorm (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := r + 1) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := r + 1) μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            ((a : ℝ) + (b : ℝ) *
              Real.sqrt (((r + 1 : ℕ) : ℝ) *
                  (∫ z, LOOConcentration.observationNormSq z ∂μ) +
                (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  let ν := datasetLawOfObservation (r := r + 1) μ
  let μE := μ.map LOOConcentration.observationToEuclidean
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  have hprob : IsProbabilityMeasure ν :=
    datasetLawOfObservation_isProbabilityMeasure μ
  have hprobE : IsProbabilityMeasure μE := by
    exact Measure.isProbabilityMeasure_map
      LOOConcentration.Revision.measurable_observationToEuclidean.aemeasurable
  let _ : IsProbabilityMeasure μE := hprobE
  have hfiniteE : logSobolevConstant μE < ⊤ := by
    simpa [μE, observationLogSobolevConstant] using hfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLCbase : logSobolevConstant μE ≤ ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hfiniteE.ne).symm.le
  let _ : IsProbabilityMeasure ν := hprob
  let _ : IsProbabilityMeasure (euclideanProductLaw (κ := Fin (r + 1)) μE) :=
    euclideanProductLaw_isProbabilityMeasure μE
  have hprod : logSobolevConstant (euclideanProductLaw (κ := Fin (r + 1)) μE) ≤
      logSobolevConstant μE := by
    simpa using logSobolevConstant_euclideanProductLaw_le r μE hfiniteE
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal C := by
    have h := hprod.trans hLCbase
    simpa [ν, ← euclideanProductLaw_observation_map_eq_datasetLaw μ] using h
  have hmoment :
      Integrable (fun x : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖ ^ 2) ν :=
    integrable_datasetLaw_norm_sq μ hM2
  have hscale :
      (∫ x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m (r + 1)), ‖x‖ ^ 2 ∂ν) =
        ((r + 1 : ℕ) : ℝ) *
          (∫ z, LOOConcentration.observationNormSq z ∂μ) :=
    integral_datasetLaw_norm_sq μ hM2
  have hnormProduct := orderedProductNormSharp (r := r) μ hfinite hM2 hp
  have hnormNu :
      MemLp (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
          (ENNReal.ofReal p) ν ∧
        eLpNorm (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
          (ENNReal.ofReal p) ν ≤
          ENNReal.ofReal (Real.sqrt
            ((∫ x, ‖x‖ ^ 2 ∂ν) + C * (p - 2))) := by
    refine ⟨?_, ?_⟩
    · simpa [ν] using hnormProduct.1
    · have hb := hnormProduct.2
      rw [← hscale] at hb
      simpa [ν] using hb
  have hsource := unbounded_centered_moment_of_lsi_bound_and_norm
    ν C hC hLC hmoment F hF a b hgrad hp hnormNu
  refine ⟨?_, ?_, ?_⟩
  · simpa [ν] using hsource.1
  · simpa [ν] using hsource.2.1
  · simpa [ν, C, hscale] using hsource.2.2

end LOOConcentration.Revision
