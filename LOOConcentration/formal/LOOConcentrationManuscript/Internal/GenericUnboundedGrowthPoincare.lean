import LOOConcentrationRevision.Analysis.UnboundedCenteredLpLimitInfrastructure
import LOOConcentrationRevision.Concentration.SourceSegmentIntegrability
import LOOConcentrationRevision.FunctionalInequalities.BoundedProductLSI
import LOOConcentrationRevision.Probability.ProductNormCapExpectations
import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped ENNReal

private theorem integral_sq_eq_eLpNorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  let u : α →₂[μ] ℝ := hf.toLp f
  have hu : ∀ᵐ x ∂μ, u x = f x := hf.coeFn_toLp
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, inner ℝ (u x) (u x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [← hx, real_inner_self_eq_norm_sq]
      simp only [Real.norm_eq_abs, sq_abs]
    _ = inner ℝ u u := by rw [MeasureTheory.L2.inner_def]
    _ = ‖u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    _ = (eLpNorm f 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]

/-- Mean zero and actual centered unit variance on the scalar coordinate give
unit raw squared-norm moment on the literal one-coordinate Euclidean carrier. -/
theorem scalar_unit_variance_norm_sq_integral
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hmean : (∫ x : EuclideanSpace ℝ (Fin 1), x 0 ∂μ) = 0)
    (hcentered :
      (∫ x : EuclideanSpace ℝ (Fin 1),
        (x 0 - ∫ y : EuclideanSpace ℝ (Fin 1), y 0 ∂μ) ^ 2 ∂μ) = 1) :
    (∫ x : EuclideanSpace ℝ (Fin 1), ‖x‖ ^ 2 ∂μ) = 1 := by
  have hnorm (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  calc
    (∫ x : EuclideanSpace ℝ (Fin 1), ‖x‖ ^ 2 ∂μ) =
        ∫ x, (x 0) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hnorm x
    _ = 1 := by simpa only [hmean, sub_zero] using hcentered

/-- Actual source variance Poincare bound for a locally Lipschitz function on
an arbitrary positive product of a centered, unit-variance scalar Euclidean
law. The product law, product norm moment, product LSI comparison, function
integrability, and centered L2 membership are all derived internally. -/
theorem generic_unbounded_growth_variance_le
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hfinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2) μ)
    (hmean : (∫ x : EuclideanSpace ℝ (Fin 1), x 0 ∂μ) = 0)
    (hcentered :
      (∫ x : EuclideanSpace ℝ (Fin 1),
        (x 0 - ∫ y : EuclideanSpace ℝ (Fin 1), y 0 ∂μ) ^ 2 ∂μ) = 1)
    (r : ℕ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ)
    (hF : LocallyLipschitz F) (b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (b : ℝ) * ‖x‖) :
    (∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1),
      (F x - ∫ y, F y ∂LOOConcentration.Revision.euclideanProductLaw
        (κ := Fin (r + 1)) μ) ^ 2 ∂LOOConcentration.Revision.euclideanProductLaw
          (κ := Fin (r + 1)) μ) ≤
      (LOOConcentration.Revision.logSobolevConstant μ).toReal *
        (r + 1 : ℝ) * (b : ℝ) ^ 2 := by
  let ν := LOOConcentration.Revision.euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν :=
    LOOConcentration.Revision.euclideanProductLaw_isProbabilityMeasure μ
  have hunit := scalar_unit_variance_norm_sq_integral μ hmean hcentered
  have hprodMoment : Integrable (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖ ^ 2) ν :=
    LOOConcentration.Revision.integrable_euclideanProductLaw_norm_sq μ hM2
  have hprodMomentValue :
      (∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1), ‖x‖ ^ 2 ∂ν) = (r + 1 : ℝ) := by
    rw [LOOConcentration.Revision.integral_euclideanProductLaw_norm_sq
      (κ := Fin (r + 1)) μ hM2]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, hunit, mul_one]
  have hrad : MemLp
      (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν :=
    (memLp_two_iff_integrable_sq continuous_norm.aestronglyMeasurable).2 hprodMoment
  have hradMoment :
      (∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1), ‖x‖ ^ 2 ∂ν) =
        (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν).toReal ^ 2 :=
    integral_sq_eq_eLpNorm_sq ν (fun x => ‖x‖) hrad
  have hradNorm :
      (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν).toReal =
        Real.sqrt (r + 1 : ℝ) := by
    have hnonneg : 0 ≤
        (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν).toReal :=
      ENNReal.toReal_nonneg
    have hNnonneg : 0 ≤ (r + 1 : ℝ) := by positivity
    have hsq :
        (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν).toReal ^ 2 =
          (r + 1 : ℝ) := by
      calc
        _ = ∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1), ‖x‖ ^ 2 ∂ν := hradMoment.symm
        _ = _ := hprodMomentValue
    have hsq' :
        (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖) 2 ν).toReal ^ 2 =
          Real.sqrt (r + 1 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hNnonneg]
      exact hsq
    apply le_antisymm
    · exact (sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).1 (le_of_eq hsq')
    · exact (sq_le_sq₀ (Real.sqrt_nonneg _) hnonneg).1 (le_of_eq hsq'.symm)
  have hprodLSI :
      LOOConcentration.Revision.logSobolevConstant ν ≤
        ENNReal.ofReal (LOOConcentration.Revision.logSobolevConstant μ).toReal := by
    have h := LOOConcentration.Revision.logSobolevConstant_euclideanProductLaw_le r μ hfinite
    have hfinite' : LOOConcentration.Revision.logSobolevConstant μ < ⊤ := hfinite
    rw [ENNReal.ofReal_toReal hfinite'.ne]
    simpa [ν] using h
  have hC : 0 ≤ (LOOConcentration.Revision.logSobolevConstant μ).toReal := ENNReal.toReal_nonneg
  obtain ⟨hseg, _hFint⟩ :=
    LOOConcentration.Revision.source_product_segment_estimate_and_integrable
      μ hM2 F hF 0 b (by simpa using hgrad)
  have hrad' : MemLp
      (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖)
      (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hrad
  have hlimit := LOOConcentration.Revision.unbounded_centered_lp_of_norm_memLp
    ν (LOOConcentration.Revision.logSobolevConstant μ).toReal hC hprodLSI hprodMoment
      F hF 0 b hseg (p := 2) (by norm_num) hrad'
  let Fc : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ :=
    fun x => F x - ∫ y, F y ∂ν
  have hFcMem : MemLp Fc 2 ν := by
    simpa [Fc] using hlimit.2.1
  have hFcNorm :
      eLpNorm Fc 2 ν ≤ ENNReal.ofReal
        (Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
          (b : ℝ) * Real.sqrt (r + 1 : ℝ)) := by
    have hfactor :
        Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal * (2 - 1)) *
            ((0 : ℝ) + (b : ℝ) *
              (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖)
                (ENNReal.ofReal (2 : ℝ)) ν).toReal) ≤
          Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
            (b : ℝ) * Real.sqrt (r + 1 : ℝ) := by
      have hradNorm' :
          (eLpNorm (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖)
            (ENNReal.ofReal (2 : ℝ)) ν).toReal = Real.sqrt (r + 1 : ℝ) := by
        simpa using hradNorm
      rw [hradNorm']
      have hsqrt :
          Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal * (2 - 1)) =
            Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) := by
        congr 1
        norm_num
      rw [hsqrt, zero_add]
      exact le_of_eq (by ring)
    have hlim' := hlimit.2.2.trans (ENNReal.ofReal_le_ofReal hfactor)
    simpa [Fc] using hlim'
  have hKnonneg : 0 ≤ Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
      (b : ℝ) * Real.sqrt (r + 1 : ℝ) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) b.property) (Real.sqrt_nonneg _)
  have hFcNormReal :
      (eLpNorm Fc 2 ν).toReal ≤
        Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
          (b : ℝ) * Real.sqrt (r + 1 : ℝ) := by
    calc
      (eLpNorm Fc 2 ν).toReal ≤
          (ENNReal.ofReal
            (Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
              (b : ℝ) * Real.sqrt (r + 1 : ℝ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hFcNorm
      _ = _ := ENNReal.toReal_ofReal hKnonneg
  have hFcSq := integral_sq_eq_eLpNorm_sq ν Fc hFcMem
  have hFcNonneg : 0 ≤ (eLpNorm Fc 2 ν).toReal := ENNReal.toReal_nonneg
  calc
    (∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1),
        (F x - ∫ y, F y ∂ν) ^ 2 ∂ν) = (eLpNorm Fc 2 ν).toReal ^ 2 := by
      simpa only [Fc] using hFcSq
    _ ≤ (Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
        (b : ℝ) * Real.sqrt (r + 1 : ℝ)) ^ 2 :=
      (sq_le_sq₀ hFcNonneg hKnonneg).2 hFcNormReal
    _ = (LOOConcentration.Revision.logSobolevConstant μ).toReal *
        (r + 1 : ℝ) * (b : ℝ) ^ 2 := by
      calc
        (Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) *
            (b : ℝ) * Real.sqrt (r + 1 : ℝ)) ^ 2 =
            Real.sqrt ((LOOConcentration.Revision.logSobolevConstant μ).toReal) ^ 2 *
              (b : ℝ) ^ 2 * Real.sqrt (r + 1 : ℝ) ^ 2 := by ring
        _ = (LOOConcentration.Revision.logSobolevConstant μ).toReal *
            (r + 1 : ℝ) * (b : ℝ) ^ 2 := by
          rw [Real.sq_sqrt hC, Real.sq_sqrt (show 0 ≤ (r + 1 : ℝ) by positivity)]
          ring

end LOOConcentration.Manuscript.Internal
