import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.ProductConditionalRisk
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

/-- The signed full fitted-loss difference is integrable from the two actual
full-loss L¹ inputs. -/
theorem modelSelection_signed_fittedLoss_integrable_all_dimensions {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2 -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) := by
  exact hf₀.sub hf₁

/-- Conditional expectation of the signed full fitted-loss difference is the
actual difference of the two frozen conditional-risk representatives, almost
everywhere on the original sample/test product law. -/
theorem modelSelection_signed_fittedLoss_condExp_all_dimensions {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2 -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      (fun p =>
        (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) p.1 -
          (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) p.1) := by
  have hsub := condExp_sub hf₀ hf₁
    (MeasurableSpace.comap Prod.fst inferInstance)
  have hchar₀ := LOOConcentration.Revision.looRiskL1_characterization
    μ (T₀ (n + 1)) L hf₀
  have hchar₁ := LOOConcentration.Revision.looRiskL1_characterization
    μ (T₁ (n + 1)) L hf₁
  exact hsub.trans (hchar₀.sub hchar₁)

/-- The sample-law risk difference agrees almost everywhere with the integral
of the actual signed full fitted loss over an independent test observation.
The equality uses one common almost-everywhere complement for the two risks. -/
theorem modelSelection_riskDifference_ae_eq_integral_all_dimensions {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    (fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) =ᵐ[
          Measure.pi fun _ : Fin (n + 2) => μ]
    (fun D => ∫ z,
      (LOOConcentration.fittedLoss (T₀ (n + 1)) L D z -
        LOOConcentration.fittedLoss (T₁ (n + 1)) L D z) ∂μ) := by
  have hclass₀ :
      (fun D : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) =>
        (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D) =ᵐ[
          Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => ∫ z,
        LOOConcentration.fittedLoss (T₀ (n + 1)) L D z ∂μ) := by
    exact hf₀.integral_prod_left.coeFn_toL1
  have hclass₁ :
      (fun D : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) =>
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) =ᵐ[
          Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => ∫ z,
        LOOConcentration.fittedLoss (T₁ (n + 1)) L D z ∂μ) := by
    exact hf₁.integral_prod_left.coeFn_toL1
  have hfiber₀ := hf₀.prod_right_ae
  have hfiber₁ := hf₁.prod_right_ae
  filter_upwards [hclass₀, hclass₁, hfiber₀, hfiber₁] with D h₀ h₁ hi₀ hi₁
  rw [h₀, h₁, integral_sub hi₀ hi₁]

/-- For every ordered sample of size `n + 2`, subtracting the two actual LOO
estimates gives the finite average of the pointwise deleted-loss differences. -/
theorem modelSelection_looEstimate_sub_all_dimensions {k m n : ℕ}
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (D : LOOConcentration.Dataset
      (LOOConcentration.Observation k m) (n + 2)) :
    LOOConcentration.looEstimate (T₀ n) L D -
      LOOConcentration.looEstimate (T₁ n) L D =
    (∑ i : Fin (n + 2),
      (LOOConcentration.fittedLoss (T₀ n) L
        (LOOConcentration.deleteAt D i) (D i) -
      LOOConcentration.fittedLoss (T₁ n) L
        (LOOConcentration.deleteAt D i) (D i))) / (n + 2 : ℝ) := by
  unfold LOOConcentration.looEstimate LOOConcentration.fittedLoss
  rw [← sub_div, ← Finset.sum_sub_distrib]

/-- With no response coordinates, both actual fitted losses coincide on the
whole original carrier, regardless of the feature dimension or predictors. -/
theorem modelSelection_signed_fittedLoss_zero_response_all_dimensions {k r : ℕ}
    (T₀ T₁ : LOOConcentration.Estimator k 0 (r + 1))
    (L : LOOConcentration.Responses 0 → LOOConcentration.Responses 0 → ℝ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation k 0) (r + 1))
    (z : LOOConcentration.Observation k 0) :
    LOOConcentration.fittedLoss T₀ L D z -
      LOOConcentration.fittedLoss T₁ L D z = 0 := by
  unfold LOOConcentration.fittedLoss
  rw [Subsingleton.elim ((T₀ D) z.1) ((T₁ D) z.1), sub_self]

end LOOConcentration.Manuscript.Internal
