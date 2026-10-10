import LOOConcentrationManuscript.Internal.RidgeExpectedDeleteBias
import LOOConcentration.Probability.FittedConditionalRisk
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Probability.SampleTestLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
noncomputable section

private abbrev ridgeDeleteAbsoluteLossConsumer :
    LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
  fun u v => |u 0 - v 0|

/-- Source moments make the literal Ridge full risk and ordered held-out
delete losses integrable. The held-out expectation is transported through the
actual `deleteAt` map to the same-law fresh-test expectation. -/
theorem ridge_actual_ordered_delete_loss_consumer
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hY1 : Integrable (fun z => |z.2 0|) μ)
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ)
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    let P := Measure.pi (fun _ : Fin (r + 2) => μ)
    let Q := (Measure.pi (fun _ : Fin (r + 1) => μ)).prod μ
    let T : ∀ n : ℕ, LOOConcentration.Estimator 1 1 (n + 1) :=
      fun n => LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n
    let L := ridgeDeleteAbsoluteLossConsumer
    Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) ×
          LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T (r + 1)) L p.1 p.2) (P.prod μ) ∧
    Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) =>
        LOOConcentration.looEstimate (T r) L D) P ∧
    ∀ i : Fin (r + 2),
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) =>
          LOOConcentration.fittedLoss (T r) L (LOOConcentration.deleteAt D i) (D i)) P ∧
      (∫ D, LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.deleteAt D i) (D i) ∂P) =
        ∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss (T r) L p.1 p.2 ∂Q := by
  classical
  intro P Q T L
  have hMom := ridge_actual_first_moment_feature_sq_source μ hX4 hY1
  have hFull := ridge_actual_fit_loss_integrable_source_moments μ hY1
    hMom.1 b δ (r + 1)
  have hShort := ridge_actual_fit_loss_integrable_source_moments μ hY1
    hMom.1 b δ r
  have hHeldMap (i : Fin (r + 2)) :=
    LOOConcentration.deleted_sample_and_heldout_measurePreserving (μ := μ) (n := r) i
  have hHeldInt (i : Fin (r + 2)) :
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) =>
          LOOConcentration.fittedLoss (T r) L (LOOConcentration.deleteAt D i) (D i)) P := by
    exact (hHeldMap i).integrable_comp_of_integrable hShort
  have hHeldEq (i : Fin (r + 2)) :
      (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2),
        LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.deleteAt D i) (D i) ∂P) =
      ∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1,
        LOOConcentration.fittedLoss (T r) L p.1 p.2 ∂Q := by
    exact LOOConcentration.integral_heldout_fittedLoss μ (T r) L i hShort
  have hLOO : Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) =>
        LOOConcentration.looEstimate (T r) L D) P := by
    have hSum : Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) =>
          ∑ i : Fin (r + 2),
            LOOConcentration.fittedLoss (T r) L
              (LOOConcentration.deleteAt D i) (D i)) P := by
      exact integrable_finsetSum Finset.univ (fun i _ => hHeldInt i)
    simpa only [LOOConcentration.looEstimate, LOOConcentration.fittedLoss,
      L, ridgeDeleteAbsoluteLossConsumer] using
      hSum.div_const (r + 2 : ℝ)
  refine ⟨?_, hLOO, ?_⟩
  · simpa only [P, T, L, ridgeDeleteAbsoluteLossConsumer] using hFull
  · intro i
    exact ⟨hHeldInt i, hHeldEq i⟩

end
end LOOConcentration.Manuscript.Internal
