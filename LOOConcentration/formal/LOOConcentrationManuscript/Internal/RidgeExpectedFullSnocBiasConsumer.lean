import LOOConcentrationManuscript.Internal.RidgeExpectedPredictionChange
import LOOConcentrationManuscript.Internal.IIDSnocTestLaw
import LOOConcentrationManuscript.Internal.RidgeExpectedDeleteBiasConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Actual ordered delete-one bias for the literal stabilized predictor and
absolute loss. The constant is fixed before all sample sizes and all held-out
indices. True integrability and the two iid law transports are proved inside
this consumer from the source first-response and fourth-feature moments. -/
theorem ridge_actual_ordered_expected_delete_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hY1 : Integrable (fun z => |z.2 0|) μ)
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ)
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (i : Fin (n + 2)),
      |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2),
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n)
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|)
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi (fun _ : Fin (n + 2) => μ)) -
        (∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
            LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (n + 1))
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|) p.1 p.2
            ∂(Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ)| ≤ C / (n + 2 : ℝ) := by
  obtain ⟨C, hC, hChange⟩ := ridge_actual_expected_prediction_change_L1 μ hY1 hX4 b δ
  refine ⟨C, hC, ?_⟩
  intro n i
  let L := fun u v : Fin 1 → ℝ => |u 0 - v 0|
  let P := Measure.pi (fun _ : Fin (n + 1) => μ)
  let Q := P.prod μ
  let R := Q.prod μ
  let short := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 1) ×
      LOOConcentration.Observation 1 1 =>
    LOOConcentration.fittedLoss
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n) L p.1 p.2
  let full := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
      LOOConcentration.Observation 1 1 =>
    LOOConcentration.fittedLoss
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (n + 1)) L p.1 p.2
  let shortOnTriple := fun p : ((Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 => short (p.1.1, p.2)
  let fullOnTriple := fun p : ((Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
    full (Fin.snoc p.1.1 p.1.2, p.2)
  have hMom := ridge_actual_first_moment_feature_sq_source μ hX4 hY1
  have hShort : Integrable short Q :=
    ridge_actual_fit_loss_integrable_source_moments μ hY1 hMom.1 b δ n
  have hFull : Integrable full ((Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ) :=
    ridge_actual_fit_loss_integrable_source_moments μ hY1 hMom.1 b δ (n + 1)
  have hs := iid_ignored_added_fresh_test_integrable_integral μ (n + 1) short hShort
  have hf := iid_snoc_fresh_test_integrable_integral μ (n + 1) full hFull
  have hShortTriple : Integrable shortOnTriple R := hs.1
  have hFullTriple : Integrable fullOnTriple R := hf.1
  have hHeld := ridge_actual_ordered_delete_loss_consumer μ hY1 hX4 b δ n
  have hExpectedHeld := (hHeld.2.2 i).2
  have hExpected :
      (∫ D : Fin (n + 2) → LOOConcentration.Observation 1 1,
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n) L
          (LOOConcentration.deleteAt D i) (D i)
          ∂Measure.pi (fun _ : Fin (n + 2) => μ)) = integral R shortOnTriple := by
    exact hExpectedHeld.trans hs.2.symm
  have hExpectedFull :
      integral ((Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ) full =
        integral R fullOnTriple := hf.2.symm
  have hPoint p : |shortOnTriple p - fullOnTriple p| ≤
      ridgeActualAddOnePredictionChangeAbs n b δ p := by
    dsimp [shortOnTriple, fullOnTriple, short, full, L, LOOConcentration.fittedLoss,
      ridgeActualAddOnePredictionChangeAbs]
    have hFeature : (fun _ : Fin 1 => p.2.1 0) = p.2.1 := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      rw [hj]
    have h := abs_abs_sub_abs_le_abs_sub
      (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n p.1.1)
        (fun _ : Fin 1 => p.2.1 0)) 0 - p.2.2 0)
      (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (n + 1)
        (Fin.snoc p.1.1 p.1.2)) (fun _ : Fin 1 => p.2.1 0)) 0 - p.2.2 0)
    have hdiff (a c y : ℝ) : |(a - y) - (c - y)| = |c - a| := by
      rw [sub_sub_sub_cancel_right, abs_sub_comm]
    simpa only [hdiff, hFeature] using h
  have hBias : |integral R shortOnTriple - integral R fullOnTriple| ≤ C / (n + 2 : ℝ) := by
    calc
      _ = |∫ p, shortOnTriple p - fullOnTriple p ∂ R| := by
        rw [integral_sub hShortTriple hFullTriple]
      _ ≤ ∫ p, |shortOnTriple p - fullOnTriple p| ∂ R :=
        abs_integral_le_integral_abs
      _ ≤ integral R (ridgeActualAddOnePredictionChangeAbs n b δ) :=
        integral_mono ((hShortTriple.sub hFullTriple).abs) (hChange n).1 hPoint
      _ ≤ C / (n + 2 : ℝ) := (hChange n).2
  change |(∫ D : Fin (n + 2) → LOOConcentration.Observation 1 1,
      LOOConcentration.fittedLoss
        (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n) L
        (LOOConcentration.deleteAt D i) (D i)
        ∂Measure.pi (fun _ : Fin (n + 2) => μ)) -
    integral ((Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ) full| ≤ _
  rw [hExpected, hExpectedFull]
  exact hBias

end LOOConcentration.Manuscript.Internal
