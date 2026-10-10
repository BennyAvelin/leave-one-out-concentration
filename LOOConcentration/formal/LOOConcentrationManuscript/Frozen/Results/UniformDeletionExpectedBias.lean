import LOOConcentrationManuscript.Internal.UniformDeletionExpectedBiasConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript

open MeasureTheory ProbabilityTheory

/-- The uniform deletion producer supplies the exact expected-loss conjunct
used by `Stable`, including the ordered heldout integrability and each
full-fit independent-test comparison. -/
theorem uniformDeletionExpectedBias
    {k m : ℕ}
    (μ : Measure (LOOConcentration.Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ,
      LOOConcentration.Estimator (k + 1) (m + 1) (r + 1))
    (L : LOOConcentration.Responses (m + 1) →
      LOOConcentration.Responses (m + 1) → ℝ)
    (β : ℕ → ℝ)
    (hJointMeas : ∀ r,
      Measurable
        (fun p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (r + 1) ×
            LOOConcentration.Observation (k + 1) (m + 1) =>
          LOOConcentration.fittedLoss (T r) L p.1 p.2))
    (hFullL1 : ∀ n,
      Integrable
        (fun p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1) =>
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2)
        ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hUniform : ∀ n (i : Fin (n + 2))
      (D : LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2))
      (z : LOOConcentration.Observation (k + 1) (m + 1)),
        |LOOConcentration.fittedLoss (T (n + 1)) L D z -
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) z| ≤ β (n + 2)) :
    ∀ n (i : Fin (n + 2)),
      Integrable
        (fun D : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) =>
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
      Integrable
        (fun p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1) =>
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2)
        ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) ∧
      |(∫ D : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2),
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1),
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
            ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ β (n + 2) := by
  exact LOOConcentration.Manuscript.Internal.uniform_deletion_stable_bias_field
    μ T L β hJointMeas hFullL1 hUniform

end LOOConcentration.Manuscript
