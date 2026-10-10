import LOOConcentration.Probability.FittedConditionalRisk
import LOOConcentration.Frozen.Foundations.LooEstimate

/-!
# Integrability of the empirical leave-one-out estimate

An integrable fitted loss under a fresh independent test observation gives an
integrable held-out loss at each deleted sample. Their finite average is
therefore integrable.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

theorem integrable_looEstimate
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    Integrable (looEstimate T L) (Measure.pi fun _ : Fin (n + 2) => μ) := by
  have hsum : Integrable
      (fun D : Dataset (Observation k m) (n + 2) =>
        ∑ i : Fin (n + 2), fittedLoss T L (deleteAt D i) (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_heldout_fittedLoss μ T L i hf)
  have hdiv := hsum.div_const (n + 2 : ℝ)
  change Integrable
    (fun D : Dataset (Observation k m) (n + 2) =>
      (∑ i : Fin (n + 2), fittedLoss T L (deleteAt D i) (D i)) / (n + 2))
    (Measure.pi fun _ : Fin (n + 2) => μ)
  exact hdiv

theorem integral_looEstimate_eq_independent_test
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    (∫ D : Dataset (Observation k m) (n + 2),
      looEstimate T L D ∂Measure.pi fun _ : Fin (n + 2) => μ) =
    ∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
      fittedLoss T L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  change (∫ D : Dataset (Observation k m) (n + 2),
    (∑ i : Fin (n + 2), fittedLoss T L (deleteAt D i) (D i)) / (n + 2)
      ∂Measure.pi fun _ : Fin (n + 2) => μ) = _
  rw [integral_div]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_heldout_fittedLoss μ T L i hf)]
  simp_rw [integral_heldout_fittedLoss μ T L _ hf]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  simp [hn]

end LOOConcentration
