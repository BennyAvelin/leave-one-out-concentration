import LOOConcentrationRevision.Probability.ConditionalMeanBound
import LOOConcentration.Geometry.NormTransport

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The actual data-dependent root's mean bound, on its literal ordered
product law and normalized event restriction. All premises are root inputs. -/
theorem dataDependent_normalized_mean_abs_le {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (H : Dataset (Observation k m) (n + 2) → ℝ) (hH : Measurable H)
    (B δ : NNReal)
    (hL2 : eLpNorm H 2 (Measure.pi fun _ : Fin (n + 2) => μ) ≤ (B : ENNReal))
    (hbias : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ (δ : ℝ))
    (K : Set (Dataset (Observation k m) (n + 2))) (hK : MeasurableSet K)
    (hKpos : 0 < (Measure.pi fun _ : Fin (n + 2) => μ) K) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    |∫ D, H D ∂normalizedRestriction ν K| ≤
      (δ : ℝ) + (B : ℝ) * Real.sqrt (ν.real Kᶜ / (1 - ν.real Kᶜ)) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  have hq : 0 < ν.real K :=
    ENNReal.toReal_pos (ne_of_gt hKpos) (measure_ne_top ν K)
  exact normalized_mean_abs_le_of_eLpNorm_le ν H hH B δ hL2 hbias K hK hq

end LOOConcentration.Revision
