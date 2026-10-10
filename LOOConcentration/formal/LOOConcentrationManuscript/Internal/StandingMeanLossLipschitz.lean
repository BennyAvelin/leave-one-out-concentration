import LOOConcentrationManuscript.Frozen.Bridges.ExpectedLossSegmentBound
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Geometry.CoordinateTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- An internal conditional consumer of a proved standing package with d=0.
Source applications must construct that package before using this lemma. -/
theorem standing_zero_d_mean_loss_lipschitz
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c : ℝ)
    (hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c 0)
    (z w : LOOConcentration.Observation k m) :
    |LOOConcentration.Revision.meanFittedLoss μ (T n) L z (hStanding.mean_integrable z) -
      LOOConcentration.Revision.meanFittedLoss μ (T n) L w (hStanding.mean_integrable w)| ≤
      c * LOOConcentration.observationNorm (z - w) := by
  let G := fun x : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
    LOOConcentration.Revision.meanFittedLoss μ (T n) L
      (LOOConcentration.Revision.observationOfEuclidean x)
      (hStanding.mean_integrable (LOOConcentration.Revision.observationOfEuclidean x))
  have hGrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
      (LOOConcentration.ObservationCoordinate k m))), ‖gradient G x‖ ≤ c + (0 : ℝ) * ‖x‖ := by
    filter_upwards [hStanding.mean_gradient] with x hx
    exact hx.2
  have h := expected_loss_segment_bound G hStanding.mean_locallyLipschitz
    ⟨c,hStanding.c_nonneg⟩ 0 hGrad
    (LOOConcentration.observationToEuclidean z) (LOOConcentration.observationToEuclidean w)
  have hSub : LOOConcentration.observationToEuclidean z -
      LOOConcentration.observationToEuclidean w =
      LOOConcentration.observationToEuclidean (z - w) := by
    ext i
    cases i <;> rfl
  have h' : |G (LOOConcentration.observationToEuclidean z) -
      G (LOOConcentration.observationToEuclidean w)| ≤
      ‖LOOConcentration.observationToEuclidean z - LOOConcentration.observationToEuclidean w‖ * c := by
    convert (by simpa only [NNReal.coe_zero, zero_div, zero_mul, add_zero] using h) using 1
    rfl
  simpa only [G, LOOConcentration.Revision.observationOfEuclidean_observationToEuclidean,
    hSub, ← LOOConcentration.observationNorm_eq_euclidean, mul_comm] using h'


end LOOConcentration.Manuscript.Internal
