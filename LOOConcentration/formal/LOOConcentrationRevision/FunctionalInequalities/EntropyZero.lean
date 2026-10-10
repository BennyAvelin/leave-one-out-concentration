import LOOConcentrationRevision.FunctionalInequalities.EntropyComputation

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Strict Jensen identifies the square of an entropy-zero L2 function a.e.
It does not assert the function itself is constant without a sign premise. -/
theorem square_ae_eq_mean_of_squareEntropy_eq_zero (f : Lp ℝ 2 μ)
    (hzero : squareEntropy μ f = 0) :
    (fun x => (f x)^2) =ᵐ[μ] (fun _ => ∫ x, (f x)^2 ∂μ) := by
  have hf : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ :=
    (squareEntropy_lt_top_iff_integrable_density f).mp (by rw [hzero]; exact bot_lt_top)
  have hupper : (∫ x, (f x)^2 * Real.log ((f x)^2) ∂μ) ≤
      (∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ) := by
    have h := hzero
    rw [squareEntropy_eq_of_integrable_density f hf, ENNReal.ofReal_eq_zero] at h
    exact sub_nonpos.mp h
  have hJ := Real.strictConvexOn_mul_log.ae_eq_const_or_map_average_lt
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Eventually.of_forall fun x => sq_nonneg (f x)) (integrable_sq f) hf
  simp only [average_eq_integral] at hJ
  rcases hJ with h | h
  · exact h
  · exact False.elim (not_lt_of_ge hupper h)

/-- A fixed sign discharges the square ambiguity in the strict Jensen consumer. -/
theorem ae_eq_sqrt_mean_of_squareEntropy_eq_zero (f : Lp ℝ 2 μ)
    (hzero : squareEntropy μ f = 0) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x) :
    f =ᵐ[μ] (fun _ => Real.sqrt (∫ x, (f x)^2 ∂μ)) := by
  filter_upwards [square_ae_eq_mean_of_squareEntropy_eq_zero f hzero, hnonneg] with x hs hx
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

end LOOConcentration.Revision
