import LOOConcentrationRevision.Probability.DiracProduct

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter

/-- The product identity supplies the actual Dirac mean consumer without an integrability premise. -/
theorem product_dirac_statistic_ae_eq_mean {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (H : (ι → α) → ℝ) (hH : Measurable H) :
    H =ᵐ[Measure.pi fun _ : ι => Measure.dirac a]
      (fun _ => ∫ x, H x ∂Measure.pi fun _ : ι => Measure.dirac a) := by
  rw [measure_pi_dirac]
  exact (dirac_integrable_statistic_ae_eq_mean hH (integrable_dirac (by finiteness))).1

/-- Centering a measurable real statistic under the Dirac product gives zero almost surely. -/
theorem product_dirac_centered_statistic_ae_eq_zero {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (H : (ι → α) → ℝ) (hH : Measurable H) :
    (fun x => H x - ∫ y, H y ∂Measure.pi fun _ : ι => Measure.dirac a)
      =ᵐ[Measure.pi fun _ : ι => Measure.dirac a] (fun _ => 0) := by
  filter_upwards [product_dirac_statistic_ae_eq_mean a H hH] with x hx
  rw [hx, sub_self]

end LOOConcentration.Revision
