import LOOConcentrationRevision.Probability.ObservationZeroLsi
import LOOConcentrationRevision.Probability.ZeroDimensional

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Conditional internal event assembly: actual centered almost-everywhere
constancy and the raw bias give all three original-law zero tails. -/
theorem original_tails_eq_zero_of_centered_ae_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (H : α → ℝ) (δ : NNReal)
    (hcenter : (fun x => H x-∫ y, H y ∂μ) =ᵐ[μ] fun _ => (0:ℝ))
    (hbias : |∫ y, H y ∂μ| ≤ (δ:ℝ))
    (ε : ℝ) (hε : (δ:ℝ) < ε) :
    μ.real {x | H x > ε} = 0 ∧ μ.real {x | -H x > ε} = 0 ∧
      μ.real {x | |H x| > ε} = 0 := by
  have habs : ∀ᵐ x ∂μ, |H x| ≤ (δ:ℝ) := by
    filter_upwards [hcenter] with x hx
    have heq : H x = ∫ y, H y ∂μ := by
      change H x-∫ y, H y ∂μ = 0 at hx
      linarith
    rw [heq]
    exact hbias
  have hp : μ {x | H x > ε} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [habs] with x hx
    change ¬ ε < H x
    have hu := (abs_le.mp hx).2
    linarith
  have hm : μ {x | -H x > ε} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [habs] with x hx
    change ¬ ε < -H x
    have hl := (abs_le.mp hx).1
    linarith
  have ha : μ {x | |H x| > ε} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [habs] with x hx
    change ¬ ε < |H x|
    linarith
  exact ⟨by simp only [Measure.real, hp, ENNReal.toReal_zero],
    by simp only [Measure.real, hm, ENNReal.toReal_zero],
    by simp only [Measure.real, ha, ENNReal.toReal_zero]⟩

/-- The actual zero-LSI observation endpoint supplies centered constancy
internally on every ordered dataset law. -/
theorem observation_zero_lsi_original_tails_eq_zero
    {k m r : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hzero : observationLogSobolevConstant μ = 0)
    (H : Dataset (Observation k m) r → ℝ) (hH : Measurable H)
    (δ : NNReal) (hbias : |∫ D, H D ∂Measure.pi fun _ : Fin r => μ| ≤ (δ:ℝ))
    (ε : ℝ) (hε : (δ:ℝ) < ε) :
    let P := Measure.pi fun _ : Fin r => μ
    P.real {D | H D > ε} = 0 ∧ P.real {D | -H D > ε} = 0 ∧
      P.real {D | |H D| > ε} = 0 := by
  have hEndpoint := observation_zero_lsi_product_bias_endpoint μ hzero H hH (δ:ℝ) δ.property hbias
  have hcenter : (fun D => H D-∫ E, H E ∂Measure.pi fun _ : Fin r => μ)
      =ᵐ[Measure.pi fun _ : Fin r => μ] fun _ => (0:ℝ) := by
    filter_upwards [hEndpoint.1] with D hD
    simp only [hD, sub_self]
  exact original_tails_eq_zero_of_centered_ae_eq_zero _ H δ hcenter hbias ε hε

/-- The accepted empty-coordinate source endpoint supplies the same raw zero
bounds without adding a dimension or positive-constant premise. -/
theorem zeroDimensional_original_tails_eq_zero
    {r : ℕ} (μ : Measure (Observation 0 0)) [IsProbabilityMeasure μ]
    (H : Dataset (Observation 0 0) r → ℝ) (hH : Measurable H)
    (δ : NNReal) (hbias : |∫ D, H D ∂Measure.pi fun _ : Fin r => μ| ≤ (δ:ℝ))
    (ε : ℝ) (hε : (δ:ℝ) < ε) :
    let P := Measure.pi fun _ : Fin r => μ
    P.real {D | H D > ε} = 0 ∧ P.real {D | -H D > ε} = 0 ∧
      P.real {D | |H D| > ε} = 0 := by
  exact original_tails_eq_zero_of_centered_ae_eq_zero _ H δ
    (zeroDimensional_observation_product_statistic μ r H hH) hbias ε hε

end LOOConcentration.Revision
