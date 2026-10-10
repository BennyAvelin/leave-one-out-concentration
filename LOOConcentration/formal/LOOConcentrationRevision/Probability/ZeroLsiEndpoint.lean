import LOOConcentrationRevision.Probability.DiracConsumer
import LOOConcentrationRevision.FunctionalInequalities.ZeroLsiPointmass

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal

/-- The zero-constant endpoint uses the Dirac product, with the supplied bias
threshold. Centered moments vanish for every exponent, without division by C. -/
theorem product_dirac_bias_endpoint {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (H : (ι → α) → ℝ) (hH : Measurable H)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (hmean : |∫ x, H x ∂Measure.pi fun _ : ι => Measure.dirac a| ≤ δ) :
    let ν := Measure.pi fun _ : ι => Measure.dirac a
    H =ᵐ[ν] (fun _ => ∫ x, H x ∂ν) ∧
      (∀ r : ℝ≥0∞, eLpNorm (fun x => H x - ∫ y, H y ∂ν) r ν = 0) ∧
      (∀ ε : ℝ, δ < ε → ν.real {x | ε < H x} = 0 ∧
        ν.real {x | ε < -H x} = 0) := by
  dsimp only
  refine ⟨product_dirac_statistic_ae_eq_mean a H hH, ?_, ?_⟩
  · intro r
    rw [eLpNorm_congr_ae (product_dirac_centered_statistic_ae_eq_zero a H hH)]
    simp
  · intro ε hε
    have hzeroPlus : (Measure.pi fun _ : ι => Measure.dirac a) {x | ε < H x} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [product_dirac_statistic_ae_eq_mean a H hH] with x hx
      rw [hx]
      exact not_lt_of_ge (le_trans (abs_le.mp hmean).2 hε.le)
    have hzeroMinus : (Measure.pi fun _ : ι => Measure.dirac a) {x | ε < -H x} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [product_dirac_statistic_ae_eq_mean a H hH] with x hx
      rw [hx]
      have h := (abs_le.mp hmean).1
      exact not_lt_of_ge (by linarith)
    exact ⟨by rw [Measure.real, hzeroPlus, ENNReal.toReal_zero],
      by rw [Measure.real, hzeroMinus, ENNReal.toReal_zero]⟩

/-- The point-mass theorem produces the Dirac witness for the same observation
law, then the product endpoint consumes that law without another hypothesis. -/
theorem zero_lsi_product_bias_endpoint {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hzero : logSobolevConstant μ = 0)
    (H : (κ → EuclideanSpace ℝ ι) → ℝ) (hH : Measurable H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : |∫ x, H x ∂Measure.pi fun _ : κ => μ| ≤ δ) :
    let ν := Measure.pi fun _ : κ => μ
    H =ᵐ[ν] (fun _ => ∫ x, H x ∂ν) ∧
      (∀ r : ℝ≥0∞, eLpNorm (fun x => H x - ∫ y, H y ∂ν) r ν = 0) ∧
      (∀ ε : ℝ, δ < ε → ν.real {x | ε < H x} = 0 ∧
        ν.real {x | ε < -H x} = 0) := by
  obtain ⟨a, ha⟩ := exists_dirac_of_logSobolevConstant_eq_zero μ hzero
  subst μ
  exact product_dirac_bias_endpoint a H hH δ hδ hmean

end LOOConcentration.Revision
