import LOOConcentration.Concentration.Chernoff
import LOOConcentrationRevision.Frozen.Definitions.ThetaRate

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- On the positive-constant branch the historical and revised literal rates
agree, with every parameter and denominator preserved. -/
theorem thetaRate_eq_historical_of_pos
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    thetaRate C M₂ hC.le hM₂ r hr t ht a b ha hb =
      LOOConcentration.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
  simp only [thetaRate, LOOConcentration.thetaRate, if_neg (ne_of_gt hC)]

/-- The genuine exponential Markov/Chernoff consumer returns the revised rate
on the positive branch; its MGF producers remain explicit internal inputs. -/
theorem chernoff_revision_thetaRate_of_quadraticMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmgf_gaussian : b = 0 → ∀ s : ℝ,
      Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂μ))) μ ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
          Real.exp ((C * a ^ 2 / 2) * s ^ 2))
    (hmgf_cutoff : 0 < b → ∀ s : ℝ, |s| ≤ 1 / (4 * C * b) →
      Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂μ))) μ ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
          Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2)) :
    let θ := thetaRate C M₂ hC.le hM₂ r hr t ht a b ha hb
    μ.real {x | F x - ∫ y, F y ∂μ > t} ≤ θ ∧
      μ.real {x | ∫ y, F y ∂μ - F x > t} ≤ θ := by
  dsimp only
  rw [thetaRate_eq_historical_of_pos C M₂ hC hM₂ r hr t ht a b ha hb]
  exact LOOConcentration.chernoff_thetaRate_of_quadraticMGF
    μ F C M₂ hC hM₂ r hr t ht a b ha hb hmgf_gaussian hmgf_cutoff

end LOOConcentration.Revision
