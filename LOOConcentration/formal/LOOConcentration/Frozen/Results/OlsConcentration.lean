import LOOConcentration.Frozen.Examples.OlsPrediction
import LOOConcentration.Frozen.Foundations.DeleteAt
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LOOConcentration.Results.Providers.OlsConcentration

set_option autoImplicit false
namespace LOOConcentration
open MeasureTheory

theorem olsConcentration :
    ∀ (ε : ℝ) (hε : 0 < ε),
      ∃ Cε cε : ℝ, 0 < Cε ∧ 0 < cε ∧
      ∃ Nε : ℕ, ∀ (α β : ℝ) (n : ℕ), Nε ≤ n + 3 →
        let γ := ProbabilityTheory.gaussianReal 0 1
        let μ : MeasureTheory.Measure (ℝ × ℝ) :=
          (γ.prod γ).map (fun p : ℝ × ℝ => (p.1, α + β * p.1 + p.2))
        let ν := MeasureTheory.Measure.pi fun _ : Fin (n + 3) => μ
        let R := fun D : Fin (n + 3) → ℝ × ℝ =>
          ∫ z, |olsPrediction D z.1 - z.2| ∂μ
        let V := fun D : Fin (n + 3) → ℝ × ℝ =>
          (∑ i : Fin (n + 3),
            |olsPrediction (deleteAt D i) (D i).1 - (D i).2|) / (n + 3 : ℝ)
        ν.real {D | |R D - V D| > ε} ≤
          Cε * (n + 3 : ℝ) * Real.exp (-(cε * (n + 3 : ℝ))) := by
  exact LOOConcentration.Providers.olsConcentration

end LOOConcentration
