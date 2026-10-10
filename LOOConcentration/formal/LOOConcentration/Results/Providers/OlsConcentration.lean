import LOOConcentration.Examples.GaussianLogSobolev
import LOOConcentration.Examples.OlsObservationTailProducer
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration.Providers

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
  intro ε hε
  obtain ⟨Cε, cε, hCε, hcε, Nε, htail⟩ :=
    olsConcentration_of_hasLogSobolev gaussianObservationLaw_hasLogSobolev ε hε
  refine ⟨Cε, cε, hCε, hcε, Nε, ?_⟩
  intro α β n hN
  let γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let μ : Measure (ℝ × ℝ) :=
    (γ.prod γ).map (fun p : ℝ × ℝ => (p.1, α + β * p.1 + p.2))
  let ν : Measure (Fin (n + 3) → ℝ × ℝ) := Measure.pi fun _ => μ
  let R : (Fin (n + 3) → ℝ × ℝ) → ℝ := fun D =>
    ∫ z, |olsPrediction D z.1 - z.2| ∂μ
  let V : (Fin (n + 3) → ℝ × ℝ) → ℝ := fun D =>
    (∑ i : Fin (n + 3),
      |olsPrediction (deleteAt D i) (D i).1 - (D i).2|) / (n + 3 : ℝ)
  have hsample : ν = olsAffineResponseLaw (n + 3) α β := by
    simpa only [ν, μ, γ] using
      olsAffineResponseLaw_eq_frozenResponseLaw (n + 3) α β
  calc
    ν.real {D | |R D - V D| > ε} =
        (olsAffineResponseLaw (n + 3) α β).real
          {D | |olsResponseError α β D| > ε} := by
      rw [hsample]
      congr 1
    _ ≤ Cε * (n + 3 : ℝ) * Real.exp (-(cε * (n + 3 : ℝ))) :=
      htail α β n hN

#print axioms olsConcentration

end LOOConcentration.Providers
