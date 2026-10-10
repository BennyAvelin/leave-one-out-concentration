import LOOConcentrationManuscript.Internal.MeanAbsoluteStandingAssembly
import LOOConcentrationManuscript.Internal.StandingMeanLossLipschitz
import LOOConcentrationManuscript.Internal.GenericTwoSidedSimplifiedAsymptotic
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Topology ENNReal

/-- A concrete source consumer for the response-only empirical mean. Its
standing assumptions come from the source moment and LSI hypotheses; both
conclusions use the original fresh-query risk and leave-one-out estimate. -/
theorem empiricalMean_actual_source_two_sided_sixN
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => LOOConcentration.Manuscript.empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    let δ₁ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 =>
      (Real.sqrt (N : ℝ))⁻¹
    let δ₂ := fun _N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (0 : ℝ)
    let δ₃ := fun N : ℕ =>
      2 * (∫ x : ℝ, |x| ∂μ) / ((N : ℝ) - 1)
    let c : ℕ → ℝ := fun _ => 1
    let d : ℕ → ℝ := fun _ => 0
    let hStanding : ∀ n, LOOConcentration.Revision.StandingAssumption
        (n := n) ν T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1)) := fun n =>
      LOOConcentration.Manuscript.Internal.empiricalMean_absoluteStanding_of_scalarLaw
        μ hSecond hFinite n
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
      let P := Measure.pi (fun _ : Fin (n + 2) => ν)
      let H := fun D =>
        (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
          ((hStanding n).stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
      P.real {D | |H D| > ε} ≤
        6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) ∧
      P.real {D | -H D > ε} ≤
        3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
  classical
  intro φ ν
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro T L δ₁ δ₂ δ₃ c d hStanding
  let C : NNReal := ⟨(LOOConcentration.Revision.observationLogSobolevConstant ν).toReal,
    ENNReal.toReal_nonneg⟩
  have hC :
      (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal = (C : ℝ) := rfl
  have hZero : ∀ n z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0 := by
    intro n z
    exact ⟨rfl, rfl⟩
  have hLip : ∀ n z w,
      |LOOConcentration.Revision.meanFittedLoss ν (T n) L z
          ((hStanding n).mean_integrable z) -
        LOOConcentration.Revision.meanFittedLoss ν (T n) L w
          ((hStanding n).mean_integrable w)| ≤ c (n + 1) *
          LOOConcentration.observationNorm (z - w) := by
    intro n z w
    exact LOOConcentration.Manuscript.Internal.standing_zero_d_mean_loss_lipschitz
      ν T L δ₁ δ₂ δ₃ 1 (hStanding n) z w
  have hc : ∀ n, c (n + 1) ≤ (1 : ℝ) := by
    intro n
    exact le_rfl
  have hδ₁ : ∀ n, ∀ᵐ z ∂ν,
      δ₁ (n + 1) z ≤ (1 : ℝ) / Real.sqrt (n + 1 : ℝ) ∧
      δ₁ (n + 2) z ≤ (1 : ℝ) / Real.sqrt (n + 2 : ℝ) := by
    intro n
    filter_upwards [] with z
    constructor
    · simp only [δ₁, Nat.cast_add, Nat.cast_one, one_div, le_rfl]
    · simp only [δ₁, Nat.cast_add, Nat.cast_ofNat, one_div, le_rfl]
  obtain ⟨c₀, hc₀, hGeneric⟩ :=
    LOOConcentration.Manuscript.Internal.generic_eventual_two_sided_sixN C 1 1
  refine ⟨c₀, hc₀, ?_⟩
  intro ε hε
  exact hGeneric 1 1 ν T L δ₁ δ₂ δ₃ c d hC hStanding hZero hLip hc hδ₁ ε hε

end LOOConcentration.Manuscript.Internal
