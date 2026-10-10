import LOOConcentrationManuscript.Internal.RidgeConditionalStandingAssembly
import LOOConcentrationRevision.Frozen.Results.MainConcentration

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

/-- Real downstream conditional main-theorem consumer of the actual Ridge
standing assembly. The only source proof gate is the named ordered bias
premise; it must be produced internally before source-node certification. -/
theorem ridge_actual_main_tails_of_ordered_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (b δ : {t : ℝ // 0 < t}) (B : ℝ) (hB : 0 ≤ B)
    (hBias : ∀ n (i : Fin (n + 2)),
      |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2),
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n)
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|)
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi (fun _ : Fin (n + 2) => μ)) -
        (∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
            LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (n + 1))
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|) p.1 p.2
            ∂(Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ)| ≤ B / (n + 2 : ℝ)) :
    let T := fun r => LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
    let L := fun u v : Fin 1 → ℝ => |u 0 - v 0|
    let σ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, LOOConcentration.observationNormSq z ∂μ
    let Θ := fun (r : ℕ) (t a b : ℝ) =>
      if σ = 0 then 0 else
      if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
        if b = 0 then 0 else Real.exp (-(t / (8 * σ * b)))
      else if b = 0 then
        Real.exp (-(t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
      else Real.exp (-(min
        (t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
        (t / (8 * σ * b))))
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N z => C * (1 + |z.1 0|) / Real.sqrt (N : ℝ))
        (fun N _ => C / (N : ℝ)) (fun N => B / (N : ℝ)) M 0,
      ∀ ε : ℝ, 3 * (B / (n + 2 : ℝ)) < ε →
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
            (hStanding.stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
        let rhs := (n + 2 : ℝ) * (∫ z, Θ (n + 1) (ε / 3)
            (C * (1 + |z.1 0|) / Real.sqrt (n + 1 : ℝ)) (C / (n + 1 : ℝ)) ∂μ) +
          Θ (n + 2) (ε / 3) (M / Real.sqrt (n + 2 : ℝ)) 0 +
          Θ (n + 2) (ε / 3 - B / (n + 2 : ℝ))
            (C * (1 + ∫ z, |z.1 0| ∂μ) / Real.sqrt (n + 2 : ℝ)) (C / (n + 2 : ℝ))
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤ rhs ∧
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤ rhs := by
  intro T L σ M₂ Θ
  obtain ⟨C, hC, M, hM, hAll⟩ :=
    ridge_actual_complete_standing_of_ordered_bias μ hSecond hLSI b δ B hB hBias
  refine ⟨C, hC, M, hM, ?_⟩
  intro n
  refine ⟨hAll n, ?_⟩
  intro ε hε
  have hε' : 3 * (B / ((n + 2 : ℕ) : ℝ)) < ε := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hε
  have hMain := (LOOConcentration.Revision.mainConcentration μ T L
    (fun N z => C * (1 + |z.1 0|) / Real.sqrt (N : ℝ))
    (fun N _ => C / (N : ℝ)) (fun N => B / (N : ℝ)) M 0 (hAll n) ε hε').1
  have hY1 := (iidResponse_full_and_deleted_absolute_mean μ hSecond).1
  have hX4 := (observation_nativeLSI_feature_fourth_moment μ hLSI hSecond).2
  have hX1 := (ridge_actual_first_moment_feature_sq_source μ hX4 hY1).1
  have hMeanA : (∫ z : LOOConcentration.Observation 1 1,
      C * (1 + |z.1 0|) / Real.sqrt ((n + 2 : ℕ) : ℝ) ∂μ) =
      C * (1 + ∫ z, |z.1 0| ∂μ) / Real.sqrt (n + 2 : ℝ) := by
    rw [integral_div, integral_const_mul, integral_add (integrable_const (1 : ℝ)) hX1]
    simp only [integral_const, probReal_univ, one_smul, Nat.cast_add, Nat.cast_ofNat]
  have hMeanA' : (∫ z : LOOConcentration.Observation 1 1,
      C * (1 + |z.1 0|) / Real.sqrt (n + 2 : ℝ) ∂μ) =
      C * (1 + ∫ z, |z.1 0| ∂μ) / Real.sqrt (n + 2 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hMeanA
  dsimp only [σ, M₂, Θ]
  simpa only [LOOConcentration.Revision.thetaRate, hMeanA',
    integral_const, probReal_univ, one_smul, zero_div, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] using hMain

end LOOConcentration.Manuscript.Internal
