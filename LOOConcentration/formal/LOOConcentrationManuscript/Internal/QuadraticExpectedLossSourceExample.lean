import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanQuadraticRiskFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- The literal scalar quadratic example in the expected-loss segment remark.
The index `r` represents the positive sample size `r + 1`. -/
theorem quadratic_expectedLoss_source_example (m v : ℝ) (r : ℕ) (z : ℝ) :
    HasDerivAt (fun t : ℝ => (t - m) ^ 2 + v / (r + 1 : ℝ))
      (2 * (z - m)) z ∧
    |deriv (fun t : ℝ => (t - m) ^ 2 + v / (r + 1 : ℝ)) z| ≤
      2 * |m| + 2 * |z| := by
  have hd : HasDerivAt (fun t : ℝ => (t - m) ^ 2 + v / (r + 1 : ℝ))
      (2 * (z - m)) z := by
    simpa using (((hasDerivAt_id z).sub_const m).pow 2).add_const
      (v / (r + 1 : ℝ))
  refine ⟨hd, ?_⟩
  rw [hd.deriv, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |z - m| ≤ 2 * (|z| + |m|) :=
      mul_le_mul_of_nonneg_left (abs_sub z m) (by norm_num)
    _ = 2 * |m| + 2 * |z| := by ring

/-- The source example is consumed by the actual expected quadratic fitted
loss, using the approved risk formula for an independent sample. -/
theorem empiricalMean_expectedQuadraticLoss_source_example_consumer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) (z : ℝ) :
    HasDerivAt (fun t : ℝ =>
      ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - t) ^ 2 ∂P)
      (2 * (z - ∫ x : ℝ, x ∂μ)) z ∧
    |deriv (fun t : ℝ =>
      ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - t) ^ 2 ∂P) z| ≤
      2 * |∫ x : ℝ, x ∂μ| + 2 * |z| := by
  have hf : (fun t : ℝ =>
      ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - t) ^ 2 ∂P) =
      (fun t : ℝ => (t - ∫ x : ℝ, x ∂μ) ^ 2 +
        variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)) := by
    funext t
    exact empiricalMean_quadraticRisk_formula P μ hSecond r X hLaw hInd t
  rw [hf]
  exact quadratic_expectedLoss_source_example (∫ x : ℝ, x ∂μ)
    (variance (id : ℝ → ℝ) μ) r z

end LOOConcentration.Manuscript.Internal
