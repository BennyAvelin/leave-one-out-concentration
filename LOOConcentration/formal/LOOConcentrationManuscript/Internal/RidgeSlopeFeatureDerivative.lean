import LOOConcentrationManuscript.ProductDerivativeCovarianceConsumer
import LOOConcentrationManuscript.RidgeVarianceCoordinateDerivativeConsumer
import LOOConcentrationManuscript.Internal.PositiveQuotientDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The actual scalar-dataset feature-coordinate derivative of the stabilized
ridge slope. The numerator and denominator are the literal empirical
covariance and variance along `varyFeature`, with clipped responses held fixed.
-/

namespace LOOConcentration.Manuscript.Internal

/-- Feature-coordinate derivative of the source's literal ridge slope for an
actual scalar dataset. The response coordinates remain fixed under the feature
update; no differentiability of the clipping map is needed. -/
theorem clippedDataset_ridgeSlope_feature_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ : ℝ) (hδ : 0 < δ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let beta : ℝ := s / (v + δ)
    HasDerivAt
      (fun t : ℝ =>
        let Dt := LOOConcentrationManuscript.varyFeature D j t
        let Xt := LOOConcentrationManuscript.featureValues Dt
        let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b
        ((∑ i : Fin (r + 1),
          (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) *
            (Ut i - (∑ k : Fin (r + 1), Ut k) * N⁻¹)) * N⁻¹) /
          (((∑ i : Fin (r + 1),
            (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) ^ 2) * N⁻¹) + δ))
      ((U j - c - 2 * beta * (X j - a)) / (N * (v + δ)))
      (X j) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b
  let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
  let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
  let beta : ℝ := s / (v + δ)
  let C : ℝ → ℝ := fun t : ℝ =>
    let Dt := LOOConcentrationManuscript.varyFeature D j t
    let Xt := LOOConcentrationManuscript.featureValues Dt
    let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b
    (∑ i : Fin (r + 1),
      (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) *
        (Ut i - (∑ k : Fin (r + 1), Ut k) * N⁻¹)) * N⁻¹
  let V : ℝ → ℝ := fun t : ℝ =>
    let Dt := LOOConcentrationManuscript.varyFeature D j t
    let Xt := LOOConcentrationManuscript.featureValues Dt
    (∑ i : Fin (r + 1),
      (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) ^ 2) * N⁻¹
  let B : ℝ → ℝ := fun t : ℝ => V t + δ
  change HasDerivAt (fun t : ℝ => C t / B t)
    ((U j - c - 2 * beta * (X j - a)) / (N * (v + δ))) (X j)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hupdate : LOOConcentrationManuscript.varyFeature D j (X j) = D := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [X, LOOConcentrationManuscript.varyFeature,
        LOOConcentrationManuscript.featureValues]
    · simp [LOOConcentrationManuscript.varyFeature, hij]
  have hC : HasDerivAt C ((U j - c) / N) (X j) := by
    simpa [C, U, c, N] using
      LOOConcentrationManuscript.clippedDatasetCovariance_feature_hasDerivAt r D j b
  have hV : HasDerivAt V
      (2 * (X j - a) * N⁻¹) (X j) := by
    simpa [V, X, a, N] using
      LOOConcentrationManuscript.actualDatasetFeatureVariance_feature_hasDerivAt r D j
  have hB : HasDerivAt B (2 * (X j - a) * N⁻¹) (X j) := by
    simpa [B] using hV.add_const δ
  have hC0 : C (X j) = s := by
    simp only [C, X]
    rw [hupdate]
  have hV0 : V (X j) = v := by
    simp only [V, X]
    rw [hupdate]
  have hv : 0 ≤ v := by
    dsimp [v]
    exact mul_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg (X i - a))
      (inv_nonneg.mpr hN.le)
  have hpos : 0 < B (X j) := by
    change 0 < V (X j) + δ
    rw [hV0]
    exact add_pos_of_nonneg_of_pos hv hδ
  have hquotF :=
    LOOConcentration.Manuscript.Internal.positiveDenominator_quotient_hasFDerivAt
      C B _ _ (X j)
      hC.hasFDerivAt hB.hasFDerivAt hpos
  have hquot := hquotF.hasDerivAt
  convert hquot using 1
  · simp only [smul_apply, sub_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
    rw [hC0]
    simp only [B, hV0]
    dsimp [beta]
    have hvδ : 0 < v + δ := add_pos_of_nonneg_of_pos hv hδ
    field_simp [hN.ne', hvδ.ne']

end LOOConcentration.Manuscript.Internal
