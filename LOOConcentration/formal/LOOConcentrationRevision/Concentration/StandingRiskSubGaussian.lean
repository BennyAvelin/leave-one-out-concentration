import LOOConcentrationRevision.Probability.LooRiskCharacterizedMean
import LOOConcentrationRevision.Concentration.ExpectedRiskGradientConsumer
import LOOConcentrationRevision.Concentration.DatasetLipschitzHerbst
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped Gradient

/-- The literal full-fit risk has the source-rate subgaussian MGF when the
second growth rate vanishes. -/
theorem standing_risk_hasSubgaussianMGF
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d)
    (hδ₂zero : ∀ z, δ₂ (n + 2) z = 0) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun D : Dataset (Observation k m) (n + 2) =>
        (looRiskL1 μ (T (n + 1)) loss (hSt.stable.integrable_full n)) D -
          ∫ E, (looRiskL1 μ (T (n + 1)) loss
            (hSt.stable.integrable_full n)) E ∂(Measure.pi fun _ : Fin (n + 2) => μ))
      (NNReal.mk
        ((observationLogSobolevConstant μ).toReal *
          (∫ z, δ₁ (n + 2) z ∂μ) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q := datasetLawOfObservation (r := n + 2) μ
  let hf := hSt.stable.integrable_full n
  let H : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => (looRiskL1 μ (T (n + 1)) loss hf) D
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ :=
    fun x => ∫ z, fittedLoss (T (n + 1)) loss (datasetOfEuclidean x) z ∂μ
  let a : ℝ := ∫ z, δ₁ (n + 2) z ∂μ
  have ha : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg fun z => hSt.stable.delta₁_nonneg (n + 1) z
  let rate : NNReal := ⟨a, ha⟩
  have hrate : (rate : ℝ) = a := rfl
  have hδ₂int : (∫ z, δ₂ (n + 2) z ∂μ) = 0 := by
    simp [hδ₂zero]
  have hsource := standing_expected_full_loss_gradient
    (n := n) μ T loss δ₁ δ₂ δ₃ c d hSt
  have hlocal : LocallyLipschitz F := by
    simpa only [F] using hsource.2.1
  have hgrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (rate : ℝ) := by
    filter_upwards [hsource.2.2] with x hx
    have hx' : DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ a := by
      simpa [F, a, hδ₂int] using hx
    exact ⟨hx'.1, hx'.2.trans_eq hrate.symm⟩
  have hgrad' : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ (rate : ℝ) + (0 : NNReal) * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    simpa using hx
  have hseg (x y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2))) :
      |F x - F y| ≤ ‖x - y‖ * (rate : ℝ) := by
    simpa only [NNReal.coe_zero, zero_mul, add_zero, zero_div, mul_zero] using
      ae_gradient_segment_estimate F hlocal rate 0 hgrad' x y
  have hLip : LipschitzWith rate F := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    simpa only [Real.norm_eq_abs, mul_comm] using hseg x y
  have hmgfQ := dataset_lipschitz_hasSubgaussianMGF μ hSt.lsi
    hSt.second_moment F rate hLip
  have hrep : (fun D => H D) =ᵐ[P]
      (fun D => F (datasetToEuclidean D)) := by
    change (fun D => (looRiskL1 μ (T (n + 1)) loss hf) D) =ᵐ[P]
      (fun D => ∫ z, fittedLoss (T (n + 1)) loss D z ∂μ)
    exact hf.integral_prod_left.coeFn_toL1
  have hMeanJoint : (∫ D, H D ∂P) =
      ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) loss p.1 p.2 ∂(P.prod μ) :=
    looRiskL1_mean_eq_joint_of_characterization μ (T (n + 1)) loss hf
  have hFMeanJoint : (∫ D, F (datasetToEuclidean D) ∂P) =
      ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) loss p.1 p.2 ∂(P.prod μ) := by
    change (∫ D, ∫ z, fittedLoss (T (n + 1)) loss D z ∂μ ∂P) = _
    exact (integral_prod (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss (T (n + 1)) loss p.1 p.2) hf).symm
  have hmeanH : (∫ D, H D ∂P) = ∫ D, F (datasetToEuclidean D) ∂P :=
    hMeanJoint.trans hFMeanJoint.symm
  have hmeanF : (∫ x, F x ∂Q) =
      ∫ D, F (datasetToEuclidean D) ∂P := by
    change (∫ x, F x ∂(P.map datasetToEuclidean)) = _
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hLip.continuous.aestronglyMeasurable
  have hrawQ := ProbabilityTheory.HasSubgaussianMGF.of_map
    measurable_datasetToEuclidean.aemeasurable hmgfQ
  have hraw : ProbabilityTheory.HasSubgaussianMGF
      (fun D => F (datasetToEuclidean D) -
        ∫ E, F (datasetToEuclidean E) ∂P)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal *
        (rate : ℝ) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun D => F (datasetToEuclidean D) - ∫ x, F x ∂Q) _ P at hrawQ
    rw [hmeanF] at hrawQ
    exact hrawQ
  have hmean : (∫ x, F x ∂Q) = ∫ E, H E ∂P :=
    hmeanF.trans hmeanH.symm
  have hcenter : (fun D => F (datasetToEuclidean D) -
        ∫ E, F (datasetToEuclidean E) ∂P) =ᵐ[P]
      (fun D => H D - ∫ E, H E ∂P) := by
    filter_upwards [hrep] with D hD
    rw [← hD, hmeanH]
  have hresult := hraw.congr hcenter
  change ProbabilityTheory.HasSubgaussianMGF
    (fun D => H D - ∫ E, H E ∂P)
    (NNReal.mk ((observationLogSobolevConstant μ).toReal * a ^ 2)
      (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P
  simpa only [hrate] using hresult

end LOOConcentration.Revision
