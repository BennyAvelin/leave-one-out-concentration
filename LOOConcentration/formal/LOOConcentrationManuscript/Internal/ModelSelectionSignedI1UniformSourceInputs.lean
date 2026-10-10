import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1UniformMgf
import LOOConcentrationManuscript.Internal.ModelSelectionSignedShortCenteringConsumer
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentration.Geometry.SmoothObservationSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open LOOConcentration.Revision
open scoped BigOperators

/-- Bounded-growth actual signed `I₁` from held-out and Euclidean-query inputs for two
estimators evaluated with the same loss and the original observation law. The
expected short loss and the `n + 2` holdout average are literal. -/
theorem modelSelection_actual_signed_i1_bounded_source_inputs
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hJoint : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ))
    (hMeanLoc : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (ObservationCoordinate k m) => ∫ E : Dataset (Observation k m) (n + 1),
        fittedLoss (T₀ n) L E (observationOfEuclidean x) -
          fittedLoss (T₁ n) L E (observationOfEuclidean x)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (hLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
        fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (a : ℝ) (ha : 0 ≤ a)
    (hδ₁ : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hδ₂zero : ∀ᵐ z ∂μ, δ₂ (n + 1) z = 0)
    (s : ℝ) :
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
    let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
    Integrable (fun D => Real.exp (s * I₁ D)) P ∧
      (∫ D, Real.exp (s * I₁ D) ∂P) ≤
        Real.exp (((observationLogSobolevConstant μ).toReal * a ^ 2 / 2) * s ^ 2) := by
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
  have hShort := modelSelection_actual_signed_short_centering μ T₀ T₁ L hJoint hHeld
  have hShortInt : Integrable F (Q.prod μ) := hShort.1
  have hMeanRawLoc : LocallyLipschitz f := by
    have h := hMeanLoc.comp
      (ContinuousLinearEquiv.lipschitz
        (LOOConcentration.observationCoordinateContinuousLinearEquiv (k := k) (m := m))).locallyLipschitz
    change LocallyLipschitz (fun z : Observation k m => ∫ E : Dataset (Observation k m) (n + 1),
      fittedLoss (T₀ n) L E (observationOfEuclidean (observationToEuclidean z)) -
        fittedLoss (T₁ n) L E (observationOfEuclidean (observationToEuclidean z)) ∂Q) at h
    simpa only [observationOfEuclidean_observationToEuclidean] using h
  have h := modelSelection_signed_i1_uniform_mgf_bounded μ T₀ T₁ L δ₁ δ₂
    hfinite hM₂ hJoint hShortInt hMeanRawLoc hLoc hGrad a ha hδ₁ hδ₂zero s
  simpa only [P, Q, F, f, I₁, Finset.sum_sub_distrib, sub_div, looEstimate, fittedLoss, Nat.cast_add, Nat.cast_ofNat] using h

/-- Positive-growth source-input consumer for the same literal signed
`I₁`; it preserves the short-sample second-moment factor and source cutoff. -/
theorem modelSelection_actual_signed_i1_positive_growth_source_inputs
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hJoint : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ))
    (hMeanLoc : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (ObservationCoordinate k m) => ∫ E : Dataset (Observation k m) (n + 1),
        fittedLoss (T₀ n) L E (observationOfEuclidean x) -
          fittedLoss (T₁ n) L E (observationOfEuclidean x)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (hLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
        fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbpos : 0 < b)
    (hδ₁ : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hδ₂ : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b)
    (s : ℝ)
    (hcut : |s| ≤ 1 /
      (4 * (observationLogSobolevConstant μ).toReal * b)) :
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
    let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
    Integrable (fun D => Real.exp (s * I₁ D)) P ∧
      (∫ D, Real.exp (s * I₁ D) ∂P) ≤
        Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
          (a ^ 2 + 2 * b ^ 2 * ((n + 1 : ℕ) : ℝ) *
            (∫ y, observationNormSq y ∂μ)) * s ^ 2)) := by
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
  have hShort := modelSelection_actual_signed_short_centering μ T₀ T₁ L hJoint hHeld
  have hShortInt : Integrable F (Q.prod μ) := hShort.1
  have hMeanRawLoc : LocallyLipschitz f := by
    have h := hMeanLoc.comp
      (ContinuousLinearEquiv.lipschitz
        (LOOConcentration.observationCoordinateContinuousLinearEquiv (k := k) (m := m))).locallyLipschitz
    change LocallyLipschitz (fun z : Observation k m => ∫ E : Dataset (Observation k m) (n + 1),
      fittedLoss (T₀ n) L E (observationOfEuclidean (observationToEuclidean z)) -
        fittedLoss (T₁ n) L E (observationOfEuclidean (observationToEuclidean z)) ∂Q) at h
    simpa only [observationOfEuclidean_observationToEuclidean] using h
  have h := modelSelection_signed_i1_uniform_mgf_positive_growth μ T₀ T₁ L δ₁ δ₂
    hfinite hM₂ hJoint hShortInt hMeanRawLoc hLoc hGrad a b ha hb hbpos hδ₁ hδ₂ s hcut
  simpa only [P, Q, F, f, I₁, Finset.sum_sub_distrib, sub_div, looEstimate, fittedLoss, Nat.cast_add, Nat.cast_ofNat] using h

end LOOConcentration.Manuscript.Internal
