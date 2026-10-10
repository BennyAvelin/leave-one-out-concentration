import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1UniformSourceInputs
import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1ZeroLsi
import LOOConcentrationRevision.Concentration.Chernoff

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

/-- Both source theta tails for the actual signed I₁, with the native zero-LSI endpoint. -/
theorem modelSelection_actual_signed_i1_uniform_theta_tails
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
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
    (a b : NNReal)
    (hBound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ))
    (t : ℝ) (ht : 0 < t) :
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
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let θ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) t ht
      a b a.property b.property
    P.real {D | I₁ D > t} ≤ θ ∧ P.real {D | -I₁ D > t} ≤ θ := by
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
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let θ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) t ht
    a b a.property b.property
  change P.real {D | I₁ D > t} ≤ θ ∧ P.real {D | -I₁ D > t} ≤ θ
  have hShort := modelSelection_actual_signed_short_centering μ T₀ T₁ L hJoint hHeld
  have hMeanZero : (∫ D, I₁ D ∂P) = 0 := hShort.2.2.2.2.2.2.2
  have ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) := hBound.mono fun z hz => hz.1
  have hb : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ (b : ℝ) := hBound.mono fun z hz => hz.2
  by_cases hLCzero : observationLogSobolevConstant μ = 0
  · have hzero := modelSelection_actual_signed_I1_zero_lsi (n := n) μ T₀ T₁ L hLCzero t ht
    constructor
    · simpa only [C, θ, hLCzero, ENNReal.toReal_zero, Revision.thetaRate, if_true] using hzero.2.2.1.le
    · simpa only [C, θ, hLCzero, ENNReal.toReal_zero, Revision.thetaRate, if_true] using hzero.2.2.2.le
  · have hCpos : 0 < C := by
      have hCnonneg : 0 ≤ C := ENNReal.toReal_nonneg
      by_contra hn
      have hCzero : C = 0 := le_antisymm (le_of_not_gt hn) hCnonneg
      have hh : observationLogSobolevConstant μ = 0 ∨ observationLogSobolevConstant μ = ⊤ :=
        (ENNReal.toReal_eq_zero_iff _).mp hCzero
      rcases hh with hz | hinf
      · exact hLCzero hz
      · exact hfinite hinf
    have hGaussian : (b : ℝ) = 0 → ∀ s : ℝ,
        Integrable (fun D => Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P))) P ∧
        (∫ D, Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P)) ∂P) ≤
          Real.exp ((C * (a : ℝ)^2 / 2) * s^2) := by
      intro hbzero s
      have hδzero : ∀ᵐ z ∂μ, δ₂ (n + 1) z = 0 := by
        filter_upwards [hb] with z hz
        exact le_antisymm (by simpa only [hbzero] using hz) (hδ₂_nonneg z)
      have hmgf := modelSelection_actual_signed_i1_bounded_source_inputs μ T₀ T₁ L δ₁ δ₂
        hfinite hM₂ hJoint hHeld hMeanLoc hLoc hGrad a a.property ha hδzero s
      change Integrable (fun D => Real.exp (s * I₁ D)) P ∧
        (∫ D, Real.exp (s * I₁ D) ∂P) ≤ Real.exp ((C * (a : ℝ)^2 / 2) * s^2) at hmgf
      simpa only [hMeanZero, sub_zero] using hmgf
    have hCutoff : 0 < (b : ℝ) → ∀ s : ℝ, |s| ≤ 1/(4*C*(b : ℝ)) →
        Integrable (fun D => Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P))) P ∧
        (∫ D, Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P)) ∂P) ≤
          Real.exp ((2*C*((a : ℝ)^2+2*(b : ℝ)^2*((n+1 : ℕ) : ℝ)*M₂))*s^2) := by
      intro hbpos s hcut
      have hmgf := modelSelection_actual_signed_i1_positive_growth_source_inputs μ T₀ T₁ L δ₁ δ₂
        hfinite hM₂ hJoint hHeld hMeanLoc hLoc hGrad a b a.property b.property hbpos ha hb s hcut
      change Integrable (fun D => Real.exp (s * I₁ D)) P ∧
        (∫ D, Real.exp (s * I₁ D) ∂P) ≤
          Real.exp ((2*C*((a : ℝ)^2+2*(b : ℝ)^2*((n+1 : ℕ) : ℝ)*M₂))*s^2) at hmgf
      simpa only [hMeanZero, sub_zero] using hmgf
    have htails := Revision.chernoff_revision_thetaRate_of_quadraticMGF P I₁ C M₂ hCpos
      (integral_nonneg observationNormSq_nonneg) (n+1) (by omega) t ht a b a.property b.property
      hGaussian hCutoff
    simpa only [hMeanZero, sub_zero, zero_sub] using htails

end LOOConcentration.Manuscript.Internal
