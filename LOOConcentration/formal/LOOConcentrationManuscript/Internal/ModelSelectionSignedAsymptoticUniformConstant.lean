import LOOConcentrationManuscript.Internal.ModelSelectionSignedSimplified
import LOOConcentrationManuscript.Internal.ModelSelectionSignedAsymptoticScale
import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensionsConsumer
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open LOOConcentration
open LOOConcentration.Revision
open scoped Gradient Topology

/-- The actual signed model-selection error has one common asymptotic Gaussian
constant for both tails, its absolute deviation, and the strict-margin
wrong-sign event. The constant is chosen from the native observation LSI
constant and the two rate bounds before the dimensions, law, estimators, loss,
rates, bias, and deviation are supplied. Equality of the native scalar LSI
constant only indexes the laws sharing that same scalar parameter. -/
theorem modelSelection_signed_actual_asymptotic_probability_uniform_scalar
    (C A B : NNReal) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ {k m : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ],
        observationLogSobolevConstant μ = (C : ENNReal) →
        Integrable observationNormSq μ →
      ∀ (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
        (L : Responses m → Responses m → ℝ)
        (δ₁ δ₂ : ℕ → Observation k m → ℝ) (c δ₃ : ℕ → ℝ),
        (hSignedMeas : ∀ n, Measurable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₀ (n + 1)) L p.1 p.2 -
              fittedLoss (T₁ (n + 1)) L p.1 p.2)) →
        (hδ₁_nonneg : ∀ N z, 0 ≤ δ₁ (N + 1) z) →
        (hδ₂_nonneg : ∀ N z, 0 ≤ δ₂ (N + 1) z) →
        (hδ₁_int : ∀ N, Integrable (fun z => δ₁ (N + 1) z) μ) →
        (hδ₂_int : ∀ N, Integrable (fun z => δ₂ (N + 1) z) μ) →
        (hzero : ∀ n, Integrable (fun z =>
          fittedLoss (T₀ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z -
            fittedLoss (T₁ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z) μ) →
        (hFullLoc : ∀ n, ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean x) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean x) z)) →
        (hFullGrad : ∀ n, ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
          DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x ∧
          ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x‖ ≤
            δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖) →
        (hf₀ : ∀ n, Integrable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₀ (n + 1)) L p.1 p.2)
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) →
        (hf₁ : ∀ n, Integrable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₁ (n + 1)) L p.1 p.2)
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) →
        (hShortMeas : ∀ n, Measurable
          (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
            fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)) →
        (hShortLoc : ∀ n, ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean x) z)) →
        (hShortGrad : ∀ n, ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
          DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
          ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
            δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖) →
        (hHeld : ∀ (n : ℕ) (i : Fin (n + 2)), Integrable
          (fun D : Dataset (Observation k m) (n + 2) =>
            fittedLoss (T₀ n) L (deleteAt D i) (D i) -
              fittedLoss (T₁ n) L (deleteAt D i) (D i))
          (Measure.pi fun _ : Fin (n + 2) => μ)) →
        (hBias : ∀ (n : ℕ) (i : Fin (n + 2)),
          |(∫ D : Dataset (Observation k m) (n + 2),
              fittedLoss (T₀ n) L (deleteAt D i) (D i) -
                fittedLoss (T₁ n) L (deleteAt D i) (D i)
              ∂Measure.pi fun _ : Fin (n + 2) => μ) -
            (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
              fittedLoss (T₀ (n + 1)) L p.1 p.2 -
                fittedLoss (T₁ (n + 1)) L p.1 p.2
                ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃ (n + 2)) →
        (hQueryInt : ∀ (n : ℕ) (z : Observation k m), Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z)
          (Measure.pi fun _ : Fin (n + 1) => μ)) →
        (hc_nonneg : ∀ n, 0 ≤ c (n + 1)) →
        (hc_bound : ∀ n, c (n + 1) ≤ (B : ℝ)) →
        (hQueryLip : ∀ n, LipschitzWith
          (NNReal.mk (c (n + 1)) (hc_nonneg n))
          (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L (hQueryInt n))) →
        (hδ₂_zero : ∀ N z, δ₂ (N + 1) z = 0) →
        (hδ₁_short_rate : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ)) →
        (hδ₁_full_rate : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ)) →
        (hδ₃_nonneg : ∀ n, 0 ≤ δ₃ (n + 2)) →
        (hδ₃_tendsto : Tendsto (fun n => δ₃ (n + 2)) atTop (nhds 0)) →
        ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
          let P : Measure (Dataset (Observation k m) (n + 2)) :=
            Measure.pi fun _ : Fin (n + 2) => μ
          let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
            Revision.looRiskL1 μ (T₀ (n + 1)) L (hf₀ n) D -
              Revision.looRiskL1 μ (T₁ (n + 1)) L (hf₁ n) D
          let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
            looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
          ((P.real {D | R D - E D > ε} ≤
              3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) ∧
            P.real {D | E D - R D > ε} ≤
              3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
            P.real {D | |R D - E D| > ε} ≤
              6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
          P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
            6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
  let c₀ := modelSelectionSignedGaussianConstant C A B
  refine ⟨c₀, ?_, ?_⟩
  · exact modelSelectionSignedGaussianConstant_pos C A B
  · intro k m μ inst hC hM₂
    have hfinite : observationLogSobolevConstant μ ≠ ⊤ := by
      rw [hC]
      exact ENNReal.coe_ne_top
    intro T₀ T₁ L δ₁ δ₂ c δ₃ hSignedMeas hδ₁_nonneg hδ₂_nonneg
      hδ₁_int hδ₂_int hzero hFullLoc hFullGrad hf₀ hf₁ hShortMeas
      hShortLoc hShortGrad hHeld hBias hQueryInt hc_nonneg hc_bound hQueryLip
      hδ₂_zero hδ₁_short_rate hδ₁_full_rate hδ₃_nonneg hδ₃_tendsto ε hε
    have hεhalf : 0 < ε / 2 := by linarith
    have hδ₃_small : ∀ᶠ n : ℕ in atTop, δ₃ (n + 2) < ε / 2 :=
      hδ₃_tendsto.eventually (Iio_mem_nhds hεhalf)
    obtain ⟨nε, hnε⟩ := eventually_atTop.1 hδ₃_small
    refine ⟨nε, ?_⟩
    intro n hn
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      Revision.looRiskL1 μ (T₀ (n + 1)) L (hf₀ n) D -
        Revision.looRiskL1 μ (T₁ (n + 1)) L (hf₁ n) D
    let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let a : NNReal := ⟨(A : ℝ) / Real.sqrt (n + 1 : ℝ), by positivity⟩
    let s : ℝ := (a : ℝ) + c (n + 1) / Real.sqrt (n + 2 : ℝ) +
      ∫ z, δ₁ (n + 2) z ∂μ
    let δ : ℝ := δ₃ (n + 2)
    have hCco : (C : ℝ) = (observationLogSobolevConstant μ).toReal := by
      rw [hC]
      simp
    have hδsmall : δ < ε / 2 := hnε n hn
    have hδnonneg : 0 ≤ δ := hδ₃_nonneg n
    have ht : 0 < ε - δ := by dsimp [δ]; linarith
    have hthreshold : δ + (ε - δ) = ε := by ring
    have hδ₁short_bound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) := by
      change ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ)
      exact hδ₁_short_rate n
    have hδ₁full_int := hδ₁_int (n + 1)
    have hδ₁full_rate := hδ₁_full_rate n
    have hδ₁full_integral :
        (∫ z, δ₁ (n + 2) z ∂μ) ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
      calc
        (∫ z, δ₁ (n + 2) z ∂μ) ≤
            ∫ _z : Observation k m, (A : ℝ) / Real.sqrt (n + 2 : ℝ) ∂μ :=
          integral_mono_ae hδ₁full_int (integrable_const _) hδ₁full_rate
        _ = (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by simp
    have hc_term : c (n + 1) / Real.sqrt (n + 2 : ℝ) ≤
        (B : ℝ) / Real.sqrt (n + 2 : ℝ) :=
      div_le_div_of_nonneg_right (hc_bound n) (Real.sqrt_nonneg _)
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      have ha : 0 ≤ (a : ℝ) := NNReal.coe_nonneg _
      have hc : 0 ≤ c (n + 1) / Real.sqrt (n + 2 : ℝ) :=
        div_nonneg (hc_nonneg n) (Real.sqrt_nonneg _)
      have hi : 0 ≤ ∫ z, δ₁ (n + 2) z ∂μ :=
        integral_nonneg (fun z => hδ₁_nonneg (n + 1) z)
      linarith
    have hs_bound : s ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) +
        (B : ℝ) / Real.sqrt (n + 2 : ℝ) + (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
      change (a : ℝ) + c (n + 1) / Real.sqrt (n + 2 : ℝ) +
        ∫ z, δ₁ (n + 2) z ∂μ ≤ _
      have ha : (a : ℝ) = (A : ℝ) / Real.sqrt (n + 1 : ℝ) := rfl
      rw [ha]
      linarith only [hc_term, hδ₁full_integral]
    have hproxy := modelSelection_signed_gaussian_proxy_bound C A B n s ε δ
      hs_nonneg hs_bound hε hδsmall
    have huniform := modelSelection_actual_signed_simplified_uniform_tails
      μ T₀ T₁ L δ₁ δ₂ δ hδnonneg (hSignedMeas n)
      (fun z => hδ₁_nonneg (n + 1) z) (fun z => hδ₂_nonneg (n + 1) z)
      (hδ₁_int (n + 1)) (hδ₂_int (n + 1)) (hzero n)
      (hFullLoc n) (hFullGrad n) hfinite hM₂ (hf₀ n) (hf₁ n)
      (hShortMeas n) (hShortLoc n) (hShortGrad n) (hHeld n) (hBias n)
      (fun z => hQueryInt n z) (c (n + 1)) (hc_nonneg n)
      (hQueryLip n) (fun z => hδ₂_zero n z)
      (fun z => hδ₂_zero (n + 1) z) a hδ₁short_bound (ε - δ) ht
    have hnumeric :
        (if (observationLogSobolevConstant μ).toReal * s ^ 2 = 0 then 0 else
          Real.exp (-((ε - δ) ^ 2 /
            (2 * ((observationLogSobolevConstant μ).toReal * s ^ 2))))) ≤
        Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      convert hproxy using 1
      simp only [s, a, δ, ← hCco]
      ring_nf
    have hplus : P.real {D | R D - E D > ε} ≤
        Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      have hsource := huniform.1
      have hsource' : P.real {D | R D - E D > δ + (ε - δ)} ≤
          (if (observationLogSobolevConstant μ).toReal * s ^ 2 = 0 then 0 else
            Real.exp (-((ε - δ) ^ 2 /
              (2 * ((observationLogSobolevConstant μ).toReal * s ^ 2))))) := by
        simpa only [P, R, E, s, a, δ] using hsource
      calc
        P.real {D | R D - E D > ε} =
            P.real {D | R D - E D > δ + (ε - δ)} := by
          congr 1
          ext D
          rw [hthreshold]
        _ ≤ _ := hsource'
        _ ≤ _ := hnumeric
    have hminus : P.real {D | E D - R D > ε} ≤
        Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      have hsource := huniform.2.1
      have hsource' : P.real {D | E D - R D > δ + (ε - δ)} ≤
          (if (observationLogSobolevConstant μ).toReal * s ^ 2 = 0 then 0 else
            Real.exp (-((ε - δ) ^ 2 /
              (2 * ((observationLogSobolevConstant μ).toReal * s ^ 2))))) := by
        simpa only [P, R, E, s, a, δ] using hsource
      calc
        P.real {D | E D - R D > ε} =
            P.real {D | E D - R D > δ + (ε - δ)} := by
          congr 1
          ext D
          rw [hthreshold]
        _ ≤ _ := hsource'
        _ ≤ _ := hnumeric
    have habs : P.real {D | |R D - E D| > ε} ≤
        2 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      have hsource := huniform.2.2
      have hsource' : P.real {D | |R D - E D| > δ + (ε - δ)} ≤
          2 * (if (observationLogSobolevConstant μ).toReal * s ^ 2 = 0 then 0 else
            Real.exp (-((ε - δ) ^ 2 /
              (2 * ((observationLogSobolevConstant μ).toReal * s ^ 2))))) := by
        simpa only [P, R, E, s, a, δ] using hsource
      have hmul := mul_le_mul_of_nonneg_left hnumeric (by norm_num : 0 ≤ (2 : ℝ))
      calc
        P.real {D | |R D - E D| > ε} =
            P.real {D | |R D - E D| > δ + (ε - δ)} := by
          congr 1
          ext D
          rw [hthreshold]
        _ ≤ _ := hsource'
        _ ≤ _ := by simpa using hmul
    have hNfactor : 1 ≤ 3 * (n + 2 : ℝ) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    have hExpNonneg : 0 ≤ Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) :=
      Real.exp_nonneg _
    have hplus' : P.real {D | R D - E D > ε} ≤
        3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      calc
        P.real {D | R D - E D > ε} ≤ Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := hplus
        _ ≤ 3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
          calc
            Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) =
                1 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hNfactor hExpNonneg
    have hminus' : P.real {D | E D - R D > ε} ≤
        3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      calc
        P.real {D | E D - R D > ε} ≤ Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := hminus
        _ ≤ 3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
          calc
            Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) =
                1 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hNfactor hExpNonneg
    have habs' : P.real {D | |R D - E D| > ε} ≤
        6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      calc
        P.real {D | |R D - E D| > ε} ≤
            2 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := habs
        _ ≤ 6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
          calc
            2 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) =
                2 * (1 * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) := by ring
            _ ≤ 2 * (3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hNfactor hExpNonneg) (by norm_num)
            _ = 6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by ring
    have hMargin := modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
      μ T₀ T₁ L (hf₀ n) (hf₁ n) ε
    dsimp only [R, E] at hMargin
    have hsign : P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
        P.real {D | ε < |R D - E D|} := measureReal_mono hMargin
    have hsign' : P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
        6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
      calc
        P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
            P.real {D | ε < |R D - E D|} := hsign
        _ = P.real {D | |R D - E D| > ε} := by congr 1
        _ ≤ 6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := habs'
    change ((P.real {D | R D - E D > ε} ≤
          3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) ∧
        P.real {D | E D - R D > ε} ≤
          3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
        P.real {D | |R D - E D| > ε} ≤
          6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
      P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
        6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))
    exact ⟨⟨⟨hplus', hminus'⟩, habs'⟩, hsign'⟩

end LOOConcentration.Manuscript.Internal
