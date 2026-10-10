import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationAverageRegularity
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Gradient

/-- The literal expected signed fitted loss under the original short law
μ^(n+1). Its sole integrability premise is for the signed integrand itself. -/
noncomputable def modelSelectionSignedExpectedMean
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (_hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (z : LOOConcentration.Observation k m) : ℝ :=
  ∫ D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1),
    (LOOConcentration.fittedLoss (T₀ n) L D z -
      LOOConcentration.fittedLoss (T₁ n) L D z)
    ∂(Measure.pi fun _ : Fin (n+1) => μ)

/-- The source signed expected mean in original Euclidean query coordinates. -/
noncomputable def modelSelectionSignedExpectedMeanQuery
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m)) : ℝ :=
  modelSelectionSignedExpectedMean μ T₀ T₁ L hI
    (LOOConcentration.Revision.observationOfEuclidean z)

/-- The literal mean over full validation data of size n+2 of the signed
expected losses trained on the independent short law μ^(n+1). -/
noncomputable def modelSelectionSignedExpectedValidationAverage
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+2)) : ℝ :=
  originalQueryValidationAverage
    (modelSelectionSignedExpectedMean μ T₀ T₁ L hI) D

/-- Actual signed expected-loss validation-average regularity at full sample
size n+2. Its only regularity inputs concern the genuine signed expected
query mean on the original observation carrier. -/
theorem modelSelectionSignedExpectedValidationAverage_regular
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hlocal : LocallyLipschitz
      (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI))
    (hgrad : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤
        c+d*‖z‖) :
    let V := modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI
    LocallyLipschitz
        (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
          V (LOOConcentration.Revision.datasetOfEuclidean u)) ∧
      ∀ᵐ u ∂(volume : Measure
          (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)))),
        DifferentiableAt ℝ
          (fun v => V (LOOConcentration.Revision.datasetOfEuclidean v)) u ∧
        ‖gradient (fun v => V (LOOConcentration.Revision.datasetOfEuclidean v)) u‖ ≤
          c/Real.sqrt (n+2:ℝ)+d/(n+2:ℝ)*‖u‖ := by
  intro V
  let f : LOOConcentration.Observation k m → ℝ :=
    modelSelectionSignedExpectedMean μ T₀ T₁ L hI
  have hlocal' : LocallyLipschitz
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)) := by
    change LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI)
    exact hlocal
  have hgrad' : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c+d*‖z‖ := by
    change ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
        ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤ c+d*‖z‖
    exact hgrad
  have hregular := originalQueryValidationAverage_euclidean_regular
    (k := k) (m := m) (N := n+2) f c d hc hd (Nat.succ_le_succ (Nat.zero_le (n+1))) hlocal' hgrad'
  change LocallyLipschitz
      (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
        originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u)) ∧
    ∀ᵐ u ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)))),
      DifferentiableAt ℝ
        (fun v => originalQueryValidationAverage f
          (LOOConcentration.Revision.datasetOfEuclidean v)) u ∧
      ‖gradient (fun v => originalQueryValidationAverage f
          (LOOConcentration.Revision.datasetOfEuclidean v)) u‖ ≤
        c/Real.sqrt (n+2:ℝ)+d/(n+2:ℝ)*‖u‖
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hregular

/-- If the signed expected query mean has zero growth, its actual full-size
validation average is Lipschitz with the exact c/sqrt(n+2) rate. -/
theorem modelSelectionSignedExpectedValidationAverage_lipschitz_of_zero_growth
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hdzero : d = 0)
    (hlocal : LocallyLipschitz
      (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI))
    (hgrad : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤
        c+d*‖z‖) :
    let V := modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI
    LipschitzWith (Real.toNNReal (c/Real.sqrt (n+2:ℝ)))
      (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
        V (LOOConcentration.Revision.datasetOfEuclidean u)) := by
  intro V
  let f : LOOConcentration.Observation k m → ℝ :=
    modelSelectionSignedExpectedMean μ T₀ T₁ L hI
  have hlocal' : LocallyLipschitz
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)) := by
    change LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI)
    exact hlocal
  have hgrad' : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c+d*‖z‖ := by
    change ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
        (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
        ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤ c+d*‖z‖
    exact hgrad
  have hLip := originalQueryValidationAverage_euclidean_lipschitz_of_zero_growth
    (k := k) (m := m) (N := n+2) f c d hc hd (Nat.succ_le_succ (Nat.zero_le (n+1))) hdzero hlocal' hgrad'
  change LipschitzWith (Real.toNNReal (c/Real.sqrt (n+2:ℝ)))
    (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
      originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hLip

/-- A genuine query-coordinate Lipschitz premise for the signed expected mean
also yields the exact Lipschitz rate for its actual validation average. -/
theorem modelSelectionSignedExpectedValidationAverage_lipschitz_of_query_lipschitz
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r+1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hI : ∀ z : LOOConcentration.Observation k m,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n+1) =>
          LOOConcentration.fittedLoss (T₀ n) L D z -
            LOOConcentration.fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c : ℝ) (hc : 0 ≤ c)
    (hqueryLip : LipschitzWith (Real.toNNReal c)
      (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI)) :
    let V := modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI
    LipschitzWith (Real.toNNReal (c/Real.sqrt (n+2:ℝ)))
      (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
        V (LOOConcentration.Revision.datasetOfEuclidean u)) := by
  intro V
  let f : LOOConcentration.Observation k m → ℝ :=
    modelSelectionSignedExpectedMean μ T₀ T₁ L hI
  have hqueryLip' : LipschitzWith (Real.toNNReal c)
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)) := by
    change LipschitzWith (Real.toNNReal c)
      (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI)
    exact hqueryLip
  have hLip := originalQueryValidationAverage_euclidean_lipschitz_of_query_lipschitz
    (k := k) (m := m) (N := n+2) f c hc (Nat.succ_le_succ (Nat.zero_le (n+1))) hqueryLip'
  change LipschitzWith (Real.toNNReal (c/Real.sqrt (n+2:ℝ)))
    (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n+2)) =>
      originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hLip


end LOOConcentration.Manuscript.Internal
