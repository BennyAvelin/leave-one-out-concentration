import LOOConcentrationRevision.Concentration.DatasetLipschitzHerbst
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import Mathlib.Analysis.Real.Sqrt

/-! Source validation-average subgaussian bound. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped MeasureTheory

private theorem sum_observationNorm_le_sqrt_mul_datasetNorm {k m N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :
    (∑ i : Fin N, LOOConcentration.observationNorm (D i)) ≤
      Real.sqrt (N : ℝ) * LOOConcentration.datasetNorm D := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i : Fin N => LOOConcentration.observationNorm (D i)) (fun _ => (1 : ℝ))
  have hsquares :
      (∑ i : Fin N, LOOConcentration.observationNorm (D i) ^ 2) =
        LOOConcentration.datasetNormSq D := by
    simp [LOOConcentration.datasetNormSq, LOOConcentration.observationNorm_sq]
  have hones : (∑ i : Fin N, (1 : ℝ) ^ 2) = (N : ℝ) := by simp
  calc
    (∑ i : Fin N, LOOConcentration.observationNorm (D i)) =
        ∑ i : Fin N, LOOConcentration.observationNorm (D i) * 1 := by simp
    _ ≤ Real.sqrt (∑ i : Fin N, LOOConcentration.observationNorm (D i) ^ 2) *
        Real.sqrt (∑ i : Fin N, (1 : ℝ) ^ 2) := by simpa using hcs
    _ = Real.sqrt (N : ℝ) * LOOConcentration.datasetNorm D := by
      rw [hsquares, hones]
      simp [LOOConcentration.datasetNorm, mul_comm]

private theorem validationAverage_dataset_lipschitz_bound
    {k m n : ℕ}
    {μ : Measure (LOOConcentration.Observation k m)} [IsProbabilityMeasure μ]
    {T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1)}
    {L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ}
    {δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hLip : ∀ z w,
      |meanFittedLoss μ (T n) L z (hSt.mean_integrable z) -
        meanFittedLoss μ (T n) L w (hSt.mean_integrable w)| ≤
          c * LOOConcentration.observationNorm (z - w))
    (D E : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :
    |(∑ i : Fin (n + 2),
        meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ) -
      (∑ i : Fin (n + 2),
        meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))) / (n + 2 : ℝ)| ≤
      (c / Real.sqrt (n + 2 : ℝ)) * LOOConcentration.datasetNorm (D - E) := by
  have hc : 0 ≤ c := hSt.c_nonneg
  have hcoord : ∀ i : Fin (n + 2),
      |meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
        meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))| ≤
          c * LOOConcentration.observationNorm (D i - E i) := by
    intro i
    exact hLip (D i) (E i)
  have hsumAbs := Finset.abs_sum_le_sum_abs
    (f := fun i : Fin (n + 2) =>
      meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
        meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))) Finset.univ
  have hsumBound :
      |∑ i : Fin (n + 2),
        (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
          meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i)))| ≤
        c * (Real.sqrt (n + 2 : ℝ) * LOOConcentration.datasetNorm (D - E)) := by
    calc
      _ ≤ ∑ i : Fin (n + 2),
          |meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
            meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))| := hsumAbs
      _ ≤ ∑ i : Fin (n + 2), c * LOOConcentration.observationNorm (D i - E i) :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = c * ∑ i : Fin (n + 2), LOOConcentration.observationNorm (D i - E i) := by
        rw [Finset.mul_sum]
      _ ≤ c * (Real.sqrt (n + 2 : ℝ) * LOOConcentration.datasetNorm (D - E)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        simpa only [Pi.sub_apply, Nat.cast_add, Nat.cast_ofNat] using
          sum_observationNorm_le_sqrt_mul_datasetNorm (D - E)
  have hNden : 0 < (n + 2 : ℝ) := by positivity
  rw [← sub_div, ← Finset.sum_sub_distrib]
  have hsqrtPos : 0 < Real.sqrt (n + 2 : ℝ) := Real.sqrt_pos.2 hNden
  have hsqrt : Real.sqrt (n + 2 : ℝ) * Real.sqrt (n + 2 : ℝ) = (n + 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (n + 2 : ℝ) by positivity)]
  calc
    |(∑ i : Fin (n + 2),
        (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
          meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i)))) /
          (n + 2 : ℝ)| =
        |(∑ i : Fin (n + 2),
          (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
            meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))))| /
          (n + 2 : ℝ) := by rw [abs_div, abs_of_pos hNden]
    _ ≤ (c * (Real.sqrt (n + 2 : ℝ) * LOOConcentration.datasetNorm (D - E))) /
        (n + 2 : ℝ) := div_le_div_of_nonneg_right hsumBound (le_of_lt hNden)
    _ = (c / Real.sqrt (n + 2 : ℝ)) * LOOConcentration.datasetNorm (D - E) := by
      field_simp [ne_of_gt hNden, ne_of_gt hsqrtPos]
      calc
        c * Real.sqrt (n + 2 : ℝ) ^ 2 * LOOConcentration.datasetNorm (D - E) =
          c * LOOConcentration.datasetNorm (D - E) *
            (Real.sqrt (n + 2 : ℝ) * Real.sqrt (n + 2 : ℝ)) := by
          rw [pow_two]
          ring
        _ = c * LOOConcentration.datasetNorm (D - E) * (n + 2 : ℝ) := by rw [hsqrt]
        _ = c * (n + 2 : ℝ) * LOOConcentration.datasetNorm (D - E) := by ring

/-- Literal validation average, centered at its actual ordered-sample mean. -/
theorem validationAverage_hasSubgaussianMGF_of_revisedStanding
    {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hLip : ∀ z w,
      |meanFittedLoss μ (T n) L z (hSt.mean_integrable z) -
        meanFittedLoss μ (T n) L w (hSt.mean_integrable w)| ≤
          c * LOOConcentration.observationNorm (z - w)) :
    let V : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2),
        meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ)
    ProbabilityTheory.HasSubgaussianMGF
      (fun D => V D - ∫ E, V E ∂(Measure.pi fun _ : Fin (n + 2) => μ))
      (NNReal.mk
        (((observationLogSobolevConstant μ).toReal * c ^ 2) / (n + 2 : ℝ))
        (div_nonneg
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg c)) (by positivity)))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let N : ℝ := (n + 2 : ℝ)
  let V : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => (∑ i : Fin (n + 2),
      meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ)
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q := datasetLawOfObservation (r := n + 2) μ
  let F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ :=
    fun x => V (datasetOfEuclidean x)
  let ℓ : NNReal := ⟨c / Real.sqrt N, div_nonneg hSt.c_nonneg (Real.sqrt_nonneg N)⟩
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hF : LipschitzWith ℓ F := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    have hsub : datasetOfEuclidean x - datasetOfEuclidean y =
        datasetOfEuclidean (x - y) := by
      funext i
      apply Prod.ext <;> funext j <;> rfl
    have hbound := validationAverage_dataset_lipschitz_bound hSt hLip
      (datasetOfEuclidean x) (datasetOfEuclidean y)
    rw [hsub, datasetNorm_datasetOfEuclidean] at hbound
    change |V (datasetOfEuclidean x) - V (datasetOfEuclidean y)| ≤
      (c / Real.sqrt (n + 2 : ℝ)) * ‖x - y‖
    simpa only [F, V, N] using hbound
  have hEuclidean := dataset_lipschitz_hasSubgaussianMGF μ hSt.lsi
    hSt.second_moment F ℓ hF
  have hmean : (∫ x, F x ∂Q) = ∫ D, F (datasetToEuclidean D) ∂P := by
    dsimp [Q, datasetLawOfObservation, P]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hF.continuous.aestronglyMeasurable
  have hRaw := ProbabilityTheory.HasSubgaussianMGF.of_map
    measurable_datasetToEuclidean.aemeasurable hEuclidean
  have hRaw' : ProbabilityTheory.HasSubgaussianMGF
      (fun D => F (datasetToEuclidean D) - ∫ E, F (datasetToEuclidean E) ∂P)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (ℓ : ℝ) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun D => F (datasetToEuclidean D) - ∫ x, F x ∂Q) _ P at hRaw
    rw [hmean] at hRaw
    exact hRaw
  have hcomp : (fun D => F (datasetToEuclidean D)) = V := by
    funext D
    simp [F, datasetOfEuclidean_datasetToEuclidean]
  have hcompInt : (∫ E, F (datasetToEuclidean E) ∂P) = ∫ E, V E ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun E => congrFun hcomp E)
  have hOrdered : ProbabilityTheory.HasSubgaussianMGF
      (fun D => V D - ∫ E, V E ∂P)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (ℓ : ℝ) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    have heq : (fun D => F (datasetToEuclidean D) - ∫ E, F (datasetToEuclidean E) ∂P) =ᵐ[P]
        (fun D => V D - ∫ E, V E ∂P) := by
      filter_upwards [] with D
      rw [congrFun hcomp D, hcompInt]
    exact hRaw'.congr heq
  have hvariance : (ℓ : ℝ) ^ 2 = c ^ 2 / N := by
    change (c / Real.sqrt N) ^ 2 = c ^ 2 / N
    rw [div_pow, Real.sq_sqrt (le_of_lt hNpos)]
  have hcoeff :
      NNReal.mk ((observationLogSobolevConstant μ).toReal * (ℓ : ℝ) ^ 2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) =
        NNReal.mk (((observationLogSobolevConstant μ).toReal * c ^ 2) / N)
          (div_nonneg
            (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg c)) (le_of_lt hNpos)) := by
    apply Subtype.ext
    change (observationLogSobolevConstant μ).toReal * (ℓ : ℝ) ^ 2 =
      ((observationLogSobolevConstant μ).toReal * c ^ 2) / N
    rw [hvariance]
    ring
  change ProbabilityTheory.HasSubgaussianMGF
    (fun D => V D - ∫ E, V E ∂P)
    (NNReal.mk (((observationLogSobolevConstant μ).toReal * c ^ 2) / N) _)
    P
  rw [← hcoeff]
  exact hOrdered

#print axioms validationAverage_hasSubgaussianMGF_of_revisedStanding
end LOOConcentration.Revision
