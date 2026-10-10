import LOOConcentration.Concentration.SegmentEstimate
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Geometry.EuclideanNormFacts
import LOOConcentration.Probability.SampleMoments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

/-!
# Growth and integrability from the segment estimate

The zero-dataset segment estimate gives quadratic growth in the exact frozen
dataset norm. Finite second moment then gives integrability under the ordered
product sample law.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration

private theorem continuous_datasetToEuclidean {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation k m) N →
      EuclideanSpace ℝ (DatasetCoordinate k m N)) := by
  change Continuous (fun D : Dataset (Observation k m) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

private theorem continuousAt_datasetNorm_sub {k m N : ℕ}
    (D : Dataset (Observation k m) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation k m) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean.comp (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    exact datasetNorm_eq_euclidean (E - D)
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

private theorem locallyLipschitzDataFunction_continuous {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) : Continuous F.1 := by
  rw [continuous_iff_continuousAt]
  intro D
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨U, hU, K, hK, hLip⟩ := F.2 D
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hzero : datasetNorm (D - D) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
    (continuousAt_datasetNorm_sub D) (ε / (K + 1)) (by positivity)
  let δ := min ρ η
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hdist
  have hEU : E ∈ U := hρU (by
    dsimp [δ] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _))
  have hnorm : datasetNorm (E - D) < ε / (K + 1) := by
    have hdist' := hηbound (by
      dsimp [δ] at hdist
      exact lt_of_lt_of_le hdist (min_le_right _ _))
    have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hdist'
    exact hdist'
  have hbound := hLip E hEU D (mem_of_mem_nhds hU)
  rw [Real.dist_eq]
  change |F.1 E - F.1 D| < ε
  calc
    |F.1 E - F.1 D| ≤ K * datasetNorm (E - D) := hbound
    _ < ε := by
      have hnormNonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      have hKmul : K * datasetNorm (E - D) ≤
          (K + 1) * datasetNorm (E - D) := by
        nlinarith [hnormNonneg]
      have hkp : 0 < K + 1 := by linarith
      have hlt : (K + 1) * datasetNorm (E - D) <
          (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hnorm hkp
      have heq : (K + 1) * (ε / (K + 1)) = ε := by field_simp
      rw [heq] at hlt
      exact hKmul.trans_lt hlt

/-- The segment estimate with its second endpoint at zero gives quadratic
growth in the exact unnormalized frozen dataset norm. -/
theorem datasetLocalSlope_growth_bound {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (D : DataCarrier k m n) :
    |F.1 D| ≤ |F.1 0| + a * datasetNorm D + (b / 2) * datasetNormSq D := by
  have hseg := datasetLocalSlope_segment_estimate F a b ha hb hSlope D 0
  have hzero : datasetNorm (0 : DataCarrier k m n) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  have hseg' : |F.1 D - F.1 0| ≤
      datasetNorm D * (a + b / 2 * datasetNorm D) := by
    simpa [hzero, sub_zero] using hseg
  calc
    |F.1 D| = |(F.1 D - F.1 0) + F.1 0| := by congr 1; ring
    _ ≤ |F.1 D - F.1 0| + |F.1 0| := abs_add_le _ _
    _ ≤ |F.1 0| + datasetNorm D * (a + b / 2 * datasetNorm D) := by
      calc
        _ = |F.1 0| + |F.1 D - F.1 0| := add_comm _ _
        _ ≤ |F.1 0| + datasetNorm D * (a + b / 2 * datasetNorm D) :=
          add_le_add_right hseg' _
    _ = |F.1 0| + a * datasetNorm D + (b / 2) * datasetNormSq D := by
      rw [← datasetNorm_sq D]
      ring

/-- Integrability of a locally Lipschitz data function under the actual
ordered product law, assuming only the source finite-second-moment input and
its pointwise local-slope growth bound. -/
theorem integrable_datasetFunction_of_localSlope_bound {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D) :
    Integrable F.1 (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let ν := Measure.pi fun _ : Fin (n + 1) => μ
  have hnorm : Integrable (datasetNorm (k := k + 1) (m := m + 1) (n := n + 1)) ν :=
    integrable_datasetNorm μ hM2
  have hnormSq : Integrable
      (datasetNormSq (k := k + 1) (m := m + 1) (n := n + 1)) ν :=
    integrable_datasetNormSq μ hM2
  have hmajor : Integrable
      (fun D : DataCarrier k m n =>
        |F.1 0| + a * datasetNorm D + (b / 2) * datasetNormSq D) ν := by
    exact ((integrable_const _).add (hnorm.const_mul a)).add
      (hnormSq.const_mul (b / 2))
  have hmeas : Measurable F.1 := (locallyLipschitzDataFunction_continuous F).measurable
  apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
  filter_upwards with D
  have hgrowth := datasetLocalSlope_growth_bound F a b ha hb hSlope D
  rw [Real.norm_eq_abs]
  exact hgrowth

/-- The first moment of the frozen product-sample norm is at most the square
root of its second moment, with the sample moment evaluated under the exact
ordered product law. -/
theorem integral_datasetNorm_le_sqrt_second_moment {k m N : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    (∫ D : Dataset (Observation k m) N, datasetNorm D
      ∂Measure.pi fun _ : Fin N => μ) ≤
        Real.sqrt ((N : ℝ) * ∫ z, observationNormSq z ∂μ) := by
  let ν := Measure.pi fun _ : Fin N => μ
  have hsq : Integrable (fun D : Dataset (Observation k m) N => datasetNorm D ^ 2) ν := by
    have heq : (fun D : Dataset (Observation k m) N => datasetNorm D ^ 2) = datasetNormSq := by
      funext D
      exact datasetNorm_sq D
    rw [heq]
    exact integrable_datasetNormSq μ hM2
  have hnormCont : Continuous (datasetNorm (k := k) (m := m) (n := N)) := by
    have hcont := continuous_datasetToEuclidean (k := k) (m := m) (N := N)
    have heq : (datasetNorm (k := k) (m := m) (n := N)) =
        fun D => ‖datasetToEuclidean D‖ := by
      funext D
      exact datasetNorm_eq_euclidean D
    rw [heq]
    exact continuous_norm.comp hcont
  have hnormMem : MemLp (datasetNorm (k := k) (m := m) (n := N))
      (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_two_iff_integrable_sq hnormCont.aestronglyMeasurable).2 hsq
  have honeMem : MemLp (fun _ : Dataset (Observation k m) N => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) ν := memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (Real.HolderConjugate.two_two) hnormMem honeMem
  have hmoment := integral_datasetNormSq (k := k) (m := m) (n := N) μ hM2
  have hnormNonneg (D : Dataset (Observation k m) N) : 0 ≤ datasetNorm D :=
    Real.sqrt_nonneg _
  have hleft :
      (∫ D : Dataset (Observation k m) N, datasetNorm D ∂ν) =
        ∫ D, ‖datasetNorm D‖ * ‖(1 : ℝ)‖ ∂ν := by
    apply integral_congr_ae
    filter_upwards with D
    rw [Real.norm_eq_abs, abs_of_nonneg (hnormNonneg D)]
    simp
  have hright :
      (∫ D : Dataset (Observation k m) N, ‖datasetNorm D‖ ^ 2 ∂ν) =
        (N : ℝ) * ∫ z, observationNormSq z ∂μ := by
    calc
      (∫ D : Dataset (Observation k m) N, ‖datasetNorm D‖ ^ 2 ∂ν) =
          ∫ D : Dataset (Observation k m) N, datasetNorm D ^ 2 ∂ν := by
            congr 1
            funext D
            rw [Real.norm_eq_abs, abs_of_nonneg (hnormNonneg D)]
      _ = ∫ D : Dataset (Observation k m) N, datasetNormSq D ∂ν := by
            congr 1
            funext D
            exact datasetNorm_sq D
      _ = (N : ℝ) * ∫ z, observationNormSq z ∂μ := hmoment
  calc
    (∫ D : Dataset (Observation k m) N, datasetNorm D ∂ν) =
        ∫ D, ‖datasetNorm D‖ * ‖(1 : ℝ)‖ ∂ν := hleft
    _ ≤ (∫ D : Dataset (Observation k m) N, ‖datasetNorm D‖ ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
          (∫ D, ‖(1 : ℝ)‖ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := hholder
    _ = Real.sqrt ((N : ℝ) * ∫ z, observationNormSq z ∂μ) := by
      calc
        _ = (∫ D : Dataset (Observation k m) N, ‖datasetNorm D‖ ^ 2 ∂ν) ^
              (1 / 2 : ℝ) := by simp [ν]
        _ = ((N : ℝ) * ∫ z, observationNormSq z ∂μ) ^ (1 / 2 : ℝ) :=
          congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ)) hright
        _ = Real.sqrt ((N : ℝ) * ∫ z, observationNormSq z ∂μ) :=
          (Real.sqrt_eq_rpow _).symm

end LOOConcentration
