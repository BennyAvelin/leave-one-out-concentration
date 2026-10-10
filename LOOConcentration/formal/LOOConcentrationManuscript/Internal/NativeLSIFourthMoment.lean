import LOOConcentrationRevision.Concentration.NormMgfLimit
import Mathlib.Probability.Moments.IntegrableExpMul
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Finite native LSI gives the fourth norm moment through the accepted
squared-norm MGF, including native constant zero. -/
theorem finite_nativeLSI_norm_fourth_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hFinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (hSecond : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^2) μ) :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^4) μ := by
  let C := (LOOConcentration.Revision.logSobolevConstant μ).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_toReal hFinite.ne]
  let t := 1/(4*(C+1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hCut : 2*C*t < 1 := by
    dsimp [t]
    rw [mul_one_div]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(C+1))).2
    linarith
  have hPos := (LOOConcentration.Revision.norm_sq_log_mgf_le_of_admissible_constant
    μ C hC hLC hSecond t ht.le hCut).1
  have hNeg : Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-t*‖x‖^2)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hPow := ProbabilityTheory.integrable_pow_of_integrable_exp_mul ht.ne' hPos hNeg 2
  simpa only [← pow_mul] using hPow

/-- The actual ridge observation law has a fourth feature moment under its
original native LSI and second-moment assumptions; no fourth-moment gate is input. -/
theorem observation_nativeLSI_feature_fourth_moment
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hFinite : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    Integrable (fun z => (LOOConcentration.observationNormSq z)^2) μ ∧
      Integrable (fun z : LOOConcentration.Observation 1 1 => (z.1 0)^4) μ := by
  let ν := μ.map LOOConcentration.observationToEuclidean
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map
    LOOConcentration.Revision.measurable_observationToEuclidean.aemeasurable
  have hNorm2 (z : LOOConcentration.Observation 1 1) :
      ‖LOOConcentration.observationToEuclidean z‖^2 =
        LOOConcentration.observationNormSq z := by
    rw [← LOOConcentration.observationNorm_eq_euclidean,LOOConcentration.observationNorm]
    exact Real.sq_sqrt (LOOConcentration.observationNormSq_nonneg z)
  have hSecondν : Integrable (fun x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) => ‖x‖^2) ν := by
    apply (integrable_map_measure (by fun_prop)
      LOOConcentration.Revision.measurable_observationToEuclidean.aemeasurable).2
    change Integrable (fun z => ‖LOOConcentration.observationToEuclidean z‖^2) μ
    simpa only [hNorm2] using hSecond
  have hFiniteν : LOOConcentration.Revision.logSobolevConstant ν < ⊤ := hFinite
  have hFourth := finite_nativeLSI_norm_fourth_moment ν hFiniteν hSecondν
  have hRaw : Integrable (fun z => ‖LOOConcentration.observationToEuclidean z‖^4) μ :=
    (integrable_map_measure (by fun_prop)
      LOOConcentration.Revision.measurable_observationToEuclidean.aemeasurable).1 hFourth
  have hSq : Integrable (fun z => (LOOConcentration.observationNormSq z)^2) μ := by
    convert hRaw using 1
    funext z
    rw [show (4 : ℕ)=2*2 by norm_num,pow_mul,hNorm2]
  refine ⟨hSq,?_⟩
  apply hSq.mono' (by fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (z.1 0)^4)]
  calc
    _ = ((z.1 0)^2)^2 := by ring
    _ ≤ (LOOConcentration.observationNormSq z)^2 := by
      apply (sq_le_sq₀ (sq_nonneg _) (LOOConcentration.observationNormSq_nonneg z)).2
      simp only [LOOConcentration.observationNormSq,Fin.sum_univ_one]
      exact le_add_of_nonneg_right (sq_nonneg _)

end LOOConcentration.Manuscript.Internal
