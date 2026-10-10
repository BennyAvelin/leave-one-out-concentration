import NoncenteredLpSourceAssembly
import LOOConcentrationRevision.Probability.NormApproximationSource
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentration.Analysis.DatasetMeasureTransport
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open MeasureTheory Filter
open InnerProductSpace
open scoped ENNReal Topology
namespace LOOConcentration.Revision

/-- The second moments of the literal accepted clipped-mollified norm sequence
converge to the raw second moment. The dominator is the actual integrable
function `2 + 2 * ‖x‖^2`. -/
theorem normClipThenMollify_sq_integral_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ) :
    Tendsto (fun j => ∫ x,
      (normClipThenMollify (ι := ι) j x) ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖x‖ ^ 2 ∂μ)) := by
  let bound : EuclideanSpace ℝ ι → ℝ := fun x => 2 + 2 * ‖x‖ ^ 2
  have hboundInt : Integrable bound μ := by
    dsimp [bound]
    exact (integrable_const (2 : ℝ)).add (hmoment.const_mul (2 : ℝ))
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (fun x => (normClipThenMollify (ι := ι) j x) ^ 2) μ := by
    exact (((normClipThenMollify_bounded_smooth (ι := ι) j).1.continuous).pow 2).aestronglyMeasurable
  have hdom (j : ℕ) (x : EuclideanSpace ℝ ι) :
      ‖(normClipThenMollify (ι := ι) j x) ^ 2‖ ≤ bound x := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hclose : |normClipThenMollify (ι := ι) j x -
        clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| ≤
        normApproximationRadius j := by
      have hseg : HasLinearGrowthSegmentBound
          (clipFunction (normApproximationCap j : ℝ)
            (fun y : EuclideanSpace ℝ ι => ‖y‖)) 1 0 :=
        clipFunction_segmentBound (by
          intro y z
          simpa [dist_eq_norm] using abs_norm_sub_norm_le y z)
      have hh := clipThenMollify_close
        (f := fun y : EuclideanSpace ℝ ι => ‖y‖)
        (N := (normApproximationCap j : ℝ))
        (η := normApproximationRadius j) (a := 1) (b := 0)
        continuous_norm (normApproximationRadius_pos j) hseg
        (by norm_num) (by norm_num) x
      have hfun : clipFunction (normApproximationCap j : ℝ)
          (fun y : EuclideanSpace ℝ ι => ‖y‖) =
          clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j := by
        funext y
        rfl
      rw [hfun] at hh
      simpa [normClipThenMollify, normApproximationRadius] using hh
    have hclip_nonneg : 0 ≤ clipValueSequence
        (fun y : EuclideanSpace ℝ ι => ‖y‖) j x := by
      change 0 ≤ max (-((j : ℝ) + 1)) (min ‖x‖ ((j : ℝ) + 1))
      exact le_trans (le_min (norm_nonneg _) (by positivity)) (le_max_right _ _)
    have hclip_le : clipValueSequence
        (fun y : EuclideanSpace ℝ ι => ‖y‖) j x ≤ ‖x‖ := by
      change max (-((j : ℝ) + 1)) (min ‖x‖ ((j : ℝ) + 1)) ≤ ‖x‖
      exact max_le (by linarith [norm_nonneg x, show 0 ≤ (j : ℝ) + 1 by positivity]) (min_le_left _ _)
    have hFabs : |normClipThenMollify (ι := ι) j x| ≤ 1 + ‖x‖ := by
      have habs := abs_sub_le (normClipThenMollify (ι := ι) j x)
        (clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x) 0
      calc
        |normClipThenMollify (ι := ι) j x| ≤
            |normClipThenMollify (ι := ι) j x -
                clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| +
              |clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| := by
          simpa using habs
        _ ≤ normApproximationRadius j + ‖x‖ := by
          rw [abs_of_nonneg hclip_nonneg]
          exact add_le_add hclose hclip_le
        _ ≤ 1 + ‖x‖ := add_le_add (normApproximationRadius_le_one j) le_rfl
    have hsq : (normClipThenMollify (ι := ι) j x) ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hFabs
    have hprod : (1 + ‖x‖) ^ 2 ≤ 2 + 2 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - 1)]
    exact hsq.trans hprod
  have hpoint (x : EuclideanSpace ℝ ι) :
      Tendsto (fun j => (normClipThenMollify (ι := ι) j x) ^ 2)
        atTop (𝓝 (‖x‖ ^ 2)) := by
    exact ((continuous_pow 2).continuousAt.tendsto.comp
      (normClipThenMollify_tendsto x))
  exact tendsto_integral_of_dominated_convergence
    (bound := bound)
    (F := fun j x => (normClipThenMollify (ι := ι) j x) ^ 2)
    (f := fun x => ‖x‖ ^ 2)
    (fun j => hmeas j) hboundInt
    (fun j => Filter.Eventually.of_forall (hdom j))
    (Filter.Eventually.of_forall hpoint)


/-- A single bounded member of the accepted approximation has the sharp
`C (p - 2)` norm bound, with the gradient moment discharged internally. -/
theorem normClipThenMollify_eLpNorm_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    {p : ℝ} (hp : 2 ≤ p) (j : ℕ) :
    eLpNorm' (normClipThenMollify (ι := ι) j) p μ ≤
      ENNReal.ofReal (Real.sqrt
        ((∫ x, (normClipThenMollify (ι := ι) j x) ^ 2 ∂μ) + C * (p - 2))) := by
  let F : EuclideanSpace ℝ ι → ℝ := normClipThenMollify (ι := ι) j
  rcases normClipThenMollify_bounded_smooth (ι := ι) j with ⟨hF, B, hB, hbound⟩
  have hFmem : MemLp F (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound hF.continuous.aestronglyMeasurable B
    filter_upwards with x
    simpa only [Real.norm_eq_abs, F] using (hbound x).1
  have hRawInt : Integrable (fun x => |F x| ^ p) μ := by
    have h := hFmem.integrable_norm_rpow'
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using h
  let G : EuclideanSpace ℝ ι → ℝ := fun x => ‖gradient F x‖
  have hGcont : Continuous G := by
    dsimp [G, gradient]
    exact continuous_norm.comp (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous).comp
      (hF.continuous_fderiv (by norm_num : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)))
  have hGmem : MemLp G (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound hGcont.aestronglyMeasurable 1
    filter_upwards with x
    have hgrad := normClipThenMollify_gradient_bound (ι := ι) j x
    simpa [G] using hgrad
  have hGInt : Integrable (fun x => ‖gradient F x‖ ^ p) μ := by
    have h := hGmem.integrable_norm_rpow'
    simpa [G, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using h
  have hGle1 : ∀ x, G x ^ p ≤ 1 := by
    intro x
    exact Real.rpow_le_one (norm_nonneg _) (normClipThenMollify_gradient_bound (ι := ι) j x)
      (by linarith : 0 ≤ p)
  have hGmoment : (∫ x, ‖gradient F x‖ ^ p ∂μ) ≤ 1 := by
    calc
      (∫ x, ‖gradient F x‖ ^ p ∂μ) ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono hGInt (integrable_const 1) hGle1
      _ = 1 := by simp
  have hGnonneg : 0 ≤ ∫ x, ‖gradient F x‖ ^ p ∂μ :=
    integral_nonneg (fun x => by positivity)
  have hGpowered : (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) ≤ 1 :=
    Real.rpow_le_one hGnonneg hGmoment (by positivity)
  have hbounded := boundedSmoothNoncenteredLp μ C hC hLC F hF B hB
    (by simpa [F] using hbound) hp
  have hcoef : 0 ≤ C * (p - 2) := mul_nonneg hC (by linarith)
  have hsharp : (∫ x, |F x| ^ p ∂μ) ^ (2 / p) ≤
      (∫ x, F x ^ 2 ∂μ) + C * (p - 2) := by
    calc
      _ ≤ (∫ x, F x ^ 2 ∂μ) + C * (p - 2) *
          (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := hbounded
      _ ≤ (∫ x, F x ^ 2 ∂μ) + C * (p - 2) := by
          calc
            _ = C * (p - 2) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) +
                ∫ x, F x ^ 2 ∂μ := by ring
            _ ≤ C * (p - 2) * 1 + ∫ x, F x ^ 2 ∂μ :=
              add_le_add_left (mul_le_mul_of_nonneg_left hGpowered hcoef) _
            _ = _ := by ring
  have hI : 0 ≤ ∫ x, |F x| ^ p ∂μ := integral_nonneg (fun x => by positivity)
  have hR : 0 ≤ (∫ x, F x ^ 2 ∂μ) + C * (p - 2) := by positivity
  have hroot : (∫ x, |F x| ^ p ∂μ) ^ (1 / p) ≤
      Real.sqrt ((∫ x, F x ^ 2 ∂μ) + C * (p - 2)) := by
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (∫ x, |F x| ^ p ∂μ) ^ (2 / p))
      hsharp (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have hleft : ((∫ x, |F x| ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) =
        (∫ x, |F x| ^ p ∂μ) ^ (1 / p) := by
      calc
        _ = (∫ x, |F x| ^ p ∂μ) ^ ((2 / p) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul hI (2 / p) (1 / 2 : ℝ)).symm
        _ = _ := by congr 1; field_simp
    rw [hleft, ← Real.sqrt_eq_rpow] at hpow
    exact hpow
  have hformula := hFmem.eLpNorm_eq_integral_rpow_norm
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0 < p))) ENNReal.ofReal_ne_top
  have hEqInt : (∫ x, ‖F x‖ ^ p ∂μ) = ∫ x, |F x| ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
  calc
    eLpNorm' F p μ = eLpNorm F (ENNReal.ofReal p) μ := by
      rw [eLpNorm_eq_eLpNorm' (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)))
        ENNReal.ofReal_ne_top]
      simp [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
    _ = ENNReal.ofReal ((∫ x, ‖F x‖ ^ (ENNReal.ofReal p).toReal ∂μ) ^
        (ENNReal.ofReal p).toReal⁻¹) := hformula
    _ = ENNReal.ofReal ((∫ x, |F x| ^ p ∂μ) ^ (1 / p)) := by
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p), ← hEqInt]
      congr 1; congr 1; norm_num [one_div]
    _ ≤ ENNReal.ofReal (Real.sqrt ((∫ x, F x ^ 2 ∂μ) + C * (p - 2))) :=
      ENNReal.ofReal_le_ofReal hroot

/-- Sharp unbounded norm moment bound obtained from the accepted bounded
noncentered theorem by the literal clipped-mollified sequence and Fatou. -/
theorem unboundedSharpNormMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))) := by
  have hp_pos : 0 < p := by linarith
  have hsecond := normClipThenMollify_sq_integral_tendsto μ hmoment
  have hcoef : 0 ≤ C * (p - 2) := mul_nonneg hC (by linarith)
  have hplus : Tendsto
      (fun j => (∫ x, normClipThenMollify (ι := ι) j x ^ 2 ∂μ) + C * (p - 2))
      atTop (𝓝 ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))) := by
    exact hsecond.add_const _
  have hroot : Tendsto
      (fun j => Real.sqrt ((∫ x, normClipThenMollify (ι := ι) j x ^ 2 ∂μ) + C * (p - 2)))
      atTop (𝓝 (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2)))) := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp hplus
  have hboundTendsto : Tendsto
      (fun j => ENNReal.ofReal (Real.sqrt
        ((∫ x, normClipThenMollify (ι := ι) j x ^ 2 ∂μ) + C * (p - 2))))
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt
        ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hroot
  have hFatou : eLpNorm' (fun x : EuclideanSpace ℝ ι => ‖x‖) p μ ≤
      Filter.liminf (fun j => eLpNorm' (normClipThenMollify (ι := ι) j) p μ) atTop := by
    exact Lp.eLpNorm'_lim_le_liminf_eLpNorm' hp_pos (μ := μ)
      (f := fun j x => normClipThenMollify (ι := ι) j x)
      (f_lim := fun x => ‖x‖)
      (fun j => (normClipThenMollify_bounded_smooth (ι := ι) j).1.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => normClipThenMollify_tendsto x)
  have hlim : Filter.liminf
      (fun j => eLpNorm' (normClipThenMollify (ι := ι) j) p μ) atTop ≤
      ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))) := by
    calc
      _ ≤ Filter.liminf (fun j => ENNReal.ofReal (Real.sqrt
          ((∫ x, normClipThenMollify (ι := ι) j x ^ 2 ∂μ) + C * (p - 2)))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j =>
          normClipThenMollify_eLpNorm_bound μ C hC hLC hp j)
      _ = ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))) :=
        hboundTendsto.liminf_eq
  have hnormbound : eLpNorm' (fun x : EuclideanSpace ℝ ι => ‖x‖) p μ ≤
      ENNReal.ofReal (Real.sqrt ((∫ x, ‖x‖ ^ 2 ∂μ) + C * (p - 2))) :=
    hFatou.trans hlim
  have hpENN0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hpENNtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hmem : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ := by
    refine ⟨continuous_norm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_eLpNorm' hpENN0 hpENNtop]
    rw [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)]
    exact hnormbound.trans_lt ENNReal.ofReal_lt_top
  constructor
  · exact hmem
  · rw [eLpNorm_eq_eLpNorm' hpENN0 hpENNtop]
    rw [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)]
    exact hnormbound


/-- Exact same-constant sharp moment on each ordered independent product of
`r + 1` observations. Product probability, tensorized intrinsic LSI, and the
product second moment are discharged inside this consumer. -/
theorem orderedProductNormSharp
    {k m r : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := r + 1) μ) ∧
      eLpNorm (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := r + 1) μ) ≤
        ENNReal.ofReal (Real.sqrt (((r + 1 : ℕ) : ℝ) *
          (∫ z, LOOConcentration.observationNormSq z ∂μ) +
            (observationLogSobolevConstant μ).toReal * (p - 2))) := by
  let μE := μ.map LOOConcentration.observationToEuclidean
  let ν := datasetLawOfObservation (r := r + 1) μ
  let C := (observationLogSobolevConstant μ).toReal
  have hprobE : IsProbabilityMeasure μE := by
    exact Measure.isProbabilityMeasure_map
      LOOConcentration.Revision.measurable_observationToEuclidean.aemeasurable
  let _ : IsProbabilityMeasure μE := hprobE
  have hfiniteE : logSobolevConstant μE < ⊤ := by
    simpa [μE, observationLogSobolevConstant] using hfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLCbase : logSobolevConstant μE ≤ ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hfiniteE.ne).symm.le
  let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  let _ : IsProbabilityMeasure (euclideanProductLaw (κ := Fin (r + 1)) μE) :=
    euclideanProductLaw_isProbabilityMeasure μE
  have hprod : logSobolevConstant (euclideanProductLaw (κ := Fin (r + 1)) μE) ≤
      logSobolevConstant μE := by
    simpa using logSobolevConstant_euclideanProductLaw_le r μE hfiniteE
  have hLCprod : logSobolevConstant ν ≤ ENNReal.ofReal C := by
    have h := hprod.trans hLCbase
    simpa [ν, ← euclideanProductLaw_observation_map_eq_datasetLaw μ] using h
  have hmomentν : Integrable
      (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖ ^ 2) ν :=
    integrable_datasetLaw_norm_sq μ hM2
  have hcore := unboundedSharpNormMoment ν C hC hLCprod hmomentν hp
  have hscale := integral_datasetLaw_norm_sq (r := r + 1) μ hM2
  constructor
  · simpa [ν] using hcore.1
  · have hb := hcore.2
    rw [hscale] at hb
    simpa [ν, C] using hb

/-- Pull back the ordered Euclidean product result to the exact frozen dataset
carrier and norm used by the moment roots. -/
theorem orderedDatasetNormSharp
    {k m r : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (LOOConcentration.datasetNorm (k := k) (m := m) (n := r + 1)) p
        (LOOConcentration.datasetProductLaw (k := k) (m := m) (n := r + 1) μ) ≤
      ENNReal.ofReal (Real.sqrt (((r + 1 : ℕ) : ℝ) *
        (∫ z, LOOConcentration.observationNormSq z ∂μ) +
          (observationLogSobolevConstant μ).toReal * (p - 2))) := by
  let ν := datasetLawOfObservation (r := r + 1) μ
  let π := LOOConcentration.datasetProductLaw (k := k) (m := m) (n := r + 1) μ
  let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  have hcore := orderedProductNormSharp (r := r) μ hfinite hM2 hp
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0 < p))
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpToReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal (by linarith : 0 ≤ p)
  have hmap : eLpNorm
      (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
        (ENNReal.ofReal p) ν =
      eLpNorm (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (r + 1) =>
        ‖LOOConcentration.datasetToEuclidean D‖) (ENNReal.ofReal p) π := by
    dsimp [ν, π, datasetLawOfObservation, LOOConcentration.datasetProductLaw]
    exact eLpNorm_map_measure continuous_norm.aestronglyMeasurable
      LOOConcentration.measurable_datasetToEuclidean.aemeasurable
  have hmap' : eLpNorm
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (r + 1) =>
        LOOConcentration.datasetNorm D) (ENNReal.ofReal p) π =
      eLpNorm (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
        (ENNReal.ofReal p) ν := by
    have hfun : (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (r + 1) =>
        LOOConcentration.datasetNorm D) =
        (fun D => ‖LOOConcentration.datasetToEuclidean D‖) := by
      funext D
      exact LOOConcentration.datasetNorm_eq_euclidean D
    rw [hfun]
    exact hmap.symm
  calc
    eLpNorm' (LOOConcentration.datasetNorm (k := k) (m := m) (n := r + 1)) p π =
        eLpNorm (LOOConcentration.datasetNorm (k := k) (m := m) (n := r + 1))
          (ENNReal.ofReal p) π := by
      rw [eLpNorm_eq_eLpNorm' hp0 hptop, hpToReal]
    _ = eLpNorm (fun x : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) => ‖x‖)
        (ENNReal.ofReal p) ν := hmap'
    _ ≤ ENNReal.ofReal (Real.sqrt (((r + 1 : ℕ) : ℝ) *
        (∫ z, LOOConcentration.observationNormSq z ∂μ) +
          (observationLogSobolevConstant μ).toReal * (p - 2))) := hcore.2

/-- Deleted-sample application with the exact frozen count `n + 1`. -/
theorem orderedDatasetNormSharp_deleted
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (LOOConcentration.datasetNorm (k := k) (m := m) (n := n + 1)) p
        (LOOConcentration.datasetProductLaw (k := k) (m := m) (n := n + 1) μ) ≤
      ENNReal.ofReal (Real.sqrt (((n + 1 : ℕ) : ℝ) *
        (∫ z, LOOConcentration.observationNormSq z ∂μ) +
          (observationLogSobolevConstant μ).toReal * (p - 2))) := by
  simpa using orderedDatasetNormSharp (r := n) μ hfinite hM2 hp

/-- Full-sample application with the exact frozen count `n + 2`. -/
theorem orderedDatasetNormSharp_full
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (LOOConcentration.datasetNorm (k := k) (m := m) (n := n + 2)) p
        (LOOConcentration.datasetProductLaw (k := k) (m := m) (n := n + 2) μ) ≤
      ENNReal.ofReal (Real.sqrt (((n + 2 : ℕ) : ℝ) *
        (∫ z, LOOConcentration.observationNormSq z ∂μ) +
          (observationLogSobolevConstant μ).toReal * (p - 2))) := by
  simpa [Nat.add_assoc] using orderedDatasetNormSharp (r := n + 1) μ hfinite hM2 hp

end LOOConcentration.Revision
