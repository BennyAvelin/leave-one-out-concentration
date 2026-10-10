import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
import LOOConcentration.FunctionalInequalities.OneSpacePoincareLimit

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology ENNReal

namespace LOOConcentration.Revision

private theorem intrinsic_entropy_density_remainder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    {B ε : ℝ} (g : EuclideanSpace ℝ ι → ℝ)
    (hg : Integrable g μ) (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hmean : ∫ x, g x ∂μ = 0) (hbounded : ∀ x, |g x| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2)
    (hqlog : Integrable (fun x => (1 + ε * g x) ^ 2 *
      Real.log ((1 + ε * g x) ^ 2)) μ) :
    |(∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ) -
      3 * ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ≤ 10 * |ε| ^ 3 * B ^ 3 := by
  let qlog : EuclideanSpace ℝ ι → ℝ := fun x =>
    (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2)
  let linear : EuclideanSpace ℝ ι → ℝ := fun x => 2 * ε * g x
  let quadratic : EuclideanSpace ℝ ι → ℝ := fun x => 3 * ε ^ 2 * g x ^ 2
  let remainder : EuclideanSpace ℝ ι → ℝ := fun x => qlog x - (linear x + quadratic x)
  have hLinear : Integrable linear μ := hg.const_mul (2 * ε)
  have hQuadratic : Integrable quadratic μ := hgSq.const_mul (3 * ε ^ 2)
  have hqlog' : Integrable qlog μ := hqlog
  let bound : ℝ := 10 * |ε| ^ 3 * B ^ 3
  have hPointwise (x : EuclideanSpace ℝ ι) : |remainder x| ≤ bound := by
    have ht : |ε * g x| ≤ 1 / 2 := by
      calc
        |ε * g x| = |ε| * |g x| := abs_mul _ _
        _ ≤ |ε| * B := mul_le_mul_of_nonneg_left (hbounded x) (abs_nonneg ε)
        _ ≤ |ε| * (B + 1) := by gcongr; linarith
        _ ≤ 1 / 2 := hsmall
    have hTaylor := LOOConcentration.one_add_entropyDensity_taylor_bound ht
    have hExpr : remainder x =
        (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) -
          (2 * (ε * g x) + 3 * (ε * g x) ^ 2) := by
      dsimp [remainder, qlog, linear, quadratic]
      ring
    have hTaylor' : |remainder x| ≤ 10 * |ε * g x| ^ 3 := by
      rw [hExpr]
      exact hTaylor
    have hproduct : |ε * g x| ≤ |ε| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbounded x) (abs_nonneg ε)
    calc
      |remainder x| ≤ 10 * |ε * g x| ^ 3 := hTaylor'
      _ ≤ 10 * (|ε| * B) ^ 3 := by gcongr
      _ = bound := by dsimp [bound]; rw [mul_pow]; ring
  have hnorm : ‖∫ x, remainder x ∂μ‖ ≤ bound := by
    calc
      ‖∫ x, remainder x ∂μ‖ ≤ ∫ _ : EuclideanSpace ℝ ι, bound ∂μ :=
        norm_integral_le_of_norm_le (integrable_const bound) <|
          Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs]
            exact hPointwise x
      _ = bound := by simp
  have hlinearInt : (∫ x, linear x ∂μ) = 2 * ε * (∫ x, g x ∂μ) :=
    integral_const_mul (2 * ε) g
  have hquadraticInt : (∫ x, quadratic x ∂μ) =
      3 * ε ^ 2 * (∫ x, g x ^ 2 ∂μ) :=
    integral_const_mul (3 * ε ^ 2) (fun x => g x ^ 2)
  have hremInt : (∫ x, remainder x ∂μ) =
      (∫ x, qlog x ∂μ) - 3 * ε ^ 2 * (∫ x, g x ^ 2 ∂μ) := by
    calc
      (∫ x, remainder x ∂μ) = (∫ x, qlog x ∂μ) -
          ((∫ x, linear x ∂μ) + ∫ x, quadratic x ∂μ) := by
        change (∫ x, (qlog - (linear + quadratic)) x ∂μ) = _
        rw [integral_sub' hqlog' (hLinear.add hQuadratic), integral_add' hLinear hQuadratic]
      _ = _ := by rw [hlinearInt, hquadraticInt, hmean]; ring
  simpa only [hremInt, Real.norm_eq_abs, bound, qlog] using hnorm

private theorem intrinsic_perturbation_sq_integral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (g : EuclideanSpace ℝ ι → ℝ) (ε : ℝ)
    (hg : Integrable g μ) (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hmean : ∫ x, g x ∂μ = 0) :
    (∫ x, (1 + ε * g x) ^ 2 ∂μ) = 1 + ε ^ 2 * (∫ x, g x ^ 2 ∂μ) := by
  have hconst : Integrable (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)) μ := integrable_const _
  have hlin : Integrable (fun x => 2 * ε * g x) μ := hg.const_mul _
  have hquad : Integrable (fun x => ε ^ 2 * g x ^ 2) μ := hgSq.const_mul _
  have hpoint (x : EuclideanSpace ℝ ι) :
      (1 + ε * g x) ^ 2 = 1 + (2 * ε * g x + ε ^ 2 * g x ^ 2) := by ring
  have hfun :
      (fun x : EuclideanSpace ℝ ι => 1 + (2 * ε * g x + ε ^ 2 * g x ^ 2)) =
        (fun _ => (1 : ℝ)) + ((fun x => 2 * ε * g x) + fun x => ε ^ 2 * g x ^ 2) := by
    funext x
    rfl
  calc
    (∫ x, (1 + ε * g x) ^ 2 ∂μ) =
        ∫ x, (1 + (2 * ε * g x + ε ^ 2 * g x ^ 2)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ _ : EuclideanSpace ℝ ι, (1 : ℝ) ∂μ) +
        ((∫ x, 2 * ε * g x ∂μ) + ∫ x, ε ^ 2 * g x ^ 2 ∂μ) := by
      rw [hfun, integral_add' hconst (hlin.add hquad), integral_add' hlin hquad]
    _ = 1 + ε ^ 2 * (∫ x, g x ^ 2 ∂μ) := by simp [integral_const_mul, hmean]

private theorem intrinsic_perturbation_entropy_remainder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    {B ε : ℝ} (g : EuclideanSpace ℝ ι → ℝ)
    (hg : Integrable g μ) (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hmean : ∫ x, g x ∂μ = 0) (hbounded : ∀ x, |g x| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2)
    (hqlog : Integrable (fun x => (1 + ε * g x) ^ 2 *
      Real.log ((1 + ε * g x) ^ 2)) μ)
    (hsmallNorm : |ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ≤ 1 / 2) :
    |((∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ) -
        (∫ x, (1 + ε * g x) ^ 2 ∂μ) *
          Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)) -
      2 * ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ≤
        10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ^ 2 := by
  have hDensity := intrinsic_entropy_density_remainder g hg hgSq hmean hbounded hsmall hqlog
  have hNorm : |((∫ x, (1 + ε * g x) ^ 2 ∂μ) *
        Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)) -
      ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ≤
      4 * |ε ^ 2 * (∫ x, g x ^ 2 ∂μ)| ^ 2 := by
    rw [intrinsic_perturbation_sq_integral g ε hg hgSq hmean]
    exact LOOConcentration.one_add_mul_log_taylor_bound hsmallNorm
  let density : ℝ := ∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ
  let normalization : ℝ := (∫ x, (1 + ε * g x) ^ 2 ∂μ) *
    Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)
  let variance : ℝ := ∫ x, g x ^ 2 ∂μ
  change |(density - normalization) - 2 * ε ^ 2 * variance| ≤ _
  calc
    |(density - normalization) - 2 * ε ^ 2 * variance| =
        |(density - 3 * ε ^ 2 * variance) - (normalization - ε ^ 2 * variance)| := by
      congr 1
      ring
    _ ≤ |density - 3 * ε ^ 2 * variance| + |normalization - ε ^ 2 * variance| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (density - 3 * ε ^ 2 * variance) 0
          (normalization - ε ^ 2 * variance))
    _ ≤ 10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * variance| ^ 2 := by
      exact add_le_add hDensity hNorm

private theorem intrinsic_entropy_ratio_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (g : EuclideanSpace ℝ ι → ℝ)
    (hgCont : Continuous g) (hmean : ∫ x, g x ∂μ = 0)
    (hbounded : ∀ x, |g x| ≤ B) :
    Tendsto
      (fun ε => ((∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ) -
        (∫ x, (1 + ε * g x) ^ 2 ∂μ) *
          Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (2 * (∫ x, g x ^ 2 ∂μ))) := by
  have hg : Integrable g μ := by
    apply Integrable.of_bound hgCont.aestronglyMeasurable B
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hbounded x
  have hgSq : Integrable (fun x => g x ^ 2) μ := by
    let sq : EuclideanSpace ℝ ι → ℝ := fun x => g x ^ 2
    have hsqCont : Continuous sq := by dsimp [sq]; fun_prop
    apply Integrable.of_bound hsqCont.aestronglyMeasurable (B ^ 2)
    filter_upwards [] with x
    change ‖g x ^ 2‖ ≤ B ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    have hprod : 0 ≤ (B - |g x|) * (B + |g x|) :=
      mul_nonneg (sub_nonneg.mpr (hbounded x))
        (add_nonneg hB (abs_nonneg (g x)))
    nlinarith [hprod]
  let variance : ℝ := ∫ x, g x ^ 2 ∂μ
  let entropy : ℝ → ℝ := fun ε =>
    (∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ) -
      (∫ x, (1 + ε * g x) ^ 2 ∂μ) *
        Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)
  change Tendsto (fun ε => entropy ε / ε ^ 2) (𝓝[≠] 0) (𝓝 (2 * variance))
  have hsmall : ∀ᶠ ε in 𝓝[≠] 0, |ε| * (B + 1) ≤ 1 / 2 := by
    have hcontinuous : Continuous fun ε : ℝ => |ε| * (B + 1) := by fun_prop
    have hlimit : Tendsto (fun ε : ℝ => |ε| * (B + 1)) (𝓝[≠] 0) (𝓝 0) := by
      have hAt : ContinuousAt (fun ε : ℝ => |ε| * (B + 1)) 0 := hcontinuous.continuousAt
      simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlimit.eventually (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))]
      with ε hε
    exact le_of_lt hε
  have hsmallNorm : ∀ᶠ ε in 𝓝[≠] 0, |ε ^ 2 * variance| ≤ 1 / 2 := by
    have hcontinuous : Continuous fun ε : ℝ => |ε ^ 2 * variance| := by fun_prop
    have hlimit : Tendsto (fun ε : ℝ => |ε ^ 2 * variance|) (𝓝[≠] 0) (𝓝 0) := by
      have hAt : ContinuousAt (fun ε : ℝ => |ε ^ 2 * variance|) 0 := hcontinuous.continuousAt
      simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlimit.eventually (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))]
      with ε hε
    exact le_of_lt hε
  let error : ℝ → ℝ := fun ε => 10 * |ε| * B ^ 3 + 4 * ε ^ 2 * variance ^ 2
  have herrorLimit : Tendsto error (𝓝[≠] 0) (𝓝 0) := by
    have hcontinuous : Continuous error := by dsimp [error]; fun_prop
    have hAt : ContinuousAt error 0 := hcontinuous.continuousAt
    simpa [error] using hAt.tendsto.mono_left nhdsWithin_le_nhds
  have hratioBound : ∀ᶠ ε in 𝓝[≠] 0, |entropy ε / ε ^ 2 - 2 * variance| ≤ error ε := by
    filter_upwards [self_mem_nhdsWithin, hsmall, hsmallNorm] with ε hεne hεsmall hεsmallNorm
    have hεne' : ε ≠ 0 := by simpa using hεne
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hεne'
    let q : EuclideanSpace ℝ ι → ℝ := fun x => 1 + ε * g x
    let Bq : ℝ := 1 + |ε| * B
    have hqBound : ∀ x, |q x| ≤ Bq := by
      intro x
      calc
        |q x| = |1 + ε * g x| := rfl
        _ ≤ |1| + |ε * g x| := abs_add_le _ _
        _ = 1 + |ε| * |g x| := by rw [abs_one, abs_mul]
        _ ≤ 1 + |ε| * B := by gcongr; exact hbounded x
        _ = Bq := rfl
    have hqlog : Integrable (fun x => q x ^ 2 * Real.log (q x ^ 2)) μ := by
      let φ : ℝ → ℝ := fun x => x ^ 2 * Real.log (x ^ 2)
      have hφ : Continuous φ := by dsimp [φ]; exact Real.continuous_mul_log.comp (by fun_prop)
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (s := Set.Icc (-Bq) Bq) hφ.continuousOn
      let M' : ℝ := max M 0
      have hqCont : Continuous q := by dsimp [q]; fun_prop
      have hmeas : Measurable (fun x => φ (q x)) := hφ.measurable.comp hqCont.measurable
      apply Integrable.of_bound hmeas.aestronglyMeasurable M'
      filter_upwards [] with x
      have hx : q x ∈ Set.Icc (-Bq) Bq := abs_le.mp (hqBound x)
      have hφbound : ‖φ (q x)‖ ≤ M := hM (q x) hx
      dsimp [M']
      exact hφbound.trans (le_max_left _ _)
    have hrem := intrinsic_perturbation_entropy_remainder g hg hgSq hmean hbounded
      hεsmall hqlog hεsmallNorm
    have hrem' : |entropy ε - 2 * ε ^ 2 * variance| ≤
        10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * variance| ^ 2 := by
      simpa [entropy, variance, q, mul_assoc] using hrem
    have hratioEq : entropy ε / ε ^ 2 - 2 * variance =
        (entropy ε - 2 * ε ^ 2 * variance) / ε ^ 2 := by
      field_simp [hεne']
    have hfirst : (10 * |ε| ^ 3 * B ^ 3) / ε ^ 2 = 10 * |ε| * B ^ 3 := by
      have hpow : |ε| ^ 3 = |ε| * ε ^ 2 := by
        calc
          |ε| ^ 3 = |ε| * |ε| ^ 2 := by ring
          _ = |ε| * ε ^ 2 := by rw [sq_abs]
      rw [hpow]
      field_simp [hεne']
    have hsecond : (4 * |ε ^ 2 * variance| ^ 2) / ε ^ 2 =
        4 * ε ^ 2 * variance ^ 2 := by
      rw [sq_abs]
      field_simp [hεne']
    calc
      |entropy ε / ε ^ 2 - 2 * variance| =
          |(entropy ε - 2 * ε ^ 2 * variance) / ε ^ 2| := by rw [hratioEq]
      _ = |entropy ε - 2 * ε ^ 2 * variance| / ε ^ 2 := by
        rw [abs_div, abs_of_pos hεpos]
      _ ≤ (10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * variance| ^ 2) / ε ^ 2 :=
        div_le_div_of_nonneg_right hrem' (le_of_lt hεpos)
      _ = error ε := by
        simpa only [add_div, error] using congrArg₂ (· + ·) hfirst hsecond
  have habsLimit : Tendsto (fun ε => |entropy ε / ε ^ 2 - 2 * variance|)
      (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hratioBound herrorLimit
  exact (tendsto_iff_norm_sub_tendsto_zero).2 <| by
    simpa only [Real.norm_eq_abs] using habsLimit

/-- The actual retained Euclidean gradient controls the variance of every
bounded smooth scalar generator, with the same nonnegative optimal LSI
constant. -/
theorem bounded_smooth_intrinsic_poincare
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) :
    Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ ∧
      (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
        C * (∫ x, ‖gradient F x‖ ^ 2 ∂μ) := by
  have hFcont : Continuous F := hF.continuous
  have hFint : Integrable F μ := by
    apply Integrable.of_bound hFcont.aestronglyMeasurable B
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using (hbound x).1
  let mean : ℝ := ∫ x, F x ∂μ
  have hmeanBound : |mean| ≤ B := by
    calc
      |mean| = |∫ x, F x ∂μ| := rfl
      _ ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, B ∂μ := by
        apply integral_mono_ae hFint.abs (integrable_const B)
        exact Filter.Eventually.of_forall fun x => (hbound x).1
      _ = B := by simp
  let g : EuclideanSpace ℝ ι → ℝ := fun x => F x - mean
  have hgCont : Continuous g := by dsimp [g]; fun_prop
  have hmeanZero : ∫ x, g x ∂μ = 0 := by
    have hconst : Integrable (fun _ : EuclideanSpace ℝ ι => mean) μ := integrable_const _
    have hfun : g = F - fun _ => mean := by funext x; rfl
    rw [hfun, integral_sub' hFint hconst]
    simp [mean]
  have hgBound : ∀ x, |g x| ≤ 2 * B := by
    intro x
    calc
      |g x| = |F x - mean| := rfl
      _ ≤ |F x| + |mean| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbound x).1 hmeanBound
      _ = 2 * B := by ring
  have hgSq : Integrable (fun x => g x ^ 2) μ := by
    apply Integrable.of_bound (hgCont.pow 2).aestronglyMeasurable ((2 * B) ^ 2)
    filter_upwards [] with x
    change ‖g x ^ 2‖ ≤ (2 * B) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    have hprod : 0 ≤ (2 * B - |g x|) * (2 * B + |g x|) :=
      mul_nonneg (sub_nonneg.mpr (hgBound x))
        (add_nonneg (mul_nonneg (by norm_num) hB) (abs_nonneg (g x)))
    nlinarith [hprod]
  have hgradCont : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have henergyInt : Integrable (fun x => ‖gradient F x‖ ^ 2) μ := by
    apply Integrable.of_bound (hgradCont.norm.pow 2).aestronglyMeasurable (B ^ 2)
    filter_upwards [] with x
    change ‖(‖gradient F x‖) ^ 2‖ ≤ B ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hprod : 0 ≤ (B - ‖gradient F x‖) * (B + ‖gradient F x‖) :=
      mul_nonneg (sub_nonneg.mpr (hbound x).2)
        (add_nonneg hB (norm_nonneg _))
    nlinarith [hprod]
  let variance : ℝ := ∫ x, g x ^ 2 ∂μ
  let energy : ℝ := ∫ x, ‖gradient F x‖ ^ 2 ∂μ
  have hlimit := intrinsic_entropy_ratio_tendsto
    (μ := μ) (g := g) (B := 2 * B)
    (mul_nonneg (by norm_num) hB) hgCont hmeanZero hgBound
  let entropyRatio : ℝ → ℝ := fun ε =>
    ((∫ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) ∂μ) -
      (∫ x, (1 + ε * g x) ^ 2 ∂μ) *
        Real.log (∫ x, (1 + ε * g x) ^ 2 ∂μ)) / ε ^ 2
  have hlimit' : Tendsto entropyRatio (𝓝[≠] 0) (𝓝 (2 * variance)) := by
    simpa [entropyRatio, variance] using hlimit
  have hboundRatio : ∀ᶠ ε in 𝓝[≠] 0, entropyRatio ε ≤ 2 * C * energy := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεne : ε ≠ 0 := by simpa using hε
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hεne
    let q : EuclideanSpace ℝ ι → ℝ := fun x => 1 + ε * g x
    let Bq : ℝ := 1 + |ε| * (2 * B)
    have hqContDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q := by
      dsimp [q, g]
      fun_prop
    have hgradQ : ∀ x, gradient q x = ε • gradient F x := by
      intro x
      rw [gradient, gradient]
      change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm
          (fderiv ℝ (fun y => 1 + ε * (F y - mean)) x) = ε •
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ F x)
      have hdF : DifferentiableAt ℝ F x := hF.contDiffAt.differentiableAt (by simp)
      rw [fderiv_const_add 1, fderiv_const_mul (hdF.sub_const mean) ε,
        fderiv_sub_const mean]
      exact map_smul _ _ _
    have hqbound : ∀ x, |q x| ≤ Bq ∧ ‖gradient q x‖ ≤ Bq := by
      intro x
      constructor
      · calc
          |q x| = |1 + ε * g x| := rfl
          _ ≤ |1| + |ε * g x| := abs_add_le _ _
          _ = 1 + |ε| * |g x| := by rw [abs_one, abs_mul]
          _ ≤ 1 + |ε| * (2 * B) := by gcongr; exact hgBound x
          _ = Bq := rfl
      · calc
          ‖gradient q x‖ = ‖ε • gradient F x‖ := by rw [hgradQ x]
          _ = |ε| * ‖gradient F x‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |ε| * B := mul_le_mul_of_nonneg_left (hbound x).2 (abs_nonneg ε)
          _ ≤ Bq := by dsimp [Bq]; nlinarith [abs_nonneg ε, hB]
    have hBq : 0 ≤ Bq := by dsimp [Bq]; positivity
    have hActual := bounded_smooth_entropy_le_of_logSobolevConstant_le
      μ C hC hLC q hqContDiff Bq hBq hqbound
    have hgradSq (x : EuclideanSpace ℝ ι) :
        ‖gradient q x‖ ^ 2 = ε ^ 2 * ‖gradient F x‖ ^ 2 := by
      rw [hgradQ x, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hqEnergy : (∫ x, ‖gradient q x‖ ^ 2 ∂μ) = ε ^ 2 * energy := by
      calc
        (∫ x, ‖gradient q x‖ ^ 2 ∂μ) =
            ∫ x, ε ^ 2 * ‖gradient F x‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hgradSq
        _ = ε ^ 2 * energy := by
          simpa only [energy] using
            (integral_const_mul (ε ^ 2) (fun x => ‖gradient F x‖ ^ 2))
    have hActual' :
        (∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ) -
          (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ) ≤
            2 * C * (ε ^ 2 * energy) := by
      simpa only [q, hqEnergy] using hActual
    change
      ((∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ) -
        (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ)) / ε ^ 2 ≤ _
    calc
      _ ≤ (2 * C * (ε ^ 2 * energy)) / ε ^ 2 :=
        div_le_div_of_nonneg_right hActual' (le_of_lt hεpos)
      _ = 2 * C * energy := by field_simp [hεne]
  have hlimitBound : 2 * variance ≤ 2 * C * energy := le_of_tendsto hlimit' hboundRatio
  refine ⟨?_, ?_⟩
  · simpa [g, mean] using hgSq
  · change variance ≤ C * energy
    nlinarith [hlimitBound]

example (μ : Measure (EuclideanSpace ℝ Empty)) [IsProbabilityMeasure μ]
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal 0) (c : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ Empty =>
      ((fun _ => c) x - ∫ y, (fun _ => c) y ∂μ) ^ 2) μ := by
  let F : EuclideanSpace ℝ Empty → ℝ := fun _ => c
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    dsimp [F]
    exact contDiff_const
  have hbound : ∀ x, |F x| ≤ |c| ∧ ‖gradient F x‖ ≤ |c| := by
    intro x
    constructor
    · simp [F]
    · simp [F, gradient]
  exact (bounded_smooth_intrinsic_poincare μ 0 (by norm_num) hLC F hF |c|
    (abs_nonneg c) hbound).1

end LOOConcentration.Revision
