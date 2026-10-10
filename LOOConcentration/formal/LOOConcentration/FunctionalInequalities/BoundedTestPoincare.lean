import LOOConcentration.FunctionalInequalities.OneSpacePoincareLimit
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Same-constant Poincaré from a bounded-test entropy inequality

This module derives the Poincaré inequality for bounded locally Lipschitz
observation tests from the corresponding bounded-test logarithmic Sobolev
inequality.  The latter remains an explicit analytic input; no full
`HasLogSobolev` hypothesis is used by the derivation.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private abbrev BoundedObservationTest (k m : ℕ) :=
  {f : Observation (k + 1) (m + 1) → ℝ //
    ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |f w - f v| ≤ K * observationNorm (w - v)}

private theorem boundedTest_integrable_square
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] (u : BoundedObservationTest k m) {B : ℝ}
    (hB : ∀ z, |u.1 z| ≤ B) :
    Integrable (fun z => u.1 z ^ 2) μ := by
  have hBnonneg : 0 ≤ B := (abs_nonneg (u.1 0)).trans (hB 0)
  have hcont : Continuous (fun z => u.1 z ^ 2) :=
    (oneObservationLip_continuous u).pow 2
  apply Integrable.of_bound hcont.aestronglyMeasurable (B ^ 2)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rw [← sq_abs (u.1 z)]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hB z))
    (add_nonneg hBnonneg (abs_nonneg (u.1 z)))]

private theorem boundedTest_integrable_entropyDensity
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] (u : BoundedObservationTest k m) {B : ℝ}
    (hB : ∀ z, |u.1 z| ≤ B) :
    Integrable (fun z => u.1 z ^ 2 * Real.log (u.1 z ^ 2)) μ := by
  let φ : ℝ → ℝ := fun x => x ^ 2 * Real.log (x ^ 2)
  have hφ : Continuous φ := by
    dsimp [φ]
    exact Real.continuous_mul_log.comp (by fun_prop)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-B) B) hφ.continuousOn
  let M' := max M 0
  have hmeas : Measurable (fun z => φ (u.1 z)) :=
    hφ.measurable.comp (oneObservationLip_continuous u).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable M'
  filter_upwards [] with z
  have hz : u.1 z ∈ Set.Icc (-B) B := abs_le.mp (hB z)
  have hφbound : ‖φ (u.1 z)‖ ≤ M := hM (u.1 z) hz
  dsimp [M']
  exact hφbound.trans (le_max_left _ _)

private theorem boundedTest_entropyDensity_remainder_bound
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {B ε : ℝ}
    (g : BoundedObservationTest k m)
    (hg : Integrable g.1 μ)
    (hgSq : Integrable (fun z => g.1 z ^ 2) μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2)
    (hqlog : Integrable
      (fun z => (oneObservationPerturbation g ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation g ε).1 z ^ 2)) μ) :
    |(∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
          Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
      3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤
        10 * |ε| ^ 3 * B ^ 3 := by
  let qlog : Observation (k + 1) (m + 1) → ℝ := fun z =>
    (oneObservationPerturbation g ε).1 z ^ 2 *
      Real.log ((oneObservationPerturbation g ε).1 z ^ 2)
  let linear : Observation (k + 1) (m + 1) → ℝ := fun z =>
    2 * ε * g.1 z
  let quadratic : Observation (k + 1) (m + 1) → ℝ := fun z =>
    3 * ε ^ 2 * g.1 z ^ 2
  let remainder := fun z => qlog z - (linear z + quadratic z)
  have hLinear : Integrable linear μ := hg.const_mul (2 * ε)
  have hQuadratic : Integrable quadratic μ := hgSq.const_mul (3 * ε ^ 2)
  have hRemainder : Integrable remainder μ := by
    exact hqlog.sub (hLinear.add hQuadratic)
  have hB : 0 ≤ B := (abs_nonneg (g.1 0)).trans (hbounded 0)
  let bound : ℝ := 10 * |ε| ^ 3 * B ^ 3
  have hPointwise (z : Observation (k + 1) (m + 1)) :
      |remainder z| ≤ bound := by
    have ht : |ε * g.1 z| ≤ 1 / 2 := by
      calc
        |ε * g.1 z| = |ε| * |g.1 z| := abs_mul _ _
        _ ≤ |ε| * B := mul_le_mul_of_nonneg_left (hbounded z) (abs_nonneg ε)
        _ ≤ |ε| * (B + 1) := by gcongr; linarith
        _ ≤ 1 / 2 := hsmall
    have hTaylor := one_add_entropyDensity_taylor_bound ht
    have hExpr : remainder z =
        (1 + ε * g.1 z) ^ 2 * Real.log ((1 + ε * g.1 z) ^ 2) -
          (2 * (ε * g.1 z) + 3 * (ε * g.1 z) ^ 2) := by
      dsimp [remainder, qlog, linear, quadratic, oneObservationPerturbation]
      ring
    have hTaylor' : |remainder z| ≤ 10 * |ε * g.1 z| ^ 3 := by
      rw [hExpr]
      exact hTaylor
    have hproduct : |ε * g.1 z| ≤ |ε| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbounded z) (abs_nonneg ε)
    calc
      |remainder z| ≤ 10 * |ε * g.1 z| ^ 3 := hTaylor'
      _ ≤ 10 * (|ε| * B) ^ 3 := by gcongr
      _ = bound := by
        dsimp [bound]
        rw [mul_pow]
        ring
  have hnorm : ‖∫ z, remainder z ∂μ‖ ≤ bound := by
    calc
      ‖∫ z, remainder z ∂μ‖ ≤ ∫ _ : Observation (k + 1) (m + 1), bound ∂μ :=
        norm_integral_le_of_norm_le (integrable_const bound) <|
          Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs]
            exact hPointwise z
      _ = bound := by simp
  have hlinearInt : (∫ z, linear z ∂μ) = 2 * ε * (∫ z, g.1 z ∂μ) :=
    integral_const_mul (2 * ε) g.1
  have hquadraticInt :
      (∫ z, quadratic z ∂μ) = 3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) :=
    integral_const_mul (3 * ε ^ 2) (fun z => g.1 z ^ 2)
  have hremInt :
      (∫ z, remainder z ∂μ) =
        (∫ z, qlog z ∂μ) - 3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
    calc
      (∫ z, remainder z ∂μ) =
          (∫ z, qlog z ∂μ) -
            ((∫ z, linear z ∂μ) + ∫ z, quadratic z ∂μ) := by
        dsimp [remainder]
        change (∫ z, (qlog - (linear + quadratic)) z ∂μ) = _
        rw [integral_sub' hqlog (hLinear.add hQuadratic),
          integral_add' hLinear hQuadratic]
      _ = (∫ z, qlog z ∂μ) -
          3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
        rw [hlinearInt, hquadraticInt, hmean]
        ring
  simpa only [hremInt, Real.norm_eq_abs, bound] using hnorm

private theorem boundedTest_entropy_remainder_bound
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {B ε : ℝ}
    (g : BoundedObservationTest k m)
    (hg : Integrable g.1 μ)
    (hgSq : Integrable (fun z => g.1 z ^ 2) μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2)
    (hqlog : Integrable
      (fun z => (oneObservationPerturbation g ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation g ε).1 z ^ 2)) μ)
    (hsmallNorm : |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤ 1 / 2) :
    |((∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
          Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
        (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
          Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)) -
      2 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤
        10 * |ε| ^ 3 * B ^ 3 +
          4 * |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ^ 2 := by
  have hDensity := boundedTest_entropyDensity_remainder_bound
    g hg hgSq hmean hbounded hsmall hqlog
  have hNorm := oneObservationPerturbation_normalization_remainder_bound
    g ε hg hgSq hmean hsmallNorm
  let density : ℝ := ∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
    Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ
  let normalization : ℝ :=
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
      Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)
  let variance : ℝ := ∫ z, g.1 z ^ 2 ∂μ
  change |(density - normalization) - 2 * ε ^ 2 * variance| ≤ _
  calc
      |(density - normalization) - 2 * ε ^ 2 * variance| =
        |(density - 3 * ε ^ 2 * variance) -
          (normalization - ε ^ 2 * variance)| := by
        congr 1
        ring
    _ ≤ |density - 3 * ε ^ 2 * variance| +
        |normalization - ε ^ 2 * variance| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (density - 3 * ε ^ 2 * variance) 0
          (normalization - ε ^ 2 * variance))
    _ ≤ 10 * |ε| ^ 3 * B ^ 3 +
        4 * |ε ^ 2 * variance| ^ 2 := add_le_add hDensity hNorm

private theorem boundedTest_entropy_ratio_tendsto
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {B : ℝ}
    (g : BoundedObservationTest k m)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B) :
    Tendsto
      (fun ε =>
        ((∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
            Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
          (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
            Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)) /
          ε ^ 2)
      (𝓝[≠] 0) (𝓝 (2 * (∫ z, g.1 z ^ 2 ∂μ))) := by
  have hgSq : Integrable (fun z => g.1 z ^ 2) μ :=
    boundedTest_integrable_square g hbounded
  have hg : Integrable g.1 μ := oneObservationLip_integrable_of_bounded g hbounded
  let variance : ℝ := ∫ z, g.1 z ^ 2 ∂μ
  let entropy : ℝ → ℝ := fun ε =>
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
      (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
        Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)
  change Tendsto (fun ε => entropy ε / ε ^ 2)
    (𝓝[≠] 0) (𝓝 (2 * variance))
  have hsmall : ∀ᶠ ε in 𝓝[≠] 0, |ε| * (B + 1) ≤ 1 / 2 := by
    have hcontinuous : Continuous fun ε : ℝ => |ε| * (B + 1) := by fun_prop
    have hlimit : Tendsto (fun ε : ℝ => |ε| * (B + 1))
        (𝓝[≠] 0) (𝓝 0) := by
      have hAt : ContinuousAt (fun ε : ℝ => |ε| * (B + 1)) 0 :=
        hcontinuous.continuousAt
      simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlimit.eventually
      (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))] with ε hε
    exact le_of_lt hε
  have hsmallNorm : ∀ᶠ ε in 𝓝[≠] 0,
      |ε ^ 2 * variance| ≤ 1 / 2 := by
    have hcontinuous : Continuous fun ε : ℝ => |ε ^ 2 * variance| := by fun_prop
    have hlimit : Tendsto (fun ε : ℝ => |ε ^ 2 * variance|)
        (𝓝[≠] 0) (𝓝 0) := by
      have hAt : ContinuousAt (fun ε : ℝ => |ε ^ 2 * variance|) 0 :=
        hcontinuous.continuousAt
      simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlimit.eventually
      (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))] with ε hε
    exact le_of_lt hε
  let error : ℝ → ℝ := fun ε =>
    10 * |ε| * B ^ 3 + 4 * ε ^ 2 * variance ^ 2
  have herrorLimit : Tendsto error (𝓝[≠] 0) (𝓝 0) := by
    have hcontinuous : Continuous error := by
      dsimp [error]
      fun_prop
    have hAt : ContinuousAt error 0 := hcontinuous.continuousAt
    simpa [error] using hAt.tendsto.mono_left nhdsWithin_le_nhds
  have hratioBound : ∀ᶠ ε in 𝓝[≠] 0,
      |entropy ε / ε ^ 2 - 2 * variance| ≤ error ε := by
    filter_upwards [self_mem_nhdsWithin, hsmall, hsmallNorm]
      with ε hεne hεsmall hεsmallNorm
    have hεne' : ε ≠ 0 := by simpa using hεne
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hεne
    let q := oneObservationPerturbation g ε
    let Bq : ℝ := 1 + |ε| * B
    have hqBound : ∀ z, |q.1 z| ≤ Bq := by
      intro z
      calc
        |q.1 z| = |1 + ε * g.1 z| := rfl
        _ ≤ |1| + |ε * g.1 z| := abs_add_le _ _
        _ = 1 + |ε| * |g.1 z| := by rw [abs_one, abs_mul]
        _ ≤ 1 + |ε| * B := by gcongr; exact hbounded z
        _ = Bq := rfl
    have hqlog : Integrable
        (fun z => q.1 z ^ 2 * Real.log (q.1 z ^ 2)) μ := by
      simpa [q] using boundedTest_integrable_entropyDensity q hqBound
    have hrem := boundedTest_entropy_remainder_bound
      g hg hgSq hmean hbounded hεsmall hqlog hεsmallNorm
    have hrem' : |entropy ε - 2 * ε ^ 2 * variance| ≤
        10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * variance| ^ 2 := by
      simpa [entropy, variance, mul_assoc] using hrem
    have hratioEq : entropy ε / ε ^ 2 - 2 * variance =
        (entropy ε - 2 * ε ^ 2 * variance) / ε ^ 2 := by
      field_simp [hεne']
    have hfirst : (10 * |ε| ^ 3 * B ^ 3) / ε ^ 2 =
        10 * |ε| * B ^ 3 := by
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
      _ ≤ (10 * |ε| ^ 3 * B ^ 3 +
          4 * |ε ^ 2 * variance| ^ 2) / ε ^ 2 :=
        div_le_div_of_nonneg_right hrem' (le_of_lt hεpos)
      _ = error ε := by
        simpa only [add_div, error] using congrArg₂ (· + ·) hfirst hsecond
  have habsLimit : Tendsto
      (fun ε => |entropy ε / ε ^ 2 - 2 * variance|)
      (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      hratioBound herrorLimit
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habsLimit

/-- A bounded-test logarithmic Sobolev inequality implies the Poincaré
inequality with the same constant on the frozen positive-dimensional
observation carrier.  The universally quantified bounded-test entropy
inequality is the sole open analytic predecessor; its eventual Gaussian
producer is not supplied here. -/
theorem boundedTestPoincare_of_boundedEntropy
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 < C)
    (hBoundedEntropy : ∀ (u : BoundedObservationTest k m) (B : ℝ),
      (∀ z, |u.1 z| ≤ B) →
      Integrable (fun z => observationLocalSlope u z ^ 2) μ →
      (∫ z, u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂μ) -
          (∫ z, u.1 z ^ 2 ∂μ) *
            Real.log (∫ z, u.1 z ^ 2 ∂μ) ≤
        2 * C * (∫ z, observationLocalSlope u z ^ 2 ∂μ))
    (g : BoundedObservationTest k m) (B : ℝ)
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (henergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ) :
    Integrable
        (fun z => (g.1 z - ∫ y, g.1 y ∂μ) ^ 2) μ ∧
      (∫ z, (g.1 z - ∫ y, g.1 y ∂μ) ^ 2 ∂μ) ≤
        C * (∫ z, observationLocalSlope g z ^ 2 ∂μ) := by
  have hg : Integrable g.1 μ := oneObservationLip_integrable_of_bounded g hbounded
  have hAbsBound : (∫ z, |g.1 z| ∂μ) ≤ B := by
    calc
      (∫ z, |g.1 z| ∂μ) ≤ ∫ _ : Observation (k + 1) (m + 1), B ∂μ := by
        apply integral_mono_ae hg.abs (integrable_const B)
        exact Filter.Eventually.of_forall hbounded
      _ = B := by simp
  let mean : ℝ := ∫ y, g.1 y ∂μ
  have hmeanBound : |mean| ≤ B := by
    calc
      |mean| = |∫ z, g.1 z ∂μ| := rfl
      _ ≤ ∫ z, |g.1 z| ∂μ := abs_integral_le_integral_abs
      _ ≤ B := hAbsBound
  let gc : BoundedObservationTest k m := ⟨fun z => g.1 z - mean, by
    intro z
    obtain ⟨U, hU, K, hK, hLip⟩ := g.2 z
    refine ⟨U, hU, K, hK, ?_⟩
    intro w hw v hv
    calc
      |(g.1 w - mean) - (g.1 v - mean)| = |g.1 w - g.1 v| := by
        congr 1
        ring
      _ ≤ K * observationNorm (w - v) := hLip w hw v hv⟩
  have hgcBound : ∀ z, |gc.1 z| ≤ 2 * B := by
    intro z
    calc
      |gc.1 z| = |g.1 z - mean| := rfl
      _ ≤ |g.1 z| + |mean| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbounded z) hmeanBound
      _ = 2 * B := by ring
  have hgcInt : Integrable gc.1 μ := oneObservationLip_integrable_of_bounded gc hgcBound
  have hmeanZero : ∫ z, gc.1 z ∂μ = 0 := by
    have hconst : Integrable (fun _ : Observation (k + 1) (m + 1) => mean) μ :=
      integrable_const _
    have hfun : (fun z : Observation (k + 1) (m + 1) => gc.1 z) =
        (fun z => g.1 z) - fun _ => mean := by
      funext z
      rfl
    rw [hfun, integral_sub' hg hconst]
    simp [mean]
  have hgcSq : Integrable (fun z => gc.1 z ^ 2) μ :=
    boundedTest_integrable_square gc hgcBound
  have hslope (z : Observation (k + 1) (m + 1)) :
      observationLocalSlope gc z = observationLocalSlope g z := by
    change limsup
        (fun w => |(g.1 w - mean) - (g.1 z - mean)| /
          observationNorm (w - z)) (𝓝[≠] z) =
      limsup (fun w => |g.1 w - g.1 z| / observationNorm (w - z)) (𝓝[≠] z)
    apply congrArg (fun f => limsup f (𝓝[≠] z))
    funext w
    rw [show (g.1 w - mean) - (g.1 z - mean) = g.1 w - g.1 z by ring]
  have hgcEnergy : Integrable (fun z => observationLocalSlope gc z ^ 2) μ := by
    simpa only [hslope] using henergy
  have hlimit := boundedTest_entropy_ratio_tendsto gc hmeanZero hgcBound
  let variance : ℝ := ∫ z, gc.1 z ^ 2 ∂μ
  let energy : ℝ := ∫ z, observationLocalSlope g z ^ 2 ∂μ
  let entropyRatio : ℝ → ℝ := fun ε =>
    ((∫ z, (oneObservationPerturbation gc ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation gc ε).1 z ^ 2) ∂μ) -
      (∫ z, (oneObservationPerturbation gc ε).1 z ^ 2 ∂μ) *
        Real.log (∫ z, (oneObservationPerturbation gc ε).1 z ^ 2 ∂μ)) / ε ^ 2
  have hlimit' : Tendsto entropyRatio (𝓝[≠] 0) (𝓝 (2 * variance)) := by
    simpa [entropyRatio, variance] using hlimit
  have hbound : ∀ᶠ ε in 𝓝[≠] 0, entropyRatio ε ≤ 2 * C * energy := by
    filter_upwards [self_mem_nhdsWithin] with ε hεne
    have hεne' : ε ≠ 0 := by simpa using hεne
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hεne'
    let q := oneObservationPerturbation gc ε
    let Bq : ℝ := 1 + |ε| * (2 * B)
    have hqBound : ∀ z, |q.1 z| ≤ Bq := by
      intro z
      calc
        |q.1 z| = |1 + ε * gc.1 z| := rfl
        _ ≤ |1| + |ε * gc.1 z| := abs_add_le _ _
        _ = 1 + |ε| * |gc.1 z| := by rw [abs_one, abs_mul]
        _ ≤ 1 + |ε| * (2 * B) := by gcongr; exact hgcBound z
        _ = Bq := rfl
    have hqEnergy : Integrable
        (fun z => observationLocalSlope q z ^ 2) μ :=
      integrable_observationLocalSlope_sq_oneObservationPerturbation ε gc hgcEnergy
    have hqBoundedEntropy := hBoundedEntropy q Bq hqBound hqEnergy
    have hSlopeIntegral :
        (∫ z, observationLocalSlope q z ^ 2 ∂μ) = ε ^ 2 * energy := by
      calc
        (∫ z, observationLocalSlope q z ^ 2 ∂μ) =
            ∫ z, ε ^ 2 * observationLocalSlope gc z ^ 2 ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            change observationLocalSlope
              (oneObservationPerturbation gc ε) z ^ 2 = _
            rw [observationLocalSlope_oneObservationPerturbation_eq]
            calc
              (|ε| * observationLocalSlope gc z) ^ 2 =
                  |ε| ^ 2 * observationLocalSlope gc z ^ 2 := by ring
              _ = ε ^ 2 * observationLocalSlope gc z ^ 2 := by rw [sq_abs]
        _ = ε ^ 2 * (∫ z, observationLocalSlope gc z ^ 2 ∂μ) := by
          rw [integral_const_mul]
        _ = ε ^ 2 * energy := by
          congr 1
          simp only [energy]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by simp only [hslope]
    have hqBoundedEntropy' :
        (∫ z, q.1 z ^ 2 * Real.log (q.1 z ^ 2) ∂μ) -
            (∫ z, q.1 z ^ 2 ∂μ) * Real.log (∫ z, q.1 z ^ 2 ∂μ) ≤
          2 * C * (ε ^ 2 * energy) := by
      simpa only [hSlopeIntegral] using hqBoundedEntropy
    have hratioBound : entropyRatio ε ≤ 2 * C * energy := by
      change
        ((∫ z, q.1 z ^ 2 * Real.log (q.1 z ^ 2) ∂μ) -
          (∫ z, q.1 z ^ 2 ∂μ) * Real.log (∫ z, q.1 z ^ 2 ∂μ)) /
          ε ^ 2 ≤ _
      calc
        _ ≤ (2 * C * (ε ^ 2 * energy)) / ε ^ 2 :=
          div_le_div_of_nonneg_right hqBoundedEntropy' (le_of_lt hεpos)
        _ = 2 * C * energy := by
          field_simp [hεne']
    exact hratioBound
  have hlimBound : 2 * variance ≤ 2 * C * energy := le_of_tendsto hlimit' hbound
  refine ⟨?_, ?_⟩
  · simpa [gc, mean] using hgcSq
  · change variance ≤ C * energy
    nlinarith

end LOOConcentration

#print axioms LOOConcentration.boundedTestPoincare_of_boundedEntropy
