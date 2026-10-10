import LOOConcentration.FunctionalInequalities.OneSpacePoincare
import LOOConcentration.Geometry.NormTransport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Entropy expansion for the one-space Poincaré perturbation

This file proves the second-order entropy expansion for the perturbation
`1 + εg` and derives the one-observation Poincaré inequality from the frozen
logarithmic Sobolev inequality.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private abbrev OneObservationLip (k m : ℕ) :=
  {g : Observation (k + 1) (m + 1) → ℝ //
    ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |g w - g v| ≤ K * observationNorm (w - v)}

/-- The explicit local Lipschitz condition implies continuity in the product
topology because `observationNorm` is continuous at zero. -/
theorem oneObservationLip_continuous {k m : ℕ} (g : OneObservationLip k m) :
    Continuous g.1 := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨U, hU, K, hK, hLip⟩ := g.2 z
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have hnormContinuous :
      Continuous fun w : Observation (k + 1) (m + 1) => observationNorm (w - z) := by
    fun_prop [observationNorm, observationNormSq]
  have hnormAt : ContinuousAt
      (fun w : Observation (k + 1) (m + 1) => observationNorm (w - z)) z :=
    hnormContinuous.continuousAt
  have hnorm : Tendsto
      (fun w : Observation (k + 1) (m + 1) => observationNorm (w - z))
      (𝓝 z) (𝓝 0) := by
    simpa [observationNorm, observationNormSq] using
      hnormAt.tendsto
  have hscaled : Tendsto
      (fun w : Observation (k + 1) (m + 1) => K * observationNorm (w - z))
      (𝓝 z) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hnorm)
  have hbound : ∀ᶠ w in 𝓝 z,
      |g.1 w - g.1 z| ≤ K * observationNorm (w - z) := by
    filter_upwards [hU] with w hw
    exact hLip w hw z hzU
  have habs : Tendsto (fun w => |g.1 w - g.1 z|) (𝓝 z) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      hbound hscaled
  change Tendsto g.1 (𝓝 z) (𝓝 (g.1 z))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- Bounded locally Lipschitz tests are integrable under a probability measure. -/
theorem oneObservationLip_integrable_of_bounded
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] (g : OneObservationLip k m) {B : ℝ}
    (hbounded : ∀ z, |g.1 z| ≤ B) : Integrable g.1 μ := by
  apply Integrable.of_bound (oneObservationLip_continuous g).aestronglyMeasurable B
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using hbounded z

/-- A uniform third-order error bound for the scalar entropy density near one. -/
theorem one_add_entropyDensity_taylor_bound {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(1 + t) ^ 2 * Real.log ((1 + t) ^ 2) - (2 * t + 3 * t ^ 2)| ≤
      10 * |t| ^ 3 := by
  have hlogSeries := Real.abs_log_sub_add_sum_range_le
    (x := -t) (by rw [abs_neg]; linarith) 2
  have hlog : |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤
      |t| ^ 3 / (1 - |t|) := by
    convert hlogSeries using 1 <;> norm_num [Finset.sum_range_succ]
    all_goals ring_nf
  have hden : 0 < 1 - |t| := by linarith
  have hinv : (1 - |t|)⁻¹ ≤ 2 := by
    have hdiv : 1 / (1 - |t|) ≤ 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [ht]
    simpa [one_div] using hdiv
  have hlog' : |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ 2 * |t| ^ 3 := by
    calc
      |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ |t| ^ 3 / (1 - |t|) := hlog
      _ = |t| ^ 3 * (1 - |t|)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ |t| ^ 3 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * |t| ^ 3 := by ring
  have hpos : 0 < 1 + t := by
    have habs := abs_le.mp ht
    linarith
  have habsOne : |1 + t| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> have := abs_le.mp ht <;> linarith
  have hsqOne : (1 + t) ^ 2 ≤ 9 / 4 := by
    calc
      (1 + t) ^ 2 = |1 + t| ^ 2 := (sq_abs _).symm
      _ ≤ (3 / 2) ^ 2 := by gcongr
      _ = 9 / 4 := by norm_num
  let r : ℝ := Real.log (1 + t) - (t - t ^ 2 / 2)
  have hlogEq : Real.log (1 + t) = t - t ^ 2 / 2 + r := by
    dsimp [r]
    ring
  have hpoly :
      (1 + t) ^ 2 * Real.log ((1 + t) ^ 2) - (2 * t + 3 * t ^ 2) =
        -(t ^ 4) + 2 * (1 + t) ^ 2 * r := by
    rw [Real.log_pow, hlogEq]
    ring_nf
  have ht4 : |t| ^ 4 ≤ (1 / 2) * |t| ^ 3 := by
    calc
      |t| ^ 4 = |t| ^ 3 * |t| := by ring
      _ ≤ |t| ^ 3 * (1 / 2) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = (1 / 2) * |t| ^ 3 := by ring
  have hrem : |2 * (1 + t) ^ 2 * r| ≤ 9 * |t| ^ 3 := by
    calc
      |2 * (1 + t) ^ 2 * r| = 2 * (1 + t) ^ 2 * |r| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + t) ^ 2)]
      _ ≤ 2 * (9 / 4) * (2 * |t| ^ 3) := by
        gcongr
      _ = 9 * |t| ^ 3 := by ring
  rw [hpoly]
  calc
    |-(t ^ 4) + 2 * (1 + t) ^ 2 * r| ≤ |t| ^ 4 +
        |2 * (1 + t) ^ 2 * r| := by
      calc
        |-(t ^ 4) + 2 * (1 + t) ^ 2 * r| ≤
            |-(t ^ 4)| + |2 * (1 + t) ^ 2 * r| := abs_add_le _ _
        _ = |t| ^ 4 + |2 * (1 + t) ^ 2 * r| := by rw [abs_neg, abs_pow]
    _ ≤ (1 / 2) * |t| ^ 3 + 9 * |t| ^ 3 := add_le_add ht4 hrem
    _ ≤ 10 * |t| ^ 3 := by
      have hnonneg : 0 ≤ |t| ^ 3 := by positivity
      nlinarith

/-- A uniform quadratic remainder bound for the normalization term. -/
theorem one_add_mul_log_taylor_bound {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(1 + s) * Real.log (1 + s) - s| ≤ 4 * |s| ^ 2 := by
  have hlogSeries := Real.abs_log_sub_add_sum_range_le
    (x := -s) (by rw [abs_neg]; linarith) 1
  have hlog : |Real.log (1 + s) - s| ≤ |s| ^ 2 / (1 - |s|) := by
    convert hlogSeries using 1 <;> norm_num [Finset.sum_range_succ]
    all_goals ring_nf
  have hden : 0 < 1 - |s| := by linarith
  have hinv : (1 - |s|)⁻¹ ≤ 2 := by
    have hdiv : 1 / (1 - |s|) ≤ 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [hs]
    simpa [one_div] using hdiv
  have hlog' : |Real.log (1 + s) - s| ≤ 2 * |s| ^ 2 := by
    calc
      |Real.log (1 + s) - s| ≤ |s| ^ 2 / (1 - |s|) := hlog
      _ = |s| ^ 2 * (1 - |s|)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ |s| ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * |s| ^ 2 := by ring
  let r : ℝ := Real.log (1 + s) - s
  have hlogEq : Real.log (1 + s) = s + r := by
    dsimp [r]
    ring
  have habsOne : |1 + s| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> have := abs_le.mp hs <;> linarith
  have hpoly :
      (1 + s) * Real.log (1 + s) - s = s ^ 2 + (1 + s) * r := by
    rw [hlogEq]
    ring
  have hrem : |(1 + s) * r| ≤ 3 * |s| ^ 2 := by
    calc
      |(1 + s) * r| = |1 + s| * |r| := abs_mul _ _
      _ ≤ (3 / 2) * (2 * |s| ^ 2) :=
        mul_le_mul habsOne hlog' (abs_nonneg _) (by positivity)
      _ = 3 * |s| ^ 2 := by ring
  rw [hpoly]
  calc
    |s ^ 2 + (1 + s) * r| ≤ |s ^ 2| + |(1 + s) * r| := abs_add_le _ _
    _ = |s| ^ 2 + |(1 + s) * r| := by rw [abs_pow]
    _ ≤ |s| ^ 2 + 3 * |s| ^ 2 := add_le_add le_rfl hrem
    _ = 4 * |s| ^ 2 := by ring

/-- With an explicitly integrable mean-zero test, the squared perturbation
has the exact second-moment normalization. -/
theorem oneObservationPerturbation_sq_integral_eq
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] (g : OneObservationLip k m) (ε : ℝ)
    (hg : Integrable g.1 μ)
    (hgSq : Integrable (fun z => g.1 z ^ 2) μ)
    (hmean : ∫ z, g.1 z ∂μ = 0) :
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) =
      1 + ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
  have hconst : Integrable (fun _ : Observation (k + 1) (m + 1) => (1 : ℝ)) μ :=
    integrable_const _
  have hlin : Integrable (fun z => 2 * ε * g.1 z) μ := hg.const_mul _
  have hquad : Integrable (fun z => ε ^ 2 * g.1 z ^ 2) μ := hgSq.const_mul _
  have hpoint (z : Observation (k + 1) (m + 1)) :
      (oneObservationPerturbation g ε).1 z ^ 2 =
        1 + (2 * ε * g.1 z + ε ^ 2 * g.1 z ^ 2) := by
    simp only [oneObservationPerturbation]
    ring
  have hfun :
      (fun z : Observation (k + 1) (m + 1) =>
        1 + (2 * ε * g.1 z + ε ^ 2 * g.1 z ^ 2)) =
      (fun _ : Observation (k + 1) (m + 1) => (1 : ℝ)) +
        ((fun z => 2 * ε * g.1 z) + fun z => ε ^ 2 * g.1 z ^ 2) := by
    funext z
    rfl
  calc
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) =
        ∫ z, (1 + (2 * ε * g.1 z + ε ^ 2 * g.1 z ^ 2)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ _ : Observation (k + 1) (m + 1), (1 : ℝ) ∂μ) +
        ((∫ z, 2 * ε * g.1 z ∂μ) + ∫ z, ε ^ 2 * g.1 z ^ 2 ∂μ) := by
      rw [hfun, integral_add' hconst (hlin.add hquad), integral_add' hlin hquad]
    _ = 1 + ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
      simp [integral_const_mul, hmean]

/-- The unnormalized entropy density has a cubic integrated remainder around
the mean-zero perturbation. The first and second moments are explicit inputs
so every Bochner integral used here is justified. -/
theorem oneObservationPerturbation_entropyDensity_remainder_bound
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B ε : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : OneObservationLip k m)
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ)
    (hg : Integrable g.1 μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2) :
    |(∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
          Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
      3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤
        10 * |ε| ^ 3 * B ^ 3 := by
  obtain ⟨hgSq, _, _⟩ := hLSI.2 g hgEnergy
  obtain ⟨_, hEntropy, _⟩ :=
    oneObservationPerturbation_lsi_bound (C := C) (ε := ε) hLSI g hgEnergy
  let qlog : Observation (k + 1) (m + 1) → ℝ := fun z =>
    (oneObservationPerturbation g ε).1 z ^ 2 *
      Real.log ((oneObservationPerturbation g ε).1 z ^ 2)
  let linear : Observation (k + 1) (m + 1) → ℝ := fun z => 2 * ε * g.1 z
  let quadratic : Observation (k + 1) (m + 1) → ℝ := fun z => 3 * ε ^ 2 * g.1 z ^ 2
  let remainder := fun z => qlog z - (linear z + quadratic z)
  have hLinear : Integrable linear μ := by
    exact hg.const_mul (2 * ε)
  have hQuadratic : Integrable quadratic μ := by
    exact hgSq.const_mul (3 * ε ^ 2)
  have hRemainder : Integrable remainder μ := by
    exact hEntropy.sub (hLinear.add hQuadratic)
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
  have hlinearInt : (∫ z, linear z ∂μ) = 2 * ε * (∫ z, g.1 z ∂μ) := by
    exact integral_const_mul (2 * ε) g.1
  have hquadraticInt :
      (∫ z, quadratic z ∂μ) = 3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
    exact integral_const_mul (3 * ε ^ 2) (fun z => g.1 z ^ 2)
  have hremInt :
      (∫ z, remainder z ∂μ) =
        (∫ z, qlog z ∂μ) - 3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
    calc
      (∫ z, remainder z ∂μ) =
          (∫ z, qlog z ∂μ) -
            ((∫ z, linear z ∂μ) + ∫ z, quadratic z ∂μ) := by
        dsimp [remainder]
        change (∫ z, (qlog - (linear + quadratic)) z ∂μ) = _
        rw [integral_sub' hEntropy (hLinear.add hQuadratic),
          integral_add' hLinear hQuadratic]
      _ = (∫ z, qlog z ∂μ) - 3 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ) := by
        rw [hlinearInt, hquadraticInt, hmean]
        ring
  simpa only [hremInt, Real.norm_eq_abs, bound] using hnorm

/-- The normalization term has a quartic remainder after its exact second
moment identity. -/
theorem oneObservationPerturbation_normalization_remainder_bound
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] (g : OneObservationLip k m) (ε : ℝ)
    (hg : Integrable g.1 μ)
    (hgSq : Integrable (fun z => g.1 z ^ 2) μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hsmall : |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤ 1 / 2) :
    |(∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
        Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) -
      ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤
        4 * |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ^ 2 := by
  rw [oneObservationPerturbation_sq_integral_eq g ε hg hgSq hmean]
  exact one_add_mul_log_taylor_bound hsmall

/-- The normalized entropy has an explicit cubic-plus-quartic remainder. -/
theorem oneObservationPerturbation_entropy_remainder_bound
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B ε : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : OneObservationLip k m)
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ)
    (hg : Integrable g.1 μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (hsmall : |ε| * (B + 1) ≤ 1 / 2)
    (hsmallNorm : |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤ 1 / 2) :
    |((∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
          Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
        (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
          Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)) -
      2 * ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ≤
        10 * |ε| ^ 3 * B ^ 3 +
          4 * |ε ^ 2 * (∫ z, g.1 z ^ 2 ∂μ)| ^ 2 := by
  obtain ⟨hgSq, _, _⟩ := hLSI.2 g hgEnergy
  have hDensity := oneObservationPerturbation_entropyDensity_remainder_bound
    hLSI g hgEnergy hg hmean hbounded hsmall
  have hNorm := oneObservationPerturbation_normalization_remainder_bound
    g ε hg hgSq hmean hsmallNorm
  let density : ℝ := ∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
    Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ
  let normalization : ℝ := (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
    Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)
  let variance : ℝ := ∫ z, g.1 z ^ 2 ∂μ
  change |(density - normalization) - 2 * ε ^ 2 * variance| ≤ _
  calc
    |(density - normalization) - 2 * ε ^ 2 * variance| =
        |(density - 3 * ε ^ 2 * variance) -
        (normalization - ε ^ 2 * variance)| := by congr 1; ring
    _ ≤ |density - 3 * ε ^ 2 * variance| +
        |normalization - ε ^ 2 * variance| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (density - 3 * ε ^ 2 * variance) 0
              (normalization - ε ^ 2 * variance))
    _ ≤ 10 * |ε| ^ 3 * B ^ 3 +
        4 * |ε ^ 2 * variance| ^ 2 := add_le_add hDensity hNorm

/-- The normalized entropy of a bounded mean-zero perturbation converges to
twice its variance as the perturbation parameter tends to zero. -/
theorem oneObservationPerturbation_entropy_tendsto
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : OneObservationLip k m)
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ)
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
  obtain ⟨hgSq, _, _⟩ := hLSI.2 g hgEnergy
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
    filter_upwards [hlimit.eventually (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))]
      with ε hε
    exact le_of_lt hε
  have hsmallNorm : ∀ᶠ ε in 𝓝[≠] 0,
      |ε ^ 2 * variance| ≤ 1 / 2 := by
    have hcontinuous : Continuous fun ε : ℝ => |ε ^ 2 * variance| := by fun_prop
    have hlimit : Tendsto (fun ε : ℝ => |ε ^ 2 * variance|)
        (𝓝[≠] 0) (𝓝 0) := by
      have hAt : ContinuousAt (fun ε : ℝ => |ε ^ 2 * variance|) 0 :=
        hcontinuous.continuousAt
      simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlimit.eventually (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))]
      with ε hε
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
    have hrem := oneObservationPerturbation_entropy_remainder_bound
      hLSI g hgEnergy hg hmean hbounded hεsmall hεsmallNorm
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
      _ ≤ (10 * |ε| ^ 3 * B ^ 3 + 4 * |ε ^ 2 * variance| ^ 2) /
          ε ^ 2 := div_le_div_of_nonneg_right hrem' (le_of_lt hεpos)
      _ = error ε := by
        simpa only [add_div, error] using congrArg₂ (· + ·) hfirst hsecond
  have habsLimit : Tendsto
      (fun ε => |entropy ε / ε ^ 2 - 2 * variance|)
      (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      hratioBound herrorLimit
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habsLimit

/-- The one-observation Poincaré inequality follows from the frozen
logarithmic Sobolev inequality with the same constant. -/
theorem oneObservation_poincare_from_logSobolev
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : OneObservationLip k m)
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ)
    (hmean : ∫ z, g.1 z ∂μ = 0)
    (hbounded : ∀ z, |g.1 z| ≤ B) :
    (∫ z, g.1 z ^ 2 ∂μ) ≤
      C * (∫ z, observationLocalSlope g z ^ 2 ∂μ) := by
  let variance : ℝ := ∫ z, g.1 z ^ 2 ∂μ
  let energy : ℝ := ∫ z, observationLocalSlope g z ^ 2 ∂μ
  let entropyRatio : ℝ → ℝ := fun ε =>
    ((∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
      (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
        Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)) / ε ^ 2
  have hlimit := oneObservationPerturbation_entropy_tendsto
    hLSI g hgEnergy hmean hbounded
  have hlimit' : Tendsto entropyRatio (𝓝[≠] 0) (𝓝 (2 * variance)) := by
    simpa [entropyRatio, variance] using hlimit
  have hbound : ∀ᶠ ε in 𝓝[≠] 0, entropyRatio ε ≤ 2 * C * energy := by
    filter_upwards [self_mem_nhdsWithin] with ε hεne
    have hεne' : ε ≠ 0 := by simpa using hεne
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hεne'
    have hLSIbound := (oneObservationPerturbation_lsi_bound
      (C := C) (ε := ε) hLSI g hgEnergy).2.2
    have hquot :
        ((∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
            Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
          (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
            Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ)) /
          ε ^ 2 ≤ 2 * C * energy := by
      calc
        _ ≤ (2 * C * (ε ^ 2 * energy)) / ε ^ 2 :=
          div_le_div_of_nonneg_right hLSIbound (le_of_lt hεpos)
        _ = 2 * C * energy := by
          field_simp [hεne']
    simpa [entropyRatio, energy] using hquot
  have hlimBound : 2 * variance ≤ 2 * C * energy := le_of_tendsto hlimit' hbound
  change variance ≤ C * energy
  nlinarith

end LOOConcentration
