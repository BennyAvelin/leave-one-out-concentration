import LOOConcentration.Examples.GaussianBoundedPositiveLSI
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The Gaussian square log-Sobolev inequality for bounded smooth functions

This file removes the positive lower bound from the bounded-positive scalar
Gaussian LSI by applying it to `u^2 + ε` and taking an actual dominated limit.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology

private theorem integrable_of_measurable_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {K : ℝ}
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ K) :
    Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable K
    (Filter.Eventually.of_forall hbound)

private theorem exists_mul_log_norm_bound (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ Set.Icc (0 : ℝ) B, ‖z * Real.log z‖ ≤ K := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B) := isCompact_Icc
  have hcontinuous : Continuous (fun z : ℝ => ‖z * Real.log z‖) :=
    continuous_norm.comp Real.continuous_mul_log
  obtain ⟨K, hK0, hK⟩ :=
    hcompact.bddAbove_image hcontinuous.continuousOn |>.exists_ge 0
  refine ⟨K, hK0, ?_⟩
  intro z hz
  exact hK _ ⟨z, hz, rfl⟩

private noncomputable def gaussianXLogX (z : ℝ) : ℝ := z * Real.log z

private noncomputable def squareEpsilon (n : ℕ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => u x ^ 2 + 1 / ((n : ℝ) + 1)

private theorem squareEpsilon_parameter_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem deriv_square_add {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (c x : ℝ) :
    deriv (fun y => u y ^ 2 + c) x = 2 * u x * deriv u x := by
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have huAt : DifferentiableAt ℝ u x := huDiff x
  change deriv (u ^ 2 + fun _ => c) x = _
  rw [deriv_add (huAt.pow 2) (differentiableAt_const c)]
  simp [deriv_pow huAt]

private theorem second_deriv_square_add {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (c x : ℝ) :
    deriv (deriv (fun y => u y ^ 2 + c)) x =
      2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x := by
  have hfirst :
      deriv (fun y => u y ^ 2 + c) = fun y => 2 * u y * deriv u y := by
    funext y
    exact deriv_square_add hu c y
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have huAt : DifferentiableAt ℝ u x := huDiff x
  have huDeriv : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hderivDifferentiable : Differentiable ℝ (deriv u) :=
    huDeriv.differentiable (by norm_num)
  rw [hfirst]
  calc
    deriv (fun y => 2 * u y * deriv u y) x =
        deriv (fun y => 2 * u y) x * deriv u x +
          (2 * u x) * deriv (deriv u) x := by
            exact deriv_mul ((differentiableAt_const (2 : ℝ)).mul huAt)
              hderivDifferentiable.differentiableAt
    _ = 2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x := by
          rw [deriv_const_mul_field]
          ring

private theorem squareEpsilon_derivative {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (n : ℕ) (x : ℝ) :
    deriv (squareEpsilon n u) x = 2 * u x * deriv u x := by
  exact deriv_square_add hu _ x

private theorem squareEpsilon_second_derivative {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (n : ℕ) (x : ℝ) :
    deriv (deriv (squareEpsilon n u)) x =
      2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x := by
  exact second_deriv_square_add hu _ x

/-- For a bounded C² scalar function, its square, its `x log x` entropy
integrand, and its squared derivative are all genuinely integrable under the
standard Gaussian. -/
theorem standardGaussian_boundedSmooth_square_integrable
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {U D₁ D₂ : ℝ}
    (hU : ∀ x, ‖u x‖ ≤ U)
    (hD₁ : ∀ x, ‖deriv u x‖ ≤ D₁)
    (hD₂ : ∀ x, ‖deriv (deriv u) x‖ ≤ D₂) :
    Integrable (fun x => u x ^ 2) standardGaussianMehler ∧
      Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) standardGaussianMehler ∧
      Integrable (fun x => (deriv u x) ^ 2) standardGaussianMehler := by
  have hU0 : 0 ≤ U := le_trans (norm_nonneg (u 0)) (hU 0)
  have hD₁0 : 0 ≤ D₁ := le_trans (norm_nonneg (deriv u 0)) (hD₁ 0)
  have hD₂0 : 0 ≤ D₂ := le_trans (norm_nonneg (deriv (deriv u) 0)) (hD₂ 0)
  have hu_sq_bound (x : ℝ) : 0 ≤ u x ^ 2 ∧ u x ^ 2 ≤ U ^ 2 := by
    constructor
    · exact sq_nonneg _
    · have huabs : |u x| ≤ U := by
        simpa [Real.norm_eq_abs] using hU x
      have habs_nonneg : 0 ≤ |u x| := abs_nonneg _
      have hprod : 0 ≤ (U - |u x|) * (U + |u x|) :=
        mul_nonneg (sub_nonneg.mpr huabs) (add_nonneg hU0 habs_nonneg)
      nlinarith [hprod, sq_abs (u x)]
  have hdu_sq_bound (x : ℝ) : 0 ≤ (deriv u x) ^ 2 ∧
      (deriv u x) ^ 2 ≤ D₁ ^ 2 := by
    constructor
    · exact sq_nonneg _
    · have hdabs : |deriv u x| ≤ D₁ := by
        simpa [Real.norm_eq_abs] using hD₁ x
      have habs_nonneg : 0 ≤ |deriv u x| := abs_nonneg _
      have hprod : 0 ≤ (D₁ - |deriv u x|) * (D₁ + |deriv u x|) :=
        mul_nonneg (sub_nonneg.mpr hdabs) (add_nonneg hD₁0 habs_nonneg)
      nlinarith [hprod, sq_abs (deriv u x)]
  have huSqMeas : Measurable (fun x => u x ^ 2) :=
    (hu.continuous.pow 2).measurable
  have huSqInt : Integrable (fun x => u x ^ 2) standardGaussianMehler := by
    apply integrable_of_measurable_norm_le huSqMeas
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hu_sq_bound x).1]
    exact (hu_sq_bound x).2
  obtain ⟨K₀, _hK₀0, hK₀⟩ := exists_mul_log_norm_bound (U ^ 2)
  have hphiMeas : Measurable (fun x => gaussianXLogX (u x ^ 2)) := by
    exact (Real.continuous_mul_log.measurable.comp huSqMeas)
  have hphiBound (x : ℝ) :
      ‖gaussianXLogX (u x ^ 2)‖ ≤ K₀ := by
    exact hK₀ (u x ^ 2) ⟨(hu_sq_bound x).1, (hu_sq_bound x).2⟩
  have hphiInt : Integrable (fun x => gaussianXLogX (u x ^ 2))
      standardGaussianMehler :=
    integrable_of_measurable_norm_le hphiMeas hphiBound
  have hderivMeas : Measurable (deriv u) :=
    hu.continuous_deriv (by norm_num) |>.measurable
  have hderivSqMeas : Measurable (fun x => (deriv u x) ^ 2) :=
    hderivMeas.pow_const 2
  have hderivSqInt : Integrable (fun x => (deriv u x) ^ 2)
      standardGaussianMehler := by
    apply integrable_of_measurable_norm_le hderivSqMeas
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hdu_sq_bound x).1]
    exact (hdu_sq_bound x).2
  refine ⟨huSqInt, ?_, hderivSqInt⟩
  simpa [gaussianXLogX] using hphiInt

/-- The exact standard Gaussian scalar log-Sobolev inequality for bounded C²
functions. The positive approximation is handled by the accepted bounded-
positive theorem, with no lower-bound or nonzero-mean condition on `u`.-/
theorem standardGaussian_boundedSmooth_square_logSobolev
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {U D₁ D₂ : ℝ}
    (hU : ∀ x, ‖u x‖ ≤ U)
    (hD₁ : ∀ x, ‖deriv u x‖ ≤ D₁)
    (hD₂ : ∀ x, ‖deriv (deriv u) x‖ ≤ D₂) :
    Integrable (fun x => u x ^ 2) standardGaussianMehler ∧
      Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) standardGaussianMehler ∧
      Integrable (fun x => (deriv u x) ^ 2) standardGaussianMehler ∧
      looconcentrationEntropy standardGaussianMehler (fun x => u x ^ 2) ≤
        2 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler) := by
  have hU0 : 0 ≤ U := le_trans (norm_nonneg (u 0)) (hU 0)
  have hD₁0 : 0 ≤ D₁ := le_trans (norm_nonneg (deriv u 0)) (hD₁ 0)
  have hD₂0 : 0 ≤ D₂ := le_trans (norm_nonneg (deriv (deriv u) 0)) (hD₂ 0)
  obtain ⟨huSqInt, hphiInt, hderivSqInt⟩ :=
    standardGaussian_boundedSmooth_square_integrable hu hU hD₁ hD₂
  let B : ℝ := U ^ 2 + 1
  obtain ⟨K, _hK0, hK⟩ := exists_mul_log_norm_bound B
  let φ : ℝ → ℝ := gaussianXLogX
  let m : ℝ := ∫ x, u x ^ 2 ∂standardGaussianMehler
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hε_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
    have hn : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 n
    exact (div_le_one₀ (by linarith : 0 < (n : ℝ) + 1)).2 (by norm_num)
  have hsource (n : ℕ) (x : ℝ) :
      1 / ((n : ℝ) + 1) ≤ squareEpsilon n u x ∧
        squareEpsilon n u x ≤ B := by
    constructor
    · dsimp [squareEpsilon]
      nlinarith [sq_nonneg (u x)]
    · have hsq := (show u x ^ 2 ≤ U ^ 2 from by
        have huabs : |u x| ≤ U := by
          simpa [Real.norm_eq_abs] using hU x
        have habs_nonneg : 0 ≤ |u x| := abs_nonneg _
        have hprod := mul_nonneg (sub_nonneg.mpr huabs)
          (add_nonneg hU0 habs_nonneg)
        nlinarith [hprod, sq_abs (u x)])
      dsimp [squareEpsilon, B]
      linarith [hε_le_one n]
  have hderivBound (n : ℕ) (x : ℝ) :
      ‖deriv (squareEpsilon n u) x‖ ≤ 2 * U * D₁ := by
    rw [squareEpsilon_derivative hu]
    calc
      ‖2 * u x * deriv u x‖ = 2 * ‖u x‖ * ‖deriv u x‖ := by
        simp [norm_mul]
      _ ≤ 2 * U * D₁ := by
        calc
          2 * ‖u x‖ * ‖deriv u x‖ ≤ 2 * U * ‖deriv u x‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hU x) (by norm_num)) (norm_nonneg _)
          _ ≤ 2 * U * D₁ :=
            mul_le_mul_of_nonneg_left (hD₁ x) (by positivity)
  have hsecondBound (n : ℕ) (x : ℝ) :
      ‖deriv (deriv (squareEpsilon n u)) x‖ ≤
        2 * D₁ ^ 2 + 2 * U * D₂ := by
    rw [squareEpsilon_second_derivative hu]
    calc
      ‖2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x‖ ≤
          ‖2 * (deriv u x) ^ 2‖ + ‖2 * u x * deriv (deriv u) x‖ := norm_add_le _ _
      _ = 2 * ‖deriv u x‖ ^ 2 +
          2 * ‖u x‖ * ‖deriv (deriv u) x‖ := by
        simp [norm_mul]
      _ ≤ 2 * D₁ ^ 2 + 2 * U * D₂ := by
        have hD₁sq : ‖deriv u x‖ ^ 2 ≤ D₁ ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hD₁0).2 (hD₁ x)
        have hUD₂ : ‖u x‖ * ‖deriv (deriv u) x‖ ≤ U * D₂ := by
          calc
            ‖u x‖ * ‖deriv (deriv u) x‖ ≤ U * ‖deriv (deriv u) x‖ :=
              mul_le_mul_of_nonneg_right (hU x) (norm_nonneg _)
            _ ≤ U * D₂ := mul_le_mul_of_nonneg_left (hD₂ x) hU0
        exact add_le_add
          (mul_le_mul_of_nonneg_left hD₁sq (by norm_num))
          (by
            calc
              2 * ‖u x‖ * ‖deriv (deriv u) x‖ =
                  2 * (‖u x‖ * ‖deriv (deriv u) x‖) := by ring
              _ ≤ 2 * (U * D₂) :=
                mul_le_mul_of_nonneg_left hUD₂ (by norm_num)
              _ = 2 * U * D₂ := by ring)
  have hregular (n : ℕ) : ContDiff ℝ 2 (squareEpsilon n u) := by
    change ContDiff ℝ 2 (fun x => u x ^ 2 + 1 / ((n : ℝ) + 1))
    exact (hu.pow 2).add contDiff_const
  have hpositiveLSI (n : ℕ) :=
    standardGaussian_boundedPositive_scalar_logSobolev
      (hregular n) (hε n) (hsource n)
      (hderivBound n) (hsecondBound n)
  have hratioBound (n : ℕ) (x : ℝ) :
      (deriv (squareEpsilon n u) x) ^ 2 / squareEpsilon n u x ≤
        4 * (deriv u x) ^ 2 := by
    rw [squareEpsilon_derivative hu]
    have hden : 0 < u x ^ 2 + 1 / ((n : ℝ) + 1) := by positivity
    apply (div_le_iff₀ hden).2
    have hnonneg := mul_nonneg (sq_nonneg (deriv u x)) (le_of_lt (hε n))
    nlinarith [sq_nonneg (u x)]
  have hratioIntegral (n : ℕ) :
      (∫ x, (deriv (squareEpsilon n u) x) ^ 2 /
          squareEpsilon n u x ∂standardGaussianMehler) ≤
        4 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler) := by
    have hleftInt := (hpositiveLSI n).1
    have hrightInt := hderivSqInt.const_mul 4
    calc
      _ ≤ ∫ x, 4 * (deriv u x) ^ 2 ∂standardGaussianMehler :=
        integral_mono hleftInt hrightInt (hratioBound n)
      _ = 4 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler) := by
        rw [integral_const_mul]

  let F : ℕ → ℝ → ℝ := fun n x => φ (squareEpsilon n u x)
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) standardGaussianMehler := by
    exact ((Real.continuous_mul_log.measurable.comp
      ((hregular n).continuous.measurable)).aestronglyMeasurable)
  have hFbound : ∀ n, ∀ x, ‖F n x‖ ≤ K := by
    intro n x
    have hrange : squareEpsilon n u x ∈ Set.Icc (0 : ℝ) B := by
      constructor
      · exact le_trans (le_of_lt (hε n)) (hsource n x).1
      · exact (hsource n x).2
    exact hK _ hrange
  have hFpoint (x : ℝ) :
      Tendsto (fun n : ℕ => F n x) atTop (𝓝 (φ (u x ^ 2))) := by
    have harg : Tendsto (fun n : ℕ => squareEpsilon n u x)
        atTop (𝓝 (u x ^ 2)) := by
      simpa [squareEpsilon] using
        (tendsto_const_nhds (x := u x ^ 2)).add squareEpsilon_parameter_tendsto_zero
    exact Real.continuous_mul_log.continuousAt.tendsto.comp harg
  have hphiLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMehler) (F := F)
    (f := fun x => φ (u x ^ 2)) (bound := fun _ => K)
    (by filter_upwards [] with n; exact hFmeas n)
    (by filter_upwards [] with n; exact ae_of_all _ (hFbound n))
    (integrable_const K)
    (by filter_upwards [] with x; exact hFpoint x)

  have hmeanApprox (n : ℕ) :
      (∫ x, squareEpsilon n u x ∂standardGaussianMehler) =
        m + 1 / ((n : ℝ) + 1) := by
    simp [squareEpsilon, m, integral_add huSqInt (integrable_const _)]
  have hmeanLogLimit : Tendsto
      (fun n : ℕ => φ (m + 1 / ((n : ℝ) + 1))) atTop (𝓝 (φ m)) := by
    apply Real.continuous_mul_log.continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds (x := m)).add
      squareEpsilon_parameter_tendsto_zero
  have hentropyApprox (n : ℕ) :
      looconcentrationEntropy standardGaussianMehler (squareEpsilon n u) =
        (∫ x, F n x ∂standardGaussianMehler) -
          φ (m + 1 / ((n : ℝ) + 1)) := by
    rw [looconcentrationEntropy, hmeanApprox n]
    rfl
  have hentropyLimit :
      looconcentrationEntropy standardGaussianMehler (fun x => u x ^ 2) =
        (∫ x, φ (u x ^ 2) ∂standardGaussianMehler) - φ m := by
    rw [looconcentrationEntropy]
    rfl
  have hentropySequence : Tendsto
      (fun n : ℕ => looconcentrationEntropy standardGaussianMehler (squareEpsilon n u))
      atTop (𝓝 (looconcentrationEntropy standardGaussianMehler (fun x => u x ^ 2))) := by
    have hsub := hphiLimit.sub hmeanLogLimit
    simpa only [hentropyApprox, hentropyLimit] using hsub
  have hboundEntropy (n : ℕ) :
      looconcentrationEntropy standardGaussianMehler (squareEpsilon n u) ≤
        2 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler) := by
    calc
      looconcentrationEntropy standardGaussianMehler (squareEpsilon n u) ≤
          (1 / 2 : ℝ) *
            (∫ x, (deriv (squareEpsilon n u) x) ^ 2 /
              squareEpsilon n u x ∂standardGaussianMehler) :=
        (hpositiveLSI n).2
      _ ≤ (1 / 2 : ℝ) *
            (4 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler)) :=
        mul_le_mul_of_nonneg_left (hratioIntegral n) (by norm_num)
      _ = 2 * (∫ x, (deriv u x) ^ 2 ∂standardGaussianMehler) := by ring
  have hfinal := le_of_tendsto' hentropySequence hboundEntropy
  exact ⟨huSqInt, hphiInt, hderivSqInt, hfinal⟩

#print axioms standardGaussian_boundedSmooth_square_integrable
#print axioms standardGaussian_boundedSmooth_square_logSobolev

end LOOConcentration
