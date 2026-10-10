import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exponential tilts and the entropy formula

For a bounded measurable real function on a probability space, this file proves
the parameter derivative and entropy identities used in the concentration
arguments. `looconcentrationEntropy` uses the same normalization as `HasLogSobolev`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

noncomputable section

local instance (priority := 10000) : AddCommGroup ℝ :=
  Real.normedAddCommGroup.toAddCommGroup
local instance (priority := 10000) : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Entropy with the normalization appearing in the frozen log-Sobolev API. -/
noncomputable def looconcentrationEntropy (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  (∫ ω, g ω * Real.log (g ω) ∂μ) -
    (∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)

/-- The exponential partition function of a bounded real observable. -/
noncomputable def logPartition (μ : Measure Ω) (F : Ω → ℝ) : ℝ → ℝ :=
  fun t => ∫ ω, Real.exp (t * F ω) ∂μ

/-- The log-partition function of a bounded real observable. -/
noncomputable def logPartitionLog (μ : Measure Ω) (F : Ω → ℝ) : ℝ → ℝ :=
  Real.log ∘ logPartition μ F

private theorem integrable_of_measurable_norm_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {K : ℝ}
    (hf : Measurable f) (_hK : 0 ≤ K) (hbound : ∀ ω, ‖f ω‖ ≤ K) :
    Integrable f μ := by
  refine Integrable.mono' (integrable_const K) hf.aestronglyMeasurable ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg _hK] using hbound ω

omit [MeasurableSpace Ω] in
private theorem abs_mul_observable_le {F : Ω → ℝ} {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) (ω : Ω) :
    |t * F ω| ≤ |t| * B := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg t)

omit [MeasurableSpace Ω] in
private theorem exp_mul_observable_le {F : Ω → ℝ} {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) (ω : Ω) :
    Real.exp (t * F ω) ≤ Real.exp (|t| * B) := by
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_mul_observable_le hF ω))

omit [MeasurableSpace Ω] in
private theorem exp_neg_abs_mul_observable_le {F : Ω → ℝ} {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) (ω : Ω) :
    Real.exp (-(|t| * B)) ≤ Real.exp (t * F ω) := by
  apply Real.exp_le_exp.mpr
  calc
    -( |t| * B) ≤ -|t * F ω| := neg_le_neg (abs_mul_observable_le hF ω)
    _ ≤ t * F ω := neg_abs_le _

private theorem integrable_exp_mul_observable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => Real.exp (t * F ω)) μ := by
  apply integrable_of_measurable_norm_le
    (Real.measurable_exp.comp (measurable_const.mul hFmeas)) (Real.exp_pos _).le
  intro ω
  change |Real.exp (t * F ω)| ≤ Real.exp (|t| * B)
  simpa only [abs_of_pos (Real.exp_pos _)] using exp_mul_observable_le hF ω

private theorem integrable_observable_mul_exp {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => F ω * Real.exp (t * F ω)) μ := by
  apply integrable_of_measurable_norm_le
    (hFmeas.mul (Real.measurable_exp.comp (measurable_const.mul hFmeas)))
    (mul_nonneg hB (Real.exp_nonneg _))
  intro ω
  change |F ω * Real.exp (t * F ω)| ≤ B * Real.exp (|t| * B)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right (hF ω) (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_mul_observable_le hF ω))) hB)

theorem logPartition_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => Real.exp (t * F ω)) μ :=
  integrable_exp_mul_observable hFmeas hF

theorem logPartition_derivative_integrable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (hFmeas : Measurable F) {B t : ℝ} (hB : 0 ≤ B)
    (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => F ω * Real.exp (t * F ω)) μ :=
  integrable_observable_mul_exp hFmeas hB hF (t := t)

theorem logPartition_pos {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) :
    0 < logPartition μ F t := by
  rw [logPartition]
  have h_exp := integrable_exp_mul_observable (μ := μ) (t := t) hFmeas hF
  have h_lower : (∫ _ω, Real.exp (-(|t| * B)) ∂μ) ≤
      ∫ ω, Real.exp (t * F ω) ∂μ :=
    integral_mono (integrable_const (Real.exp (-(|t| * B)))) h_exp
      (fun ω => exp_neg_abs_mul_observable_le hF ω)
  rw [integral_const, probReal_univ, one_smul] at h_lower
  exact (Real.exp_pos _).trans_le h_lower

theorem logPartition_hasDerivAt {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    HasDerivAt (logPartition μ F)
      (∫ ω, F ω * Real.exp (t * F ω) ∂μ) t := by
  let s : Set ℝ := Metric.ball t 1
  let K : ℝ := B * Real.exp ((|t| + 1) * B)
  have hK : 0 ≤ K := mul_nonneg hB (Real.exp_nonneg _)
  have hdiff : ∀ ω, ∀ y ∈ s,
      HasDerivAt (Real.exp ∘ fun x : ℝ => id x * F ω)
        (F ω * Real.exp (y * F ω)) y := by
    intro ω y _
    exact ((Real.hasDerivAt_exp (y * F ω)).comp y
      ((hasDerivAt_id y).mul_const (F ω))).congr_deriv (by ring)
  have hbound : ∀ᵐ ω ∂μ, ∀ t ∈ s,
      ‖F ω * Real.exp (t * F ω)‖ ≤ K := by
    apply ae_of_all
    intro ω y hy
    have hdist : |y - t| < 1 := by
      simpa [s, Metric.mem_ball, Real.dist_eq] using hy
    have hy_bound : |y| ≤ |t| + 1 := by
      calc
        |y| = |(y - t) + t| := by congr 1; ring
        _ ≤ |y - t| + |t| := abs_add_le _ _
        _ ≤ 1 + |t| := add_le_add hdist.le le_rfl
        _ = |t| + 1 := by ring
    have harg : y * F ω ≤ (|t| + 1) * B := by
      calc
        y * F ω ≤ |y * F ω| := le_abs_self _
        _ = |y| * |F ω| := abs_mul _ _
        _ ≤ (|t| + 1) * B := by
          calc
            |y| * |F ω| ≤ (|t| + 1) * |F ω| :=
              mul_le_mul_of_nonneg_right hy_bound (abs_nonneg _)
            _ ≤ (|t| + 1) * B :=
              mul_le_mul_of_nonneg_left (hF ω) (by positivity)
    change |F ω * Real.exp (y * F ω)| ≤ K
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |F ω| * Real.exp (y * F ω) ≤ B * Real.exp (y * F ω) :=
        mul_le_mul_of_nonneg_right (hF ω) (Real.exp_nonneg _)
      _ ≤ B * Real.exp ((|t| + 1) * B) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hB
      _ = K := rfl
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (F := fun t ω => Real.exp (t * F ω))
    (F' := fun t ω => F ω * Real.exp (t * F ω)) (bound := fun _ => K)
    (Metric.ball_mem_nhds _ zero_lt_one)
    (Filter.Eventually.of_forall fun t =>
      (Real.measurable_exp.comp (measurable_const.mul hFmeas)).aestronglyMeasurable)
    (integrable_exp_mul_observable (μ := μ) (t := t) hFmeas hF)
    ((hFmeas.mul (Real.measurable_exp.comp (measurable_const.mul hFmeas))).aestronglyMeasurable)
    hbound (integrable_const K)
    (Filter.Eventually.of_forall fun ω => hdiff ω)
  convert hderiv.2 using 1 <;> rfl

theorem logPartitionLog_hasDerivAt {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    HasDerivAt (logPartitionLog μ F)
      ((∫ ω, F ω * Real.exp (t * F ω) ∂μ) / logPartition μ F t) t := by
  have hZ : 0 < logPartition μ F t := logPartition_pos hFmeas hF
  exact ((Real.hasDerivAt_log hZ.ne').comp t
    (logPartition_hasDerivAt hFmeas hB hF)).congr_deriv (by
      rw [div_eq_mul_inv]
      ring)

theorem logPartition_deriv {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    deriv (logPartition μ F) t =
      ∫ ω, F ω * Real.exp (t * F ω) ∂μ :=
  (logPartition_hasDerivAt hFmeas hB hF).deriv

theorem logPartitionLog_deriv {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    deriv (logPartitionLog μ F) t =
      (∫ ω, F ω * Real.exp (t * F ω) ∂μ) / logPartition μ F t :=
  (logPartitionLog_hasDerivAt hFmeas hB hF).deriv

theorem looconcentrationEntropy_exp_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => Real.exp (t * F ω) *
      Real.log (Real.exp (t * F ω))) μ := by
  have hprod := integrable_observable_mul_exp (μ := μ) hFmeas hB hF (t := t)
  have hmul : Integrable (fun ω => t * (F ω * Real.exp (t * F ω))) μ :=
    hprod.const_mul t
  refine hmul.congr ?_
  filter_upwards with ω
  simp only [Real.log_exp]
  ring

theorem looconcentrationEntropy_exp_eq_logPartition_deriv {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (hFmeas : Measurable F) {B t : ℝ} (hB : 0 ≤ B)
    (hF : ∀ ω, |F ω| ≤ B) :
    looconcentrationEntropy μ (fun ω => Real.exp (t * F ω)) /
      logPartition μ F t =
        t * deriv (logPartitionLog μ F) t - logPartitionLog μ F t := by
  have hZ : logPartition μ F t =
      ∫ ω, Real.exp (t * F ω) ∂μ := rfl
  have hderiv := logPartitionLog_deriv (μ := μ) (F := F) (t := t) hFmeas hB hF
  have hZpos := logPartition_pos (μ := μ) (F := F) (t := t) hFmeas hF
  have h_int :
      (∫ ω, Real.exp (t * F ω) * Real.log (Real.exp (t * F ω)) ∂μ) =
        t * ∫ ω, F ω * Real.exp (t * F ω) ∂μ := by
    calc
      (∫ ω, Real.exp (t * F ω) * Real.log (Real.exp (t * F ω)) ∂μ) =
          ∫ ω, t * (F ω * Real.exp (t * F ω)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [Real.log_exp]
        ring
      _ = t * ∫ ω, F ω * Real.exp (t * F ω) ∂μ := integral_const_mul t _
  rw [looconcentrationEntropy, h_int, ← hZ]
  change (t * (∫ ω, F ω * Real.exp (t * F ω) ∂μ) -
      logPartition μ F t * Real.log (logPartition μ F t)) / logPartition μ F t =
    t * deriv (logPartitionLog μ F) t - Real.log (logPartition μ F t)
  rw [hderiv]
  field_simp [ne_of_gt hZpos]

end

end LOOConcentration
