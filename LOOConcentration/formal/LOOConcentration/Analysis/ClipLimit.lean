import LOOConcentration.Analysis.ClipMollify
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Truncation limits and centered Fatou transfer

The clipping sequence uses the actual caps `j + 1`. Dominated convergence
proves its mean and `L¹` limits from integrability. The Fatou helpers take the
measurability, integrability, pointwise limit, mean limit, and uniform
approximant-moment bound as explicit inputs; they do not assume integrability
of the limiting exponential or power.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology ENNReal

namespace LOOConcentration

theorem clipValue_eq_self_of_abs_lt {A u : ℝ} (h : |u| < A) :
    clipValue A u = u := by
  have hu := abs_lt.mp h
  unfold clipValue
  rw [min_eq_left hu.2.le, max_eq_right hu.1.le]

theorem tendsto_clipValue_atTop (u : ℝ) :
    Tendsto (fun A : ℝ => clipValue A u) atTop (𝓝 u) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop |u|] with A hA
  exact (clipValue_eq_self_of_abs_lt hA).symm

theorem tendsto_clipValue_sequence (u : ℝ) :
    Tendsto (fun j : ℕ => clipValue ((j : ℝ) + 1) u) atTop (𝓝 u) := by
  have hcap : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_clipValue_atTop u).comp hcap

theorem continuous_clipValue (A : ℝ) :
    Continuous (fun u : ℝ => clipValue A u) := by
  unfold clipValue
  exact continuous_const.max (continuous_id.min continuous_const)

theorem abs_clipValue_le_abs {A u : ℝ} (hA : 0 ≤ A) :
    |clipValue A u| ≤ |u| := by
  have hzero : clipValue A 0 = 0 := by
    simp [clipValue, hA]
  simpa [hzero] using abs_clipValue_sub_le A u 0

/-- The clipped sequence at the source levels `A_j = j + 1`. -/
def clipValueSequence {α : Type*} (F : α → ℝ) (j : ℕ) : α → ℝ :=
  fun x => clipValue ((j : ℝ) + 1) (F x)

theorem clipValueSequence_tendsto {α : Type*} (F : α → ℝ) (x : α) :
    Tendsto (fun j : ℕ => clipValueSequence F j x) atTop (𝓝 (F x)) := by
  exact tendsto_clipValue_sequence (F x)

theorem clipValueSequence_integral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {F : α → ℝ}
    (hF : Integrable F μ) :
    Tendsto (fun j : ℕ => ∫ x, clipValueSequence F j x ∂μ)
      atTop (𝓝 (∫ x, F x ∂μ)) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖F x‖)
  · exact Filter.Eventually.of_forall fun j => by
      change AEStronglyMeasurable
        (fun x => clipValue ((j : ℝ) + 1) (F x)) μ
      exact (continuous_clipValue ((j : ℝ) + 1)).comp_aestronglyMeasurable hF.1
  · exact Filter.Eventually.of_forall fun j => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_clipValue_le_abs (by positivity)
  · exact hF.norm
  · filter_upwards [] with x
    exact clipValueSequence_tendsto F x

theorem clipValueSequence_L1_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {F : α → ℝ}
    (hF : Integrable F μ) :
    Tendsto (fun j : ℕ => ∫ x, |clipValueSequence F j x - F x| ∂μ)
      atTop (𝓝 0) := by
  have hbound : Integrable (fun x => 2 * |F x|) μ := by
    simpa [Real.norm_eq_abs] using hF.norm.const_mul (2 : ℝ)
  have hlim : Tendsto
      (fun j : ℕ => ∫ x, |clipValueSequence F j x - F x| ∂μ) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : α => (0 : ℝ)) (bound := fun x => 2 * |F x|)
    · exact Filter.Eventually.of_forall fun j => by
        change AEStronglyMeasurable
          (fun x => |clipValue ((j : ℝ) + 1) (F x) - F x|) μ
        have hclip : AEStronglyMeasurable
            (fun x => clipValue ((j : ℝ) + 1) (F x)) μ :=
          (continuous_clipValue ((j : ℝ) + 1)).comp_aestronglyMeasurable hF.1
        exact continuous_abs.comp_aestronglyMeasurable (hclip.sub hF.1)
    · exact Filter.Eventually.of_forall fun j => Filter.Eventually.of_forall fun x => by
        have hcap : 0 ≤ (j : ℝ) + 1 := by positivity
        calc
          ‖|clipValueSequence F j x - F x|‖ =
              |clipValueSequence F j x - F x| := by
                rw [Real.norm_eq_abs, abs_abs]
          _ = |clipValueSequence F j x + -F x| := by rw [sub_eq_add_neg]
          _ ≤ |clipValueSequence F j x| + |F x| := by
            simpa only [abs_neg] using abs_add_le (clipValueSequence F j x) (-F x)
          _ ≤ |F x| + |F x| := by
            exact add_le_add (abs_clipValue_le_abs hcap) le_rfl
          _ = 2 * |F x| := by ring
    · exact hbound
    · filter_upwards [] with x
      have hclip := clipValueSequence_tendsto F x
      have hsub : Tendsto (fun j : ℕ => clipValueSequence F j x - F x)
          atTop (𝓝 0) := by
        simpa using hclip.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => F x)
          atTop (𝓝 (F x)))
      have hAbs := continuous_abs.continuousAt.tendsto.comp hsub
      have hAbs' : Tendsto
          (abs ∘ fun j : ℕ => clipValueSequence F j x - F x) atTop (𝓝 0) := by
        simpa only [abs_zero] using hAbs
      exact Filter.Tendsto.congr'
        (f₁ := abs ∘ fun j : ℕ => clipValueSequence F j x - F x)
        (f₂ := fun j : ℕ => |clipValueSequence F j x - F x|)
        (Filter.Eventually.of_forall fun _ => rfl) hAbs'
  simpa using hlim

/-- Convergence of the actual integrals used as centers in the Fatou lemmas. -/
def IntegralMeansConverge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ) (F : α → ℝ) : Prop :=
  Tendsto (fun j => ∫ x, f j x ∂μ) atTop (𝓝 (∫ x, F x ∂μ))

theorem centeredTransform_fatou {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (_hF : Integrable F μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (hmeans : IntegralMeansConverge μ f F)
    (phi : ℝ → ℝ≥0∞) (hphi : Continuous phi) :
    ∫⁻ x, phi (F x - ∫ y, F y ∂μ) ∂μ ≤
      atTop.liminf (fun j => ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := by
  have hfatou :
      ∫⁻ x, atTop.liminf
        (fun j => phi (f j x - ∫ y, f j y ∂μ)) ∂μ ≤
        atTop.liminf (fun j => ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := by
    apply MeasureTheory.lintegral_liminf_le'
    · intro j
      exact (hphi.comp_aestronglyMeasurable
        ((hf j).1.sub aestronglyMeasurable_const)).aemeasurable
  calc
    ∫⁻ x, phi (F x - ∫ y, F y ∂μ) ∂μ =
        ∫⁻ x, atTop.liminf
          (fun j => phi (f j x - ∫ y, f j y ∂μ)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with x hx
      have hcenter : Tendsto (fun j => f j x - ∫ y, f j y ∂μ) atTop
          (𝓝 (F x - ∫ y, F y ∂μ)) := by
        dsimp [IntegralMeansConverge] at hmeans
        exact hx.sub hmeans
      exact (hphi.continuousAt.tendsto.comp hcenter).liminf_eq.symm
    _ ≤ atTop.liminf
        (fun j => ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := hfatou

theorem centeredExp_fatou {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (hmeans : IntegralMeansConverge μ f F)
    (lam : ℝ) (B : ℝ≥0∞)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (f j x - ∫ y, f j y ∂μ))) ∂μ ≤ B) :
    ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (F x - ∫ y, F y ∂μ))) ∂μ ≤ B := by
  let phi : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (lam * t))
  have hphi : Continuous phi := by
    dsimp [phi]
    exact ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hfatou := centeredTransform_fatou hf hF hpoint hmeans phi hphi
  calc
    ∫⁻ x, phi (F x - ∫ y, F y ∂μ) ∂μ ≤
        atTop.liminf (fun j => ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := hfatou
    _ ≤ B := Filter.liminf_le_of_frequently_le
      ((Filter.Eventually.of_forall hbound).frequently)

theorem centeredPow_fatou {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (hmeans : IntegralMeansConverge μ f F)
    {p : ℝ} (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal
      (|f j x - ∫ y, f j y ∂μ| ^ p) ∂μ ≤ B) :
    ∫⁻ x, ENNReal.ofReal
      (|F x - ∫ y, F y ∂μ| ^ p) ∂μ ≤ B := by
  let phi : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (|t| ^ p)
  have hp₀ : 0 ≤ p := le_trans (by norm_num) hp
  have hphi : Continuous phi := by
    dsimp [phi]
    exact ENNReal.continuous_ofReal.comp
      ((Real.continuous_rpow_const hp₀).comp continuous_abs)
  have hfatou := centeredTransform_fatou hf hF hpoint hmeans phi hphi
  calc
    ∫⁻ x, phi (F x - ∫ y, F y ∂μ) ∂μ ≤
        atTop.liminf (fun j => ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := hfatou
    _ ≤ B := Filter.liminf_le_of_frequently_le
      ((Filter.Eventually.of_forall hbound).frequently)

end LOOConcentration
