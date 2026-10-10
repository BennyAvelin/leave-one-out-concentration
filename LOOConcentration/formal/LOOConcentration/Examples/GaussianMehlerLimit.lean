import LOOConcentration.Examples.GaussianMehler
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology NNReal

private theorem coe_nnreal_tendsto_atTop :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop := by
  exact NNReal.tendsto_coe_atTop.mpr tendsto_id

private theorem mehler_drift_tendsto_zero :
    Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp coe_nnreal_tendsto_atTop)

private theorem mehler_noise_tendsto_one :
    Tendsto (fun t : ℝ≥0 => Real.sqrt (1 - Real.exp (-2 * (t : ℝ))))
      atTop (𝓝 1) := by
  have h2t : Tendsto (fun t : ℝ≥0 => (2 : ℝ) * (t : ℝ)) atTop atTop := by
    exact coe_nnreal_tendsto_atTop.const_mul_atTop (by norm_num)
  have hneg2t : Tendsto (fun t : ℝ≥0 => -2 * (t : ℝ)) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp h2t
    convert h using 1
    ext t
    simp only [Function.comp_apply]
    ring
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-2 * (t : ℝ)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg2t
  have hinside : Tendsto (fun t : ℝ≥0 => 1 - Real.exp (-2 * (t : ℝ)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  convert Real.continuous_sqrt.continuousAt.tendsto.comp hinside using 1
  · ext t
    rfl
  · simp

private theorem mehler_argument_tendsto_noise {x y : ℝ} :
    Tendsto
      (fun t : ℝ≥0 => standardGaussianMehlerArgument (t : ℝ) x y)
      atTop (𝓝 y) := by
  have hdrift := mehler_drift_tendsto_zero.mul_const x
  have hnoise := mehler_noise_tendsto_one.mul_const y
  have hsum := hdrift.add hnoise
  simpa [standardGaussianMehlerArgument, standardGaussianMehlerDrift,
    standardGaussianMehlerNoise] using hsum

/-- For a bounded continuous source, the actual scalar Mehler average converges
pointwise to its Gaussian mean. Dominated convergence uses the source's own
uniform bound and the literal drift and noise coefficients. -/
theorem tendsto_standardGaussianMehlerAverage_atTop
    {f : ℝ → ℝ} (hf : Continuous f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Tendsto
      (fun t : ℝ≥0 =>
        standardGaussianMehlerAverage f hf.measurable hbounded
          (t : ℝ) t.property x)
      atTop (𝓝 (∫ y, f y ∂standardGaussianMehler)) := by
  rcases hbounded with ⟨M, hM⟩
  let F : ℝ≥0 → ℝ → ℝ := fun t y =>
    f (standardGaussianMehlerArgument (t : ℝ) x y)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) standardGaussianMehler := by
    intro t
    exact (hf.measurable.comp (by
      unfold standardGaussianMehlerArgument standardGaussianMehlerDrift
        standardGaussianMehlerNoise
      fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ t in atTop, ∀ᵐ y ∂standardGaussianMehler,
      ‖F t y‖ ≤ M := by
    filter_upwards [] with t
    exact ae_of_all _ fun y => hM _
  have hpoint : ∀ᵐ y ∂standardGaussianMehler,
      Tendsto (fun t : ℝ≥0 => F t y) atTop (𝓝 (f y)) := by
    filter_upwards [] with y
    exact hf.continuousAt.tendsto.comp mehler_argument_tendsto_noise
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMehler) (F := F) (f := f) (bound := fun _ => M)
    (by
      filter_upwards [] with t
      exact (hmeas t))
    hbound
    (integrable_const M)
    hpoint
  simpa [F, standardGaussianMehlerAverage] using hlim

private noncomputable def gaussianMehlerXLogX (z : ℝ) : ℝ :=
  z * Real.log z

private theorem gaussianMehlerXLogX_continuousOn
    {ε B : ℝ} (hε : 0 < ε) :
    ContinuousOn gaussianMehlerXLogX (Set.Icc ε B) := by
  unfold gaussianMehlerXLogX
  apply ContinuousOn.mul continuousOn_id
  apply Real.continuousOn_log.mono
  intro z hz
  exact ne_of_gt (lt_of_lt_of_le hε hz.1)

/-- The actual entropy of the bounded positive scalar Mehler average tends to
zero. Stationarity fixes its mean, and outer dominated convergence applies on
the preserved compact interval `[ε,B]`. -/
theorem tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_atTop
    {f : ℝ → ℝ} (hf : Continuous f) {ε B : ℝ}
    (hε : 0 < ε) (hlower : ∀ y, ε ≤ f y) (hupper : ∀ y, f y ≤ B) :
    Tendsto
      (fun t : ℝ≥0 =>
        looconcentrationEntropy standardGaussianMehler
          (standardGaussianMehlerAverage f hf.measurable
            ⟨B, by
              intro y
              have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
              rw [Real.norm_eq_abs, abs_of_nonneg hpos]
              exact hupper y⟩
            (t : ℝ) t.property))
      atTop (𝓝 0) := by
  have hεB : ε ≤ B := (hlower 0).trans (hupper 0)
  have hnorm : ∀ y, ‖f y‖ ≤ B := by
    intro y
    have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact hupper y
  let hb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := ⟨B, hnorm⟩
  let P : ℝ≥0 → ℝ → ℝ := fun t x =>
    standardGaussianMehlerAverage f hf.measurable hb (t : ℝ) t.property x
  let φ : ℝ → ℝ := gaussianMehlerXLogX
  let m : ℝ := ∫ y, f y ∂standardGaussianMehler
  have hfInt : Integrable f standardGaussianMehler := by
    refine (integrable_const B).mono' hf.measurable.aestronglyMeasurable ?_
    exact ae_of_all _ hnorm
  have hmLower : ε ≤ m := by
    calc
      ε = ∫ _ : ℝ, ε ∂standardGaussianMehler := by simp
      _ ≤ ∫ y, f y ∂standardGaussianMehler :=
        integral_mono (integrable_const ε) hfInt hlower
  have hmUpper : m ≤ B := by
    calc
      (∫ y, f y ∂standardGaussianMehler) ≤
          ∫ _ : ℝ, B ∂standardGaussianMehler :=
        integral_mono hfInt (integrable_const B) hupper
      _ = B := by simp
  have hmpos : 0 < m := lt_of_lt_of_le hε hmLower
  have hφat : ContinuousAt φ m := by
    have hlog : ContinuousAt Real.log m :=
      Real.continuousAt_log (ne_of_gt hmpos)
    change ContinuousAt (fun z : ℝ => z * Real.log z) m
    exact continuousAt_id.mul hlog
  have hφcont : ContinuousOn φ (Set.Icc ε B) := by
    simpa [φ] using gaussianMehlerXLogX_continuousOn hε
  have hφnormcont : ContinuousOn (fun z => ‖φ z‖) (Set.Icc ε B) :=
    hφcont.norm
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hφnormcont
  have hφbound : ∀ z ∈ Set.Icc ε B, ‖φ z‖ ≤ K := by
    intro z hz
    exact hK (Set.mem_image_of_mem _ hz)
  have hPmeas : ∀ t, Measurable (P t) := by
    intro t
    exact measurable_standardGaussianMehlerAverage hf.measurable hb
      (t : ℝ) t.property
  have hPbounds : ∀ t x, ε ≤ P t x ∧ P t x ≤ B := by
    intro t x
    constructor
    · exact standardGaussianMehlerAverage_lower_bound hf.measurable hnorm
        hlower (t : ℝ) t.property x
    · exact (standardGaussianMehlerAverage_bounds hf.measurable hnorm
        (t : ℝ) t.property x).2
  have houterMeas : ∀ t, AEStronglyMeasurable (fun x => φ (P t x))
      standardGaussianMehler := by
    intro t
    exact ((hPmeas t).mul (Real.measurable_log.comp (hPmeas t))).aestronglyMeasurable
  have houterBound : ∀ᶠ t in atTop, ∀ᵐ x ∂standardGaussianMehler,
      ‖φ (P t x)‖ ≤ K := by
    filter_upwards [] with t
    exact ae_of_all _ fun x => hφbound (P t x) ⟨(hPbounds t x).1, (hPbounds t x).2⟩
  have hpt : ∀ x, Tendsto (fun t : ℝ≥0 => P t x) atTop (𝓝 m) := by
    intro x
    simpa [P, m, hb] using
      tendsto_standardGaussianMehlerAverage_atTop hf hb x
  have houterPoint : ∀ᵐ x ∂standardGaussianMehler,
      Tendsto (fun t : ℝ≥0 => φ (P t x)) atTop (𝓝 (φ m)) := by
    filter_upwards [] with x
    exact hφat.tendsto.comp (hpt x)
  have houterLim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMehler)
    (F := fun t x => φ (P t x)) (f := fun _ : ℝ => φ m)
    (bound := fun _ => K)
    (by
      filter_upwards [] with t
      exact houterMeas t)
    houterBound
    (integrable_const K)
    houterPoint
  have hstationary (t : ℝ≥0) :
      (∫ x, P t x ∂standardGaussianMehler) = m := by
    simpa [P, m, hb] using
      integral_standardGaussianMehlerAverage_eq hf.measurable hb
        (t : ℝ) t.property
  have hentropyEq (t : ℝ≥0) :
      looconcentrationEntropy standardGaussianMehler (P t) =
        (∫ x, φ (P t x) ∂standardGaussianMehler) - φ m := by
    simp [looconcentrationEntropy, φ, gaussianMehlerXLogX, hstationary t, m]
  have houterLim' : Tendsto
      (fun t : ℝ≥0 => ∫ x, φ (P t x) ∂standardGaussianMehler)
      atTop (𝓝 (φ m)) := by
    simpa using houterLim
  have hresult : Tendsto
      (fun t : ℝ≥0 =>
        (∫ x, φ (P t x) ∂standardGaussianMehler) - φ m)
      atTop (𝓝 0) := by
    simpa [sub_self] using houterLim'.sub_const (φ m)
  have hresultP : Tendsto
      (fun t : ℝ≥0 => looconcentrationEntropy standardGaussianMehler (P t))
      atTop (𝓝 0) := by
    simpa [hentropyEq] using hresult
  simpa [P, hb] using hresultP

#print axioms tendsto_standardGaussianMehlerAverage_atTop
#print axioms tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_atTop

end LOOConcentration
