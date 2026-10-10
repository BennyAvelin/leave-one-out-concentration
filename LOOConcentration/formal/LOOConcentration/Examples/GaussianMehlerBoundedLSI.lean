import LOOConcentration.Examples.GaussianMehler
import LOOConcentration.Examples.GaussianMehlerLimit
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology NNReal

private theorem nnreal_coe_tendsto_zero :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
  exact continuous_subtype_val.continuousAt.tendsto

private theorem mehler_drift_tendsto_one :
    Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ)))
      (𝓝 (0 : ℝ≥0)) (𝓝 1) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    nnreal_coe_tendsto_zero.neg
  convert h using 1
  · ext t
    rfl
  · simp

private theorem mehler_noise_tendsto_zero :
    Tendsto (fun t : ℝ≥0 => Real.sqrt (1 - Real.exp (-2 * (t : ℝ))))
      (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ≥0 => (2 : ℝ) * (t : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
    simpa using nnreal_coe_tendsto_zero.const_mul (2 : ℝ)
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-2 * (t : ℝ)))
      (𝓝 (0 : ℝ≥0)) (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp h2.neg
    convert h using 1
    · ext t
      congr 1
      ring
    · simp
  have hinside : Tendsto (fun t : ℝ≥0 => 1 - Real.exp (-2 * (t : ℝ)))
      (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
    have hOne : Tendsto (fun _ : ℝ≥0 => (1 : ℝ))
        (𝓝 (0 : ℝ≥0)) (𝓝 1) := tendsto_const_nhds
    simpa using hOne.sub hexp
  convert Real.continuous_sqrt.continuousAt.tendsto.comp hinside using 1
  · ext t
    rfl
  · simp

private theorem mehler_argument_tendsto_start {x y : ℝ} :
    Tendsto
      (fun t : ℝ≥0 => standardGaussianMehlerArgument (t : ℝ) x y)
      (𝓝 (0 : ℝ≥0)) (𝓝 x) := by
  have hdrift := mehler_drift_tendsto_one.mul_const x
  have hnoise := mehler_noise_tendsto_zero.mul_const y
  simpa [standardGaussianMehlerArgument, standardGaussianMehlerDrift,
    standardGaussianMehlerNoise] using hdrift.add hnoise

/-- At the nonnegative-time endpoint, the actual bounded Mehler average
converges pointwise to its source. Dominated convergence uses the uniform
bound on that source in the noise coordinate. -/
theorem tendsto_standardGaussianMehlerAverage_nhds_zero
    {f : ℝ → ℝ} (hf : Continuous f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Tendsto
      (fun t : ℝ≥0 =>
        standardGaussianMehlerAverage f hf.measurable hbounded
          (t : ℝ) t.property x)
      (𝓝 (0 : ℝ≥0)) (𝓝 (f x)) := by
  rcases hbounded with ⟨M, hM⟩
  let F : ℝ≥0 → ℝ → ℝ := fun t y =>
    f (standardGaussianMehlerArgument (t : ℝ) x y)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) standardGaussianMehler := by
    intro t
    exact (hf.measurable.comp (by
      unfold standardGaussianMehlerArgument standardGaussianMehlerDrift
        standardGaussianMehlerNoise
      fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ᵐ y ∂standardGaussianMehler,
      ‖F t y‖ ≤ M := by
    filter_upwards [] with t
    exact ae_of_all _ fun y => hM _
  have hpoint : ∀ᵐ y ∂standardGaussianMehler,
      Tendsto (fun t : ℝ≥0 => F t y) (𝓝 (0 : ℝ≥0)) (𝓝 (f x)) := by
    filter_upwards [] with y
    exact hf.continuousAt.tendsto.comp
      (mehler_argument_tendsto_start (x := x) (y := y))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMehler) (F := F) (f := fun _ => f x)
    (bound := fun _ => M)
    (by
      filter_upwards [] with t
      exact hmeas t)
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

/-- The reviewed wave-11 equilibrium limit supplies the real-parameter tail
limit for any trajectory that agrees with the actual Mehler entropy at every
nonnegative time. Only those source times are used. -/
theorem tendsto_standardGaussianMehlerEntropyTrajectory_atTop
    {f : ℝ → ℝ} (hf : Continuous f) {ε B : ℝ}
    (hε : 0 < ε) (hlower : ∀ y, ε ≤ f y) (hupper : ∀ y, f y ≤ B)
    (ψ : ℝ → ℝ)
    (hpath : ∀ t, 0 ≤ t →
      ψ t = looconcentrationEntropy standardGaussianMehler
        (standardGaussianMehlerAverage f hf.measurable
          ⟨B, by
            intro y
            have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
            rw [Real.norm_eq_abs, abs_of_nonneg hpos]
            exact hupper y⟩
          (Real.toNNReal t) (Real.toNNReal t).property)) :
    Tendsto ψ atTop (𝓝 0) := by
  have hnorm : ∀ y, ‖f y‖ ≤ B := by
    intro y
    have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact hupper y
  let hb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := ⟨B, hnorm⟩
  let P : ℝ≥0 → ℝ := fun t =>
    looconcentrationEntropy standardGaussianMehler
      (standardGaussianMehlerAverage f hf.measurable hb (t : ℝ) t.property)
  have hlimit := tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_atTop
    hf hε hlower hupper
  have hlimitP : Tendsto P atTop (𝓝 0) := by
    simpa [P, hb] using hlimit
  have hcomp : Tendsto (fun t : ℝ => P (Real.toNNReal t)) atTop (𝓝 0) :=
    hlimitP.comp Real.tendsto_toNNReal_atTop
  have heventually : (fun t : ℝ => P (Real.toNNReal t)) =ᶠ[atTop] ψ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hpath t ht).symm
  exact Filter.Tendsto.congr' heventually hcomp

/-- The actual Gaussian entropy is continuous at the initial endpoint for a
bounded positive continuous source. Outer dominated convergence uses the
preserved interval bounds and `z log z` on its compact positive interval. -/
theorem tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_nhds_zero
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
      (𝓝 (0 : ℝ≥0)) (𝓝 (looconcentrationEntropy standardGaussianMehler f)) := by
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
  have hφAt (x : ℝ) (hx : 0 < f x) : ContinuousAt φ (f x) := by
    have hlog : ContinuousAt Real.log (f x) := Real.continuousAt_log (ne_of_gt hx)
    change ContinuousAt (fun z : ℝ => z * Real.log z) (f x)
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
  have houterBound : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ᵐ x ∂standardGaussianMehler,
      ‖φ (P t x)‖ ≤ K := by
    filter_upwards [] with t
    exact ae_of_all _ fun x =>
      hφbound (P t x) ⟨(hPbounds t x).1, (hPbounds t x).2⟩
  have hpt : ∀ x, Tendsto (fun t : ℝ≥0 => P t x)
      (𝓝 (0 : ℝ≥0)) (𝓝 (f x)) := by
    intro x
    simpa [P, hb] using
      tendsto_standardGaussianMehlerAverage_nhds_zero hf hb x
  have houterPoint : ∀ᵐ x ∂standardGaussianMehler,
      Tendsto (fun t : ℝ≥0 => φ (P t x))
        (𝓝 (0 : ℝ≥0)) (𝓝 (φ (f x))) := by
    filter_upwards [] with x
    exact (hφAt x (lt_of_lt_of_le hε (hlower x))).tendsto.comp (hpt x)
  have houterLim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMehler)
    (F := fun t x => φ (P t x)) (f := fun x => φ (f x))
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
  have hEntropyP (t : ℝ≥0) :
      looconcentrationEntropy standardGaussianMehler (P t) =
        (∫ x, φ (P t x) ∂standardGaussianMehler) - m * Real.log m := by
    simp [looconcentrationEntropy, φ, gaussianMehlerXLogX, hstationary t, m]
  have hEntropyF :
      looconcentrationEntropy standardGaussianMehler f =
        (∫ x, φ (f x) ∂standardGaussianMehler) - m * Real.log m := by
    simp [looconcentrationEntropy, φ, gaussianMehlerXLogX, m]
  have hresult : Tendsto
      (fun t : ℝ≥0 =>
        (∫ x, φ (P t x) ∂standardGaussianMehler) - m * Real.log m)
      (𝓝 (0 : ℝ≥0))
      (𝓝 ((∫ x, φ (f x) ∂standardGaussianMehler) - m * Real.log m)) := by
    simpa using houterLim.sub_const (m * Real.log m)
  have hresultP : Tendsto
      (fun t : ℝ≥0 => looconcentrationEntropy standardGaussianMehler (P t))
      (𝓝 (0 : ℝ≥0)) (𝓝 (looconcentrationEntropy standardGaussianMehler f)) := by
    simpa [hEntropyP, hEntropyF] using hresult
  simpa [P, hb] using hresultP

/-- Continuity on the valid time domain follows from the actual initial
entropy endpoint and differentiability at every positive time. The trajectory
is only identified with Mehler entropy for nonnegative times. -/
theorem standardGaussianMehlerEntropyTrajectory_continuousOn_nonneg
    {f : ℝ → ℝ} (hf : Continuous f) {ε B : ℝ}
    (hε : 0 < ε) (hlower : ∀ y, ε ≤ f y) (hupper : ∀ y, f y ≤ B)
    (ψ : ℝ → ℝ)
    (hpath : ∀ (t : ℝ) (ht : 0 ≤ t),
      ψ t = looconcentrationEntropy standardGaussianMehler
        (standardGaussianMehlerAverage f hf.measurable
          ⟨B, by
            intro y
            have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
            rw [Real.norm_eq_abs, abs_of_nonneg hpos]
            exact hupper y⟩ t ht))
    (hderiv : ∀ t, 0 < t → DifferentiableAt ℝ ψ t) :
    ContinuousOn ψ (Set.Ici 0) ∧
      ψ 0 = looconcentrationEntropy standardGaussianMehler f := by
  have hnorm : ∀ y, ‖f y‖ ≤ B := by
    intro y
    have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact hupper y
  let hb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := ⟨B, hnorm⟩
  have haverageZero :
      standardGaussianMehlerAverage f hf.measurable
        ⟨B, by
          intro y
          have hpos : 0 ≤ f y := (le_of_lt hε).trans (hlower y)
          rw [Real.norm_eq_abs, abs_of_nonneg hpos]
          exact hupper y⟩ 0 (by norm_num) = f := by
    funext x
    simp [standardGaussianMehlerAverage, standardGaussianMehlerArgument,
      standardGaussianMehlerDrift, standardGaussianMehlerNoise]
  have hinitial : ψ 0 = looconcentrationEntropy standardGaussianMehler f := by
    have hpath0 := hpath 0 (by norm_num)
    rw [haverageZero] at hpath0
    exact hpath0
  have hpathNN (t : ℝ≥0) :
      ψ (t : ℝ) = looconcentrationEntropy standardGaussianMehler
        (standardGaussianMehlerAverage f hf.measurable hb
          (t : ℝ) t.property) := by
    have h := hpath (t : ℝ) t.property
    unfold standardGaussianMehlerAverage at h ⊢
    exact h
  have hendpoint := tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_nhds_zero
    hf hε hlower hupper
  have hpsiEndpoint : Tendsto (fun t : ℝ≥0 => ψ (t : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 (ψ 0)) := by
    simpa only [hpathNN, hinitial, standardGaussianMehlerAverage] using hendpoint
  have hzero : ContinuousWithinAt ψ (Set.Ici 0) 0 := by
    apply (continuousWithinAt_iff_continuousAt_domRestrict ψ (by norm_num)).2
    change Tendsto (fun t : ℝ≥0 => ψ (t : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 (ψ 0))
    exact hpsiEndpoint
  have hcont : ContinuousOn ψ (Set.Ici 0) := by
    intro t ht
    have htle : 0 ≤ t := by simpa using ht
    rcases eq_or_lt_of_le htle with rfl | htpos
    · exact hzero
    · exact (hderiv t htpos).continuousAt.continuousWithinAt
  exact ⟨hcont, hinitial⟩

/-- Scalar entropy integration lemma for the Gaussian Mehler route. The
trajectory is used only on nonnegative times. Positive-time dissipation and
the weighted-energy decay give a monotone corrected trajectory; equilibrium
at infinity then yields the factor `1/2`. -/
theorem scalarEntropy_le_half_of_dissipation_and_energy_decay
    {ψ energy : ℝ → ℝ} {E₀ : ℝ}
    (hψcont : ContinuousOn ψ (Set.Ici 0))
    (hdissipation : ∀ t, 0 < t → HasDerivAt ψ (-energy t) t)
    (henergy : ∀ t, 0 < t → energy t ≤ Real.exp (-2 * t) * E₀)
    (hequilibrium : Tendsto ψ atTop (𝓝 0)) :
    ψ 0 ≤ E₀ / 2 := by
  let correction : ℝ → ℝ := fun t => E₀ / 2 - E₀ / 2 * Real.exp (-2 * t)
  let G : ℝ → ℝ := ψ + correction
  have hExpCont : Continuous (fun t : ℝ => Real.exp (-2 * t)) := by fun_prop
  have hcorCont : Continuous (fun t : ℝ => E₀ / 2 - E₀ / 2 * Real.exp (-2 * t)) :=
    continuous_const.sub (continuous_const.mul hExpCont)
  have hGcont : ContinuousOn G (Set.Ici 0) := by
    exact hψcont.add (by simpa [correction] using hcorCont.continuousOn)
  have hGderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt G (deriv ψ t + E₀ * Real.exp (-2 * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
      simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
        (Real.exp (-2 * t) * (-2)) t := by
      exact hlin.exp
    have hcor : HasDerivAt
        (fun s : ℝ => E₀ / 2 - E₀ / 2 * Real.exp (-2 * s))
        (0 - E₀ / 2 * (Real.exp (-2 * t) * (-2))) t := by
      exact (hasDerivAt_const t (E₀ / 2)).sub (hexp.const_mul (E₀ / 2))
    have hsum := (hdissipation t ht).add hcor
    have hvalue :
        (-energy t + (0 - E₀ / 2 * (Real.exp (-2 * t) * (-2)))) =
          deriv ψ t + E₀ * Real.exp (-2 * t) := by
      rw [← (hdissipation t ht).deriv]
      ring
    simpa [G, correction] using hsum.congr_deriv hvalue
  have hGmono : MonotoneOn G (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hGcont
    · intro t ht
      have htpos : 0 < t := by simpa [interior_Ici] using ht
      exact (hGderiv t htpos).differentiableAt.differentiableWithinAt
    · intro t ht
      have htpos : 0 < t := by simpa [interior_Ici] using ht
      rw [(hGderiv t htpos).deriv]
      have hd := (hdissipation t htpos).deriv
      rw [hd]
      have he := henergy t htpos
      nlinarith
  have hExpLim : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have hcorLim : Tendsto
      (fun t : ℝ => E₀ / 2 - E₀ / 2 * Real.exp (-2 * t))
      atTop (𝓝 (E₀ / 2)) := by
    simpa using tendsto_const_nhds.sub (hExpLim.const_mul (E₀ / 2))
  have hGLim : Tendsto G atTop (𝓝 (E₀ / 2)) := by
    change Tendsto (fun t : ℝ => ψ t + correction t) atTop (𝓝 (E₀ / 2))
    simpa [correction] using hequilibrium.add hcorLim
  have hEventually : ∀ᶠ t in atTop, G 0 ≤ G t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hGmono (by simp) ht ht
  have hzero : G 0 ≤ E₀ / 2 := ge_of_tendsto hGLim hEventually
  simpa [G, correction, Real.exp_zero] using hzero

/-! The concrete equilibrium producer is reviewed in wave 11. The two
remaining analytic predecessors are the positive-time entropy dissipation
identity and the weighted-energy decay estimate; this scalar theorem keeps
them explicit rather than assuming the target entropy bound. -/

#print axioms tendsto_standardGaussianMehlerAverage_nhds_zero
#print axioms tendsto_looconcentrationEntropy_standardGaussianMehlerAverage_nhds_zero
#print axioms standardGaussianMehlerEntropyTrajectory_continuousOn_nonneg
#print axioms tendsto_standardGaussianMehlerEntropyTrajectory_atTop
#print axioms scalarEntropy_le_half_of_dissipation_and_energy_decay

end LOOConcentration
