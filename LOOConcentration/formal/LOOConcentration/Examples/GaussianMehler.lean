import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

noncomputable abbrev standardGaussianMehler : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The deterministic coefficient in the scalar standard Gaussian Mehler kernel. -/
noncomputable def standardGaussianMehlerDrift (t : ℝ) : ℝ := Real.exp (-t)

/-- The noise coefficient in the scalar standard Gaussian Mehler kernel. -/
noncomputable def standardGaussianMehlerNoise (t : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-2 * t))

/-- The affine argument of the scalar standard Gaussian Mehler kernel. -/
noncomputable def standardGaussianMehlerArgument (t x y : ℝ) : ℝ :=
  standardGaussianMehlerDrift t * x + standardGaussianMehlerNoise t * y

@[fun_prop]
theorem measurable_standardGaussianMehlerArgument (t : ℝ) :
    Measurable (fun z : ℝ × ℝ => standardGaussianMehlerArgument t z.1 z.2) := by
  unfold standardGaussianMehlerArgument standardGaussianMehlerDrift standardGaussianMehlerNoise
  fun_prop

private lemma standardGaussianMehler_noise_sq {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-2 * t) ∧
      standardGaussianMehlerNoise t ^ 2 = 1 - Real.exp (-2 * t) := by
  have harg : -2 * t ≤ 0 := by nlinarith
  have hexp : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr harg
  constructor
  · linarith
  · exact Real.sq_sqrt (by linarith)

/-- The affine image of two independent standard Gaussians in a scalar Mehler
step again has the standard Gaussian law. -/
theorem standardGaussianMehler_map_product_law {t : ℝ} (ht : 0 ≤ t) :
    (standardGaussianMehler.prod standardGaussianMehler).map
      (fun z : ℝ × ℝ => standardGaussianMehlerArgument t z.1 z.2) =
        standardGaussianMehler := by
  let a := standardGaussianMehlerDrift t
  let b := standardGaussianMehlerNoise t
  let va : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩
  let vb : ℝ≥0 := ⟨b ^ 2, sq_nonneg b⟩
  let X : ℝ × ℝ → ℝ := fun z => z.1 * a
  let Y : ℝ × ℝ → ℝ := fun z => z.2 * b
  have ha : a ^ 2 = Real.exp (-2 * t) := by
    dsimp [a, standardGaussianMehlerDrift]
    calc
      Real.exp (-t) ^ 2 = Real.exp (-t) * Real.exp (-t) := by ring
      _ = Real.exp ((-t) + (-t)) := by rw [← Real.exp_add]
      _ = Real.exp (-2 * t) := by
            congr 1
            ring
  have hb : b ^ 2 = 1 - Real.exp (-2 * t) :=
    (standardGaussianMehler_noise_sq ht).2
  have hvariance : va + vb = 1 := by
    apply Subtype.ext
    change a ^ 2 + b ^ 2 = 1
    rw [ha, hb]
    ring
  have hX : (standardGaussianMehler.prod standardGaussianMehler).map X =
      ProbabilityTheory.gaussianReal 0 va := by
    calc
      _ = ((standardGaussianMehler.prod standardGaussianMehler).map Prod.fst).map
          (fun x : ℝ => x * a) := by
            change (standardGaussianMehler.prod standardGaussianMehler).map
              ((fun x : ℝ => x * a) ∘ Prod.fst) = _
            rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => x * a))
              measurable_fst]
      _ = standardGaussianMehler.map (fun x : ℝ => x * a) := by
            rw [measurePreserving_fst.map_eq]
      _ = ProbabilityTheory.gaussianReal 0 va := by
            rw [ProbabilityTheory.gaussianReal_map_mul_const]
            simp only [mul_zero, mul_one]
            congr 1
  have hY : (standardGaussianMehler.prod standardGaussianMehler).map Y =
      ProbabilityTheory.gaussianReal 0 vb := by
    calc
      _ = ((standardGaussianMehler.prod standardGaussianMehler).map Prod.snd).map
          (fun y : ℝ => y * b) := by
            change (standardGaussianMehler.prod standardGaussianMehler).map
              ((fun y : ℝ => y * b) ∘ Prod.snd) = _
            rw [← Measure.map_map (by fun_prop : Measurable (fun y : ℝ => y * b))
              measurable_snd]
      _ = standardGaussianMehler.map (fun y : ℝ => y * b) := by
            rw [measurePreserving_snd.map_eq]
      _ = ProbabilityTheory.gaussianReal 0 vb := by
            rw [ProbabilityTheory.gaussianReal_map_mul_const]
            simp only [mul_zero, mul_one]
            congr 1
  have hXY : ProbabilityTheory.IndepFun X Y
      (standardGaussianMehler.prod standardGaussianMehler) := by
    have hfst : ProbabilityTheory.IndepFun
        (fun z : ℝ × ℝ => z.1) (fun z => z.2)
        (standardGaussianMehler.prod standardGaussianMehler) :=
      ProbabilityTheory.indepFun_prod (μ := standardGaussianMehler)
        (ν := standardGaussianMehler) (X := id) (Y := id)
        measurable_id measurable_id
    have hmeasA : Measurable (fun x : ℝ => x * a) := by fun_prop
    have hmeasB : Measurable (fun y : ℝ => y * b) := by fun_prop
    exact hfst.comp hmeasA hmeasB
  have hsum := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
    hXY hX hY
  have hsumfun : X + Y = fun z : ℝ × ℝ =>
      standardGaussianMehlerArgument t z.1 z.2 := by
    funext z
    dsimp [X, Y, standardGaussianMehlerArgument, a, b]
    ring
  rw [hsumfun] at hsum
  calc
    _ = ProbabilityTheory.gaussianReal (0 + 0) (va + vb) := hsum
    _ = standardGaussianMehler := by
          rw [hvariance]
          simp [standardGaussianMehler]

/-- A bounded measurable scalar function averaged against one Mehler noise
coordinate. The nonnegative time proof restricts the public construction to
the intended real square-root coefficient, and the explicit bound makes every
section an integrable source average. -/
noncomputable def standardGaussianMehlerAverage
    (f : ℝ → ℝ) (_hf : Measurable f)
    (_hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    (t : ℝ) (_ht : 0 ≤ t) : ℝ → ℝ :=
  fun x => ∫ y, f (standardGaussianMehlerArgument t x y) ∂standardGaussianMehler

private lemma standardGaussianMehler_joint_measurable
    {t : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun z : ℝ × ℝ =>
      f (standardGaussianMehlerArgument t z.1 z.2)) := by
  exact hf.comp (measurable_standardGaussianMehlerArgument t)

/-- Every source section in the public Mehler constructor is integrable. -/
theorem integrable_standardGaussianMehler_section
    {t : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Integrable (fun y => f (standardGaussianMehlerArgument t x y))
      standardGaussianMehler := by
  rcases hbounded with ⟨M, hM⟩
  have hmeas : Measurable (fun y : ℝ =>
      f (standardGaussianMehlerArgument t x y)) := by
    apply hf.comp
    unfold standardGaussianMehlerArgument standardGaussianMehlerDrift
      standardGaussianMehlerNoise
    fun_prop
  exact (integrable_const M).mono' hmeas.aestronglyMeasurable
    (ae_of_all standardGaussianMehler fun y => hM _)

/-- The Mehler averaging operation preserves the interval `[-M, M]`. -/
theorem standardGaussianMehlerAverage_bounds
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hbounded : ∀ y, ‖f y‖ ≤ M) (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    -M ≤ standardGaussianMehlerAverage f hf ⟨M, hbounded⟩ t ht x ∧
      standardGaussianMehlerAverage f hf ⟨M, hbounded⟩ t ht x ≤ M := by
  have hsec := integrable_standardGaussianMehler_section (t := t) hf ⟨M, hbounded⟩ x
  have hlow : ∀ y, -M ≤ f (standardGaussianMehlerArgument t x y) := by
    intro y
    have habs : |f (standardGaussianMehlerArgument t x y)| ≤ M := by
      simpa only [Real.norm_eq_abs] using hbounded (standardGaussianMehlerArgument t x y)
    exact (abs_le.mp habs).1
  have hupp : ∀ y, f (standardGaussianMehlerArgument t x y) ≤ M := by
    intro y
    have habs : |f (standardGaussianMehlerArgument t x y)| ≤ M := by
      simpa only [Real.norm_eq_abs] using hbounded (standardGaussianMehlerArgument t x y)
    exact (abs_le.mp habs).2
  constructor
  · calc
      -M = ∫ _ : ℝ, -M ∂standardGaussianMehler := by simp
      _ ≤ ∫ y, f (standardGaussianMehlerArgument t x y)
          ∂standardGaussianMehler :=
            integral_mono (integrable_const (-M)) hsec
              hlow
  · calc
      (∫ y, f (standardGaussianMehlerArgument t x y)
          ∂standardGaussianMehler) ≤ ∫ _ : ℝ, M ∂standardGaussianMehler :=
          integral_mono hsec (integrable_const M)
              hupp
      _ = M := by simp

/-- A pointwise lower bound on the source function is preserved by the
standard Gaussian Mehler average. -/
theorem standardGaussianMehlerAverage_lower_bound
    {f : ℝ → ℝ} (hf : Measurable f) {M ε : ℝ}
    (hbounded : ∀ y, ‖f y‖ ≤ M) (hlower : ∀ y, ε ≤ f y)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    ε ≤ standardGaussianMehlerAverage f hf ⟨M, hbounded⟩ t ht x := by
  have hsec := integrable_standardGaussianMehler_section (t := t) hf ⟨M, hbounded⟩ x
  calc
    ε = ∫ _ : ℝ, ε ∂standardGaussianMehler := by simp
    _ ≤ ∫ y, f (standardGaussianMehlerArgument t x y)
        ∂standardGaussianMehler :=
          integral_mono (integrable_const ε) hsec
            (fun y => hlower (standardGaussianMehlerArgument t x y))

/-- The public scalar Mehler average is measurable in its outer coordinate. -/
theorem measurable_standardGaussianMehlerAverage
    {f : ℝ → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Measurable (standardGaussianMehlerAverage f hf hbounded t ht) := by
  have hjoint : StronglyMeasurable
      (fun z : ℝ × ℝ => f (standardGaussianMehlerArgument t z.1 z.2)) :=
    (standardGaussianMehler_joint_measurable (t := t) (f := f) hf).stronglyMeasurable
  have houter : StronglyMeasurable
    (fun x : ℝ => ∫ y, f (standardGaussianMehlerArgument t x y)
        ∂standardGaussianMehler) :=
    hjoint.integral_prod_right' (ν := standardGaussianMehler)
  exact houter.measurable

private lemma integrable_standardGaussianMehler_joint
    {t : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun z : ℝ × ℝ =>
      f (standardGaussianMehlerArgument t z.1 z.2))
      (standardGaussianMehler.prod standardGaussianMehler) := by
  rcases hbounded with ⟨M, hM⟩
  have hjoint := standardGaussianMehler_joint_measurable (t := t) (f := f) hf
  exact (integrable_const M).mono' hjoint.aestronglyMeasurable
    (ae_of_all _ fun z => hM _)

/-- Stationarity of the scalar Mehler kernel, proved by bounded-kernel Fubini
and the actual affine pushforward law of two independent standard Gaussians. -/
theorem integral_standardGaussianMehlerAverage_eq
    {f : ℝ → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, standardGaussianMehlerAverage f hf hbounded t ht x
      ∂standardGaussianMehler) = ∫ x, f x ∂standardGaussianMehler := by
  have hjointInt := integrable_standardGaussianMehler_joint (t := t) hf hbounded
  calc
    (∫ x, standardGaussianMehlerAverage f hf hbounded t ht x
        ∂standardGaussianMehler) =
      ∫ x, ∫ y, f (standardGaussianMehlerArgument t x y)
        ∂standardGaussianMehler ∂standardGaussianMehler := by
          apply integral_congr_ae
          exact ae_of_all standardGaussianMehler fun x => rfl
    _ = ∫ z, f (standardGaussianMehlerArgument t z.1 z.2)
        ∂(standardGaussianMehler.prod standardGaussianMehler) :=
          (integral_prod _ hjointInt).symm
    _ = ∫ x, f x ∂standardGaussianMehler := by
          calc
            _ = ∫ x, f x
                ∂((standardGaussianMehler.prod standardGaussianMehler).map
                  (fun z : ℝ × ℝ => standardGaussianMehlerArgument t z.1 z.2)) := by
                    symm
                    exact integral_map_of_stronglyMeasurable
                      (by fun_prop) hf.stronglyMeasurable
            _ = ∫ x, f x ∂standardGaussianMehler := by
                  rw [standardGaussianMehler_map_product_law ht]

end LOOConcentration
