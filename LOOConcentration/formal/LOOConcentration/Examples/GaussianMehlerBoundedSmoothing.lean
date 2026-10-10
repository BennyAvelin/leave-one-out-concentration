import LOOConcentration.Examples.GaussianMehler
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Positive-time smoothing of bounded measurable Gaussian Mehler inputs

The proof shifts the Gaussian density and differentiates the resulting
exponential weight. The source function remains measurable and bounded; no
source derivative or continuity is used.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology NNReal

private theorem integrable_bounded_probability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hbound)

private theorem integrable_abs_standardGaussianMehler :
    Integrable (fun y : ℝ => |y|) standardGaussianMehler := by
  have hid : Integrable (fun y : ℝ => y) standardGaussianMehler := by
    apply memLp_one_iff_integrable.mp
    exact ProbabilityTheory.memLp_id_gaussianReal
      (μ := 0) (v := (1 : ℝ≥0)) (1 : ℝ≥0)
  simpa only [Real.norm_eq_abs] using hid.norm

/-- Every two-sided exponential in the coordinate is integrable for the actual
standard Gaussian law. -/
private theorem integrable_exp_abs_standardGaussianMehler (C : ℝ) :
    Integrable (fun y : ℝ => Real.exp (C * |y|)) standardGaussianMehler := by
  have hpos : Integrable (fun y : ℝ => Real.exp (C * y)) standardGaussianMehler := by
    simpa [standardGaussianMehler] using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : ℝ≥0)) C)
  have hneg : Integrable (fun y : ℝ => Real.exp (-C * y)) standardGaussianMehler := by
    simpa [standardGaussianMehler] using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : ℝ≥0)) (-C))
  refine (hpos.add hneg).mono'
    (Real.measurable_exp.comp (measurable_const.mul measurable_abs)).aestronglyMeasurable ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    have hpoint : Real.exp (C * y) ≤ Real.exp (C * y) + Real.exp (-(C * y)) := by
      calc
        Real.exp (C * y) = Real.exp (C * y) + 0 := by simp
        _ ≤ Real.exp (C * y) + Real.exp (-(C * y)) :=
          add_le_add le_rfl (Real.exp_nonneg _)
    simpa only [Pi.add_apply, neg_mul, mul_neg] using hpoint
  · rw [abs_of_neg (lt_of_not_ge hy)]
    have hpoint : Real.exp (-(C * y)) ≤ Real.exp (C * y) + Real.exp (-(C * y)) := by
      calc
        Real.exp (-(C * y)) = 0 + Real.exp (-(C * y)) := by simp
        _ ≤ Real.exp (C * y) + Real.exp (-(C * y)) :=
          add_le_add (Real.exp_nonneg _) le_rfl
    simpa only [Pi.add_apply, neg_mul, mul_neg] using hpoint

private theorem exp_abs_linear_polynomial_bound
    {q M A B y : ℝ} (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    M * Real.exp (q * |y|) * (A * |y| + B) ≤
      (M * (A + B)) * Real.exp ((q + 1) * |y|) := by
  have hyexp : |y| ≤ Real.exp |y| := by
    have h := Real.add_one_le_exp (|y|)
    linarith
  have honeexp : 1 ≤ Real.exp |y| := by
    have h := Real.add_one_le_exp (|y|)
    linarith [abs_nonneg y]
  have hBexp : B ≤ B * Real.exp |y| := by
    calc
      B = B * 1 := by ring
      _ ≤ B * Real.exp |y| := mul_le_mul_of_nonneg_left honeexp hB
  have hpoly : A * |y| + B ≤ (A + B) * Real.exp |y| := by
    calc
      A * |y| + B ≤ A * Real.exp |y| + B * Real.exp |y| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hyexp hA)
          hBexp
      _ = (A + B) * Real.exp |y| := by ring
  calc
    M * Real.exp (q * |y|) * (A * |y| + B) ≤
        M * Real.exp (q * |y|) * ((A + B) * Real.exp |y|) :=
      mul_le_mul_of_nonneg_left hpoly
        (mul_nonneg hM (Real.exp_nonneg _))
    _ = (M * (A + B)) * Real.exp ((q + 1) * |y|) := by
      rw [show (q + 1) * |y| = q * |y| + |y| by ring, Real.exp_add]
      ring

private theorem standardGaussian_exp_shift_pdf (c y : ℝ) :
    ProbabilityTheory.gaussianPDFReal c (1 : ℝ≥0) y =
      ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) y *
        Real.exp (c * y - c ^ 2 / 2) := by
  simp only [ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_one,
    mul_one, sub_zero]
  have hexpArg : -(y - c) ^ 2 / 2 = -y ^ 2 / 2 + (c * y - c ^ 2 / 2) := by ring
  rw [hexpArg, Real.exp_add]
  ring

/-- The exact density-shift formula used to differentiate a Mehler average.
It follows from the actual translated Gaussian law and its density ratio. -/
private theorem standardGaussian_shift_weight_integral {g : ℝ → ℝ}
    (hg : Measurable g) (c : ℝ) :
    (∫ y, g (y + c) ∂standardGaussianMehler) =
      ∫ y, g y * Real.exp (c * y - c ^ 2 / 2) ∂standardGaussianMehler := by
  have hmap : standardGaussianMehler.map (fun y : ℝ => y + c) =
      ProbabilityTheory.gaussianReal c (1 : ℝ≥0) := by
    simpa [standardGaussianMehler] using
      (ProbabilityTheory.gaussianReal_map_add_const
        (μ := 0) (v := (1 : ℝ≥0)) c)
  have hmapIntegral :
      (∫ y, g y ∂standardGaussianMehler.map (fun y : ℝ => y + c)) =
        ∫ y, g (y + c) ∂standardGaussianMehler :=
    integral_map (by fun_prop) hg.aestronglyMeasurable
  calc
    (∫ y, g (y + c) ∂standardGaussianMehler) =
        ∫ y, g y ∂standardGaussianMehler.map (fun y : ℝ => y + c) :=
      hmapIntegral.symm
    _ = ∫ y, g y ∂ProbabilityTheory.gaussianReal c (1 : ℝ≥0) := by rw [hmap]
    _ = ∫ y, ProbabilityTheory.gaussianPDFReal c (1 : ℝ≥0) y * g y := by
      rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (μ := c) (v := (1 : ℝ≥0)) (by norm_num)]
      rfl
    _ = ∫ y, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) y *
        (g y * Real.exp (c * y - c ^ 2 / 2)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change ProbabilityTheory.gaussianPDFReal c (1 : ℝ≥0) y * g y = _
        rw [standardGaussian_exp_shift_pdf]
        ring
    _ = ∫ y, g y * Real.exp (c * y - c ^ 2 / 2)
        ∂standardGaussianMehler := by
      symm
      rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)]
      rfl

private theorem integrable_standardGaussian_id_mul_bounded {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun y : ℝ => y * g y) standardGaussianMehler := by
  have hid : Integrable (fun y : ℝ => y) standardGaussianMehler := by
    apply memLp_one_iff_integrable.mp
    exact ProbabilityTheory.memLp_id_gaussianReal
      (μ := 0) (v := (1 : ℝ≥0)) (1 : ℝ≥0)
  exact hid.mul_bdd hg.aestronglyMeasurable (ae_of_all _ hM)

private theorem standardGaussianMehlerAverage_hasDerivAt
    {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    HasDerivAt
      (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht))
      ((Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) *
        ∫ y, y * h (Real.exp (-t) * x₀ +
          Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂standardGaussianMehler) x₀ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let q : ℝ := a / b
  let H : ℝ → ℝ := fun y => h (a * x₀ + b * y)
  let G : ℝ → ℝ → ℝ := fun x y =>
    H y * Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)
  let G' : ℝ → ℝ → ℝ := fun x y =>
    H y * Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2) *
      (q * y - q ^ 2 * (x - x₀))
  have hbpos : 0 < b := by
    dsimp [b]
    apply Real.sqrt_pos.2
    have hexp : Real.exp (-2 * t) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hqpos : 0 < q := by
    dsimp [q, a]
    exact div_pos (Real.exp_pos _) hbpos
  have hqb : q * b = a := by
    dsimp [q]
    exact div_mul_cancel₀ a hbpos.ne'
  have hHmeas : Measurable H := by
    exact hh.comp (by fun_prop)
  have hHbound (y : ℝ) : ‖H y‖ ≤ M := hM _
  have hHint : Integrable H standardGaussianMehler :=
    integrable_bounded_probability hHmeas hHbound
  have hGmeas (x : ℝ) : Measurable (G x) := by
    dsimp [G]
    exact hHmeas.mul (by fun_prop)
  have hGprimeMeas (x : ℝ) : Measurable (G' x) := by
    dsimp [G']
    fun_prop
  have hGprimeAt (x y : ℝ) : HasDerivAt (G · y)
      (G' x y) x := by
    have hdelta : HasDerivAt (fun z : ℝ => q * (z - x₀)) q x := by
      have hsub : HasDerivAt (fun z : ℝ => z - x₀) 1 x :=
        (hasDerivAt_id x).sub_const x₀
      simpa only [mul_one] using HasDerivAt.const_mul q hsub
    have hlinear : HasDerivAt
        (fun z : ℝ => q * (z - x₀) * y) (q * y) x := hdelta.mul_const y
    have hquad := hdelta.pow 2
    have hquadNeg : HasDerivAt
        (fun z : ℝ => -(q * (z - x₀)) ^ 2 / 2)
        (-q ^ 2 * (x - x₀)) x := by
      apply (hquad.neg.div_const (2 : ℝ)).congr_deriv
      norm_num [pow_one]
      ring
    have harg : HasDerivAt
        (fun z : ℝ => q * (z - x₀) * y - (q * (z - x₀)) ^ 2 / 2)
        (q * y - q ^ 2 * (x - x₀)) x := by
      have hargFun :
          (fun z : ℝ => q * (z - x₀) * y - (q * (z - x₀)) ^ 2 / 2) =
            (fun z : ℝ => q * (z - x₀) * y) +
              (fun z : ℝ => -(q * (z - x₀)) ^ 2 / 2) := by
        funext z
        simp only [Pi.add_apply]
        ring
      have hderivEq : q * y + (-q ^ 2 * (x - x₀)) =
          q * y - q ^ 2 * (x - x₀) := by ring
      rw [hargFun]
      exact (hlinear.add hquadNeg).congr_deriv hderivEq
    have hexp := harg.exp
    have hmul := HasDerivAt.const_mul (H y) hexp
    change HasDerivAt
      (fun z : ℝ => H y * Real.exp
        (q * (z - x₀) * y - (q * (z - x₀)) ^ 2 / 2))
      (G' x y) x
    exact hmul.congr_deriv (by dsimp [G']; ring)
  have hGshift (x : ℝ) :
      standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht) x =
        ∫ y, G x y ∂standardGaussianMehler := by
    have harg (y : ℝ) : a * x + b * y = a * x₀ + b * (y + q * (x - x₀)) := by
      rw [← hqb]
      ring
    have hshift := standardGaussian_shift_weight_integral
      (g := H) hHmeas (q * (x - x₀))
    change (∫ y, h (a * x + b * y) ∂standardGaussianMehler) = _
    rw [show (fun y : ℝ => h (a * x + b * y)) =
      fun y => H (y + q * (x - x₀)) from by
        funext y
        dsimp [H]
        rw [harg y]]
    simpa [G] using hshift
  have hGprimeBound (x y : ℝ)
      (hx : x ∈ Metric.ball x₀ 1) :
      ‖G' x y‖ ≤ M * (q + q ^ 2) *
        Real.exp ((q + 1) * |y|) := by
    have hδ : |x - x₀| ≤ 1 := by
      have hx' : dist x x₀ < 1 := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at hx'
      exact le_of_lt (by simpa [abs_sub_comm] using hx')
    have hqδ : |q * (x - x₀)| ≤ q := by
      rw [abs_mul, abs_of_pos hqpos]
      calc
        q * |x - x₀| ≤ q * 1 := mul_le_mul_of_nonneg_left hδ hqpos.le
        _ = q := by ring
    have hexpArg :
        q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2 ≤ q * |y| := by
      have hlin : q * (x - x₀) * y ≤ q * |y| := by
        calc
          q * (x - x₀) * y ≤ |q * (x - x₀) * y| := le_abs_self _
          _ = |q * (x - x₀)| * |y| := abs_mul _ _
          _ ≤ q * |y| := mul_le_mul_of_nonneg_right hqδ (abs_nonneg _)
      have hsq : 0 ≤ (q * (x - x₀)) ^ 2 / 2 := by positivity
      linarith
    have hexp :
        ‖Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)‖ ≤
          Real.exp (q * |y|) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hexpArg
    have hfactor : |q * y - q ^ 2 * (x - x₀)| ≤ q * |y| + q ^ 2 := by
      calc
        |q * y - q ^ 2 * (x - x₀)| ≤ |q * y| + |q ^ 2 * (x - x₀)| := abs_sub _ _
        _ = q * |y| + q ^ 2 * |x - x₀| := by
          rw [abs_mul, abs_of_pos hqpos, abs_mul, abs_of_nonneg (sq_nonneg q)]
        _ ≤ q * |y| + q ^ 2 := by
          calc
            _ ≤ q * |y| + q ^ 2 * 1 := add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hδ (sq_nonneg q))
            _ = q * |y| + q ^ 2 := by ring
    calc
      ‖G' x y‖ = ‖H y‖ *
          ‖Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)‖ *
          |q * y - q ^ 2 * (x - x₀)| := by
            simp [G', norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ M * Real.exp (q * |y|) * (q * |y| + q ^ 2) := by
        have hexpbound : ‖H y‖ *
            ‖Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)‖ ≤
              M * Real.exp (q * |y|) := by
          calc
            _ ≤ M * ‖Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)‖ :=
              mul_le_mul_of_nonneg_right (hHbound y) (norm_nonneg _)
            _ ≤ M * Real.exp (q * |y|) := mul_le_mul_of_nonneg_left hexp hM0
        calc
          _ ≤ M * Real.exp (q * |y|) * |q * y - q ^ 2 * (x - x₀)| :=
            mul_le_mul_of_nonneg_right hexpbound (abs_nonneg _)
          _ ≤ M * Real.exp (q * |y|) * (q * |y| + q ^ 2) :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ (M * (q + q ^ 2)) * Real.exp ((q + 1) * |y|) :=
        exp_abs_linear_polynomial_bound (y := y) hM0 hqpos.le (sq_nonneg q)
  have hmajorantInt : Integrable
      (fun y : ℝ => (M * (q + q ^ 2)) * Real.exp ((q + 1) * |y|))
      standardGaussianMehler := by
    have h := integrable_exp_abs_standardGaussianMehler (q + 1)
    exact h.const_mul (M * (q + q ^ 2))
  have hF'zero : G' x₀ = fun y => q * (y * H y) := by
    funext y
    simp [G', H]
    ring
  have hFprimeMeas : AEStronglyMeasurable (G' x₀) standardGaussianMehler := by
    rw [hF'zero]
    exact ((measurable_id.mul hHmeas).const_mul q).aestronglyMeasurable
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x₀ zero_lt_one)
    (by filter_upwards [] with x; exact (hGmeas x).aestronglyMeasurable)
    (by simpa [G] using hHint)
    hFprimeMeas
    (by
      filter_upwards [] with y
      intro x hx
      exact hGprimeBound x y hx)
    hmajorantInt
    (by
      filter_upwards [] with y
      intro x hx
      exact hGprimeAt x y)
  have hparamDeriv : HasDerivAt
      (fun x => ∫ y, G x y ∂standardGaussianMehler)
      (q * ∫ y, y * H y ∂standardGaussianMehler) x₀ := by
    apply hparam.2.congr_deriv
    rw [hF'zero, integral_const_mul]
  have hsourcePath :
      (fun x => standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht) x) =
        fun x => ∫ y, G x y ∂standardGaussianMehler := by
    funext x
    exact hGshift x
  change HasDerivAt
    (fun x => standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht) x)
    _ x₀
  rw [hsourcePath]
  have htarget :
      q * ∫ y, y * H y ∂standardGaussianMehler =
        (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) *
          ∫ y, y * h (Real.exp (-t) * x₀ +
            Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂standardGaussianMehler := by
    dsimp [H, q, a, b]
  exact hparamDeriv.congr_deriv htarget

private theorem standardGaussianMehlerAverage_deriv_continuous
    {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    Continuous (deriv
      (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht))) := by
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let q : ℝ := a / b
  have hbpos : 0 < b := by
    dsimp [b]
    apply Real.sqrt_pos.2
    have hexp : Real.exp (-2 * t) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hqpos : 0 < q := by
    dsimp [q, a]
    exact div_pos (Real.exp_pos _) hbpos
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
  have habsInt := integrable_abs_standardGaussianMehler
  have hcontinuousAt (x₀ : ℝ) :
      ContinuousAt (deriv
        (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht))) x₀ := by
    let H : ℝ → ℝ := fun y => h (a * x₀ + b * y)
    let Q : ℝ → ℝ → ℝ := fun x y =>
      (y - q * (x - x₀)) * H y *
        Real.exp (q * (x - x₀) * y - (q * (x - x₀)) ^ 2 / 2)
    have hHmeas : Measurable H := hh.comp (by fun_prop)
    have hHbound (y : ℝ) : ‖H y‖ ≤ M := hM _
    have hqB : q * b = a := by
      dsimp [q]
      exact div_mul_cancel₀ a hbpos.ne'
    have hsourceShift (x : ℝ) :
        (q * ∫ y, y * h (a * x + b * y) ∂standardGaussianMehler) =
          q * ∫ y, Q x y ∂standardGaussianMehler := by
      let c : ℝ := q * (x - x₀)
      let g : ℝ → ℝ := fun y => (y - c) * H y
      have hgmeas : Measurable g := by
        dsimp [g]
        fun_prop
      have harg (y : ℝ) : a * x + b * y = a * x₀ + b * (y + c) := by
        dsimp [c]
        rw [← hqB]
        ring
      have hleft := standardGaussian_shift_weight_integral
        (g := g) hgmeas c
      have hleftEq :
          (∫ y, y * h (a * x + b * y) ∂standardGaussianMehler) =
            ∫ y, g (y + c) ∂standardGaussianMehler := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          dsimp [g, H]
          rw [harg y]
          ring
      calc
        _ = q * ∫ y, g (y + c) ∂standardGaussianMehler := by rw [hleftEq]
        _ = q * ∫ y, g y * Real.exp (c * y - c ^ 2 / 2)
              ∂standardGaussianMehler := by rw [hleft]
        _ = q * ∫ y, Q x y ∂standardGaussianMehler := by
          apply congrArg (fun z : ℝ => q * z)
          apply integral_congr_ae
          exact ae_of_all _ fun y => by
            dsimp [Q, g, c]
    have hQmeas (x : ℝ) : Measurable (Q x) := by
      dsimp [Q]
      fun_prop
    have hQbound (x : ℝ) (y : ℝ)
        (hx : x ∈ Metric.ball x₀ 1) :
        ‖Q x y‖ ≤ (M * (1 + q)) * Real.exp ((q + 1) * |y|) := by
      let c : ℝ := q * (x - x₀)
      have hδ : |x - x₀| ≤ 1 := by
        have hx' : dist x x₀ < 1 := Metric.mem_ball.mp hx
        rw [Real.dist_eq] at hx'
        exact le_of_lt (by simpa [abs_sub_comm] using hx')
      have hqδ : |c| ≤ q := by
        rw [show c = q * (x - x₀) by rfl, abs_mul, abs_of_pos hqpos]
        calc
          q * |x - x₀| ≤ q * 1 := mul_le_mul_of_nonneg_left hδ hqpos.le
          _ = q := by ring
      have hexpArg :
          c * y - c ^ 2 / 2 ≤ q * |y| := by
        have hlin : c * y ≤ q * |y| := by
          calc
            c * y ≤ |c * y| := le_abs_self _
            _ = |c| * |y| := abs_mul _ _
            _ ≤ q * |y| := mul_le_mul_of_nonneg_right hqδ (abs_nonneg _)
        have hsq : 0 ≤ c ^ 2 / 2 := by positivity
        linarith
      have hexp :
          ‖Real.exp (c * y - c ^ 2 / 2)‖ ≤
            Real.exp (q * |y|) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hexpArg
      have hfactor :
          |y - c| ≤ |y| + q := by
        calc
          |y - c| ≤ |y| + |c| := abs_sub _ _
          _ ≤ |y| + q := add_le_add le_rfl hqδ
      have hprod : |y - c| * ‖H y‖ ≤ (|y| + q) * M :=
        mul_le_mul hfactor (hHbound y) (norm_nonneg _) (add_nonneg (abs_nonneg _) hqpos.le)
      calc
        ‖Q x y‖ = |y - c| * ‖H y‖ * ‖Real.exp (c * y - c ^ 2 / 2)‖ := by
          simp [Q, c, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ ((|y| + q) * M) * ‖Real.exp (c * y - c ^ 2 / 2)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ ((|y| + q) * M) * Real.exp (q * |y|) :=
          mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (add_nonneg (abs_nonneg y) hqpos.le) hM0)
        _ = M * Real.exp (q * |y|) * (|y| + q) := by ring
        _ ≤ (M * (1 + q)) * Real.exp ((q + 1) * |y|) := by
          simpa only [one_mul] using
            (exp_abs_linear_polynomial_bound (q := q) (M := M) (A := 1)
              (B := q) (y := y) hM0 (by norm_num) hqpos.le)
    have hQmajorant : Integrable
        (fun y : ℝ => (M * (1 + q)) * Real.exp ((q + 1) * |y|))
        standardGaussianMehler := by
      have h := integrable_exp_abs_standardGaussianMehler (q + 1)
      exact h.const_mul (M * (1 + q))
    have hQcont : ∀ᵐ y ∂standardGaussianMehler,
        ContinuousAt (fun x => Q x y) x₀ := by
      filter_upwards [] with y
      exact (by fun_prop : Continuous fun x => Q x y).continuousAt
    have hQintegralCont := continuousAt_of_dominated
      (x₀ := x₀) (bound := fun y => (M * (1 + q)) * Real.exp ((q + 1) * |y|))
      (by filter_upwards [] with x; exact (hQmeas x).aestronglyMeasurable)
      (by
        filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
        exact ae_of_all _ (fun y => hQbound x y hx))
      hQmajorant hQcont
    have hderivFormula (x : ℝ) :=
      standardGaussianMehlerAverage_hasDerivAt hh hM ht x
    have hderivEq (x : ℝ) :
        deriv (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht)) x =
          q * ∫ y, Q x y ∂standardGaussianMehler := by
      rw [(hderivFormula x).deriv]
      exact hsourceShift x
    have hcont : ContinuousAt
        (deriv (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht))) x₀ := by
      have heq : deriv
          (standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht)) =
            fun x => q * ∫ y, Q x y ∂standardGaussianMehler := by
        funext x
        exact hderivEq x
      rw [heq]
      exact continuousAt_const.mul hQintegralCont
    exact hcont
  exact continuous_iff_continuousAt.mpr hcontinuousAt

/-- For bounded measurable scalar `h` and every positive time, its actual
standard Gaussian Mehler average is C¹ in space. Its derivative is the
Gaussian score formula and obeys the uniform first-moment bound. -/
theorem standardGaussianMehlerAverage_boundedMeasurable_C1
    {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    let P := standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht)
    ContDiff ℝ 1 P ∧
      (∀ x, deriv P x =
        (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) *
          ∫ y, y * h (Real.exp (-t) * x +
            Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂standardGaussianMehler) ∧
      (∀ x, ‖deriv P x‖ ≤
        (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) * M *
          ∫ y, |y| ∂standardGaussianMehler) := by
  dsimp
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
  let P := standardGaussianMehlerAverage h hh ⟨M, hM⟩ t (le_of_lt ht)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let q : ℝ := a / b
  have hbpos : 0 < b := by
    dsimp [b]
    apply Real.sqrt_pos.2
    have hexp : Real.exp (-2 * t) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hqpos : 0 < q := by
    dsimp [q, a]
    exact div_pos (Real.exp_pos _) hbpos
  have hformula (x : ℝ) :=
    standardGaussianMehlerAverage_hasDerivAt hh hM ht x
  have hderivContinuous :=
    standardGaussianMehlerAverage_deriv_continuous hh hM ht
  have hC1 : ContDiff ℝ 1 P := by
    apply (contDiff_one_iff_deriv).2
    refine ⟨?_, ?_⟩
    · intro x
      exact (hformula x).differentiableAt
    · simpa [P] using hderivContinuous
  have hformula' (x : ℝ) :
      deriv P x = q * ∫ y, y * h (a * x + b * y) ∂standardGaussianMehler := by
    exact (hformula x).deriv
  have hId : Integrable (fun y : ℝ => y) standardGaussianMehler := by
    apply memLp_one_iff_integrable.mp
    exact ProbabilityTheory.memLp_id_gaussianReal
      (μ := 0) (v := (1 : ℝ≥0)) (1 : ℝ≥0)
  have hAbs : Integrable (fun y : ℝ => |y|) standardGaussianMehler := by
    simpa only [Real.norm_eq_abs] using hId.norm
  have hderivBound (x : ℝ) :
      ‖deriv P x‖ ≤ q * M * ∫ y, |y| ∂standardGaussianMehler := by
    have hHxMeas : Measurable (fun y : ℝ => h (a * x + b * y)) :=
      hh.comp (by fun_prop)
    have hHxBound (y : ℝ) : ‖h (a * x + b * y)‖ ≤ M := hM _
    have hweighted := integrable_standardGaussian_id_mul_bounded hHxMeas hHxBound
    have habsM : Integrable (fun y : ℝ => |y| * M) standardGaussianMehler :=
      hAbs.mul_const M
    have hpoint (y : ℝ) :
        ‖y * h (a * x + b * y)‖ ≤ |y| * M := by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using hHxBound y) (abs_nonneg _)
    calc
      ‖deriv P x‖ = q *
          ‖∫ y, y * h (a * x + b * y) ∂standardGaussianMehler‖ := by
            rw [hformula' x, norm_mul, Real.norm_eq_abs, abs_of_pos hqpos]
      _ ≤ q * ∫ y, ‖y * h (a * x + b * y)‖ ∂standardGaussianMehler := by
        have hnormInt :
            ‖∫ y, y * h (a * x + b * y) ∂standardGaussianMehler‖ ≤
              ∫ y, ‖y * h (a * x + b * y)‖ ∂standardGaussianMehler :=
          norm_integral_le_integral_norm _
        exact mul_le_mul_of_nonneg_left hnormInt hqpos.le
      _ ≤ q * ∫ y, |y| * M ∂standardGaussianMehler :=
        mul_le_mul_of_nonneg_left
          (integral_mono hweighted.norm habsM hpoint) hqpos.le
      _ = q * M * ∫ y, |y| ∂standardGaussianMehler := by
        rw [show (∫ y, |y| * M ∂standardGaussianMehler) =
          M * ∫ y, |y| ∂standardGaussianMehler by
            calc
              _ = ∫ y, M * |y| ∂standardGaussianMehler := by
                apply integral_congr_ae
                exact ae_of_all _ fun y => by ring
              _ = M * ∫ y, |y| ∂standardGaussianMehler := integral_const_mul _ _]
        ring
  refine ⟨hC1, ?_, ?_⟩
  · intro x
    simpa [P, a, b, q] using hformula' x
  · intro x
    simpa [P, a, b, q] using hderivBound x

#print axioms standardGaussianMehlerAverage_boundedMeasurable_C1

end LOOConcentration
