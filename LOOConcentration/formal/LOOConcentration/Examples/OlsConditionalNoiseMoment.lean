import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
import LOOConcentration.Examples.GaussianSquareMGF
import LOOConcentration.Examples.OlsPairwise

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory ProbabilityTheory

private noncomputable abbrev olsNoiseGaussianLaw (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi fun _ : Fin r => standardGaussian

private lemma olsStandardGaussian_id_memLp :
    MemLp id 2 standardGaussian := by
  change MemLp id 2 (gaussianReal 0 1)
  exact IsGaussian.memLp_two_id

private lemma olsNoiseGaussianLinear_memLp {r : ℕ} (w : Fin r → ℝ) :
    MemLp (fun e : Fin r → ℝ => ∑ i : Fin r, w i * e i) 2
      (olsNoiseGaussianLaw r) := by
  have hterm (i : Fin r) :
      MemLp (fun e : Fin r → ℝ => w i * e i) 2 (olsNoiseGaussianLaw r) := by
    have hscalar : MemLp (fun z : ℝ => w i * z) 2 standardGaussian :=
      olsStandardGaussian_id_memLp.const_mul (w i)
    simpa [Function.comp_def, olsNoiseGaussianLaw] using
      hscalar.comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin r => standardGaussian) i)
  have hsum : MemLp (∑ i : Fin r, fun e => w i * e i) 2
      (olsNoiseGaussianLaw r) :=
    memLp_finsetSum' Finset.univ (by
      intro i hi
      exact hterm i)
  have hfun : (fun e : Fin r → ℝ => ∑ i : Fin r, w i * e i) =
      (∑ i : Fin r, fun e => w i * e i) := by
    ext e
    simp
  rw [hfun]
  exact hsum

private lemma olsNoiseGaussianLinear_variance {r : ℕ} (w : Fin r → ℝ) :
    variance (fun e : Fin r → ℝ => ∑ i : Fin r, w i * e i)
      (olsNoiseGaussianLaw r) = ∑ i : Fin r, w i ^ 2 := by
  have hfun : (fun e : Fin r → ℝ => ∑ i : Fin r, w i * e i) =
      ∑ i : Fin r, (fun e => w i * e i) := by
    ext e
    simp
  rw [hfun]
  change variance (∑ i : Fin r, (fun e => w i * e i))
      (Measure.pi fun _ : Fin r => standardGaussian) = _
  rw [variance_sum_pi]
  · have hterm (i : Fin r) :
        variance (fun z : ℝ => w i * z) standardGaussian = w i ^ 2 := by
      change variance (fun z : ℝ => w i * id z) standardGaussian = _
      rw [variance_const_mul, variance_id_gaussianReal]
      simp
    exact Finset.sum_congr rfl (fun i hi => hterm i)
  · intro i
    exact olsStandardGaussian_id_memLp.const_mul (w i)

/-- The exact second moment of a deterministic linear statistic of the
actual finite product of standard Gaussian noise coordinates. -/
theorem integral_olsNoiseGaussianLinear_sq {r : ℕ} (w : Fin r → ℝ) :
    (∫ e : Fin r → ℝ, (∑ i : Fin r, w i * e i) ^ 2
      ∂olsNoiseGaussianLaw r) = ∑ i : Fin r, w i ^ 2 := by
  let X : (Fin r → ℝ) → ℝ := fun e => ∑ i : Fin r, w i * e i
  have hmean : (∫ e, X e ∂olsNoiseGaussianLaw r) = 0 := by
    change (∫ e : Fin r → ℝ, ∑ i : Fin r, w i * e i
      ∂olsNoiseGaussianLaw r) = 0
    rw [integral_finsetSum Finset.univ]
    · simp [integral_const_mul, integral_eval, olsNoiseGaussianLaw,
        standardGaussian]
    · intro i hi
      exact (integrable_eval IsGaussian.integrable_id).const_mul _
  calc
    (∫ e, X e ^ 2 ∂olsNoiseGaussianLaw r) =
        variance X (olsNoiseGaussianLaw r) :=
          (variance_of_integral_eq_zero (Measurable.aemeasurable (by fun_prop)) hmean).symm
    _ = ∑ i : Fin r, w i ^ 2 := olsNoiseGaussianLinear_variance w

private lemma olsFixedDesignCenteredSum {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    (∑ i : Fin r, (x i - (∑ j : Fin r, x j) / (r : ℝ))) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hconst :
      (∑ _i : Fin r, (∑ j : Fin r, x j) / (r : ℝ)) =
        (r : ℝ) * ((∑ j : Fin r, x j) / (r : ℝ)) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hrne]
  ring

/-- On a deterministic design, the actual OLS noise predictor is a linear
statistic of the actual noise coordinates with its literal OLS weights. -/
theorem olsNoisePredictor_eq_affine_noise_sum {r : ℕ} (hr : 0 < r)
    (x e : Fin r → ℝ) (u : ℝ) :
    olsNoisePredictor (fun i => (x i, e i)) u =
      ∑ i : Fin r,
        (1 / (r : ℝ) +
          (x i - (∑ j : Fin r, x j) / (r : ℝ)) *
            (u - (∑ j : Fin r, x j) / (r : ℝ)) /
              (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)) * e i := by
  let xb : ℝ := (∑ j : Fin r, x j) / (r : ℝ)
  let sx : ℝ := ∑ j : Fin r, (x j - xb) ^ 2
  let eb : ℝ := (∑ j : Fin r, e j) / (r : ℝ)
  let S : Fin r → ℝ × ℝ := fun i => (x i, e i)
  have hxbar : olsXBar S = xb := by simp [S, olsXBar, xb]
  have hebar : olsEBar S = eb := by simp [S, olsEBar, eb]
  have hdesign : olsCenteredDesign S = sx := by
    simp [S, olsCenteredDesign, olsXBar, xb, sx]
  have hcenter : (∑ i : Fin r, (x i - xb)) = 0 := by
    simpa [xb] using olsFixedDesignCenteredSum hr x
  have hcross : olsCenteredCross S = ∑ i : Fin r, (x i - xb) * e i := by
    rw [olsCenteredCross, hxbar, hebar]
    calc
      (∑ i : Fin r, (x i - xb) * (e i - eb)) =
          ∑ i : Fin r, ((x i - xb) * e i - (x i - xb) * eb) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin r, (x i - xb) * e i) -
          (∑ i : Fin r, (x i - xb)) * eb := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = ∑ i : Fin r, (x i - xb) * e i := by rw [hcenter]; ring
  have hslope : olsNoiseSlope S = (∑ i : Fin r, (x i - xb) * e i) / sx := by
    simp [olsNoiseSlope, hcross, hdesign]
  have hsum :
      (∑ i : Fin r, (1 / (r : ℝ) + ((u - xb) / sx) * (x i - xb)) * e i) =
        (1 / (r : ℝ)) * (∑ i : Fin r, e i) +
          ((u - xb) / sx) * (∑ i : Fin r, (x i - xb) * e i) := by
    calc
      _ = ∑ i : Fin r,
          ((1 / (r : ℝ)) * e i + ((u - xb) / sx) * ((x i - xb) * e i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  unfold olsNoisePredictor
  rw [hebar, hxbar, hslope]
  calc
    eb + ((∑ i : Fin r, (x i - xb) * e i) / sx) * (u - xb) =
        (1 / (r : ℝ)) * (∑ i : Fin r, e i) +
          ((u - xb) / sx) * (∑ i : Fin r, (x i - xb) * e i) := by
            simp [eb]
            ring
    _ = ∑ i : Fin r, (1 / (r : ℝ) + ((u - xb) / sx) * (x i - xb)) * e i :=
          hsum.symm
    _ = ∑ i : Fin r,
        (1 / (r : ℝ) + (x i - xb) * (u - xb) / sx) * e i := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          ring

/-- The sample-mean noise and OLS slope noise have zero covariance under the
actual iid standard Gaussian noise law, by their actual linear weights. -/
theorem olsNoiseMeanSlopeCovariance_eq_zero {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ) :
    covariance
      (fun e : Fin r → ℝ => olsEBar (fun i => (x i, e i)))
      (fun e : Fin r → ℝ => olsNoiseSlope (fun i => (x i, e i)))
      (olsNoiseGaussianLaw r) = 0 := by
  let xb : ℝ := (∑ j : Fin r, x j) / (r : ℝ)
  let sx : ℝ := ∑ j : Fin r, (x j - xb) ^ 2
  let a : Fin r → ℝ := fun _ => 1 / (r : ℝ)
  let b : Fin r → ℝ := fun i => (x i - xb) / sx
  let M : (Fin r → ℝ) → ℝ := fun e => olsEBar (fun i => (x i, e i))
  let Q : (Fin r → ℝ) → ℝ := fun e => olsNoiseSlope (fun i => (x i, e i))
  have hcenter : (∑ i : Fin r, (x i - xb)) = 0 := by
    simpa [xb] using olsFixedDesignCenteredSum hr x
  have hdesign (e : Fin r → ℝ) :
      olsCenteredDesign (fun i => (x i, e i)) = sx := by
    simp [olsCenteredDesign, olsXBar, xb, sx]
  have hcross (e : Fin r → ℝ) :
      olsCenteredCross (fun i => (x i, e i)) =
        ∑ i : Fin r, (x i - xb) * e i := by
    let eb : ℝ := (∑ j : Fin r, e j) / (r : ℝ)
    have hebar : olsEBar (fun i => (x i, e i)) = eb := by
      simp [olsEBar, eb]
    have hxbar : olsXBar (fun i => (x i, e i)) = xb := by
      simp [olsXBar, xb]
    rw [olsCenteredCross, hxbar, hebar]
    calc
      (∑ i : Fin r, (x i - xb) * (e i - eb)) =
          ∑ i : Fin r, ((x i - xb) * e i - (x i - xb) * eb) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin r, (x i - xb) * e i) -
          (∑ i : Fin r, (x i - xb)) * eb := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = ∑ i : Fin r, (x i - xb) * e i := by rw [hcenter]; ring
  have hMfun : M = fun e => ∑ i : Fin r, a i * e i := by
    funext e
    dsimp [M, a]
    simp [olsEBar]
    rw [← Finset.mul_sum]
    ring
  have hQfun : Q = fun e => ∑ i : Fin r, b i * e i := by
    funext e
    dsimp [Q, b]
    rw [olsNoiseSlope, hcross e, hdesign e]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot : (∑ i : Fin r, a i * b i) = 0 := by
    calc
      (∑ i : Fin r, a i * b i) =
          ∑ i : Fin r, ((1 / (r : ℝ)) / sx) * (x i - xb) := by
            dsimp [a, b]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ((1 / (r : ℝ)) / sx) * (∑ i : Fin r, (x i - xb)) := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hcenter]; ring
  have hsq :
      (∑ i : Fin r, (a i + b i) ^ 2) =
        (∑ i : Fin r, a i ^ 2) + (∑ i : Fin r, b i ^ 2) := by
    calc
      (∑ i : Fin r, (a i + b i) ^ 2) =
          (∑ i : Fin r, (a i ^ 2 + 2 * (a i * b i))) +
            (∑ i : Fin r, b i ^ 2) := by
              rw [show (fun i => (a i + b i) ^ 2) =
                fun i => a i ^ 2 + 2 * (a i * b i) + b i ^ 2 by
                  funext i; ring]
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ i : Fin r, a i ^ 2) + 2 * (∑ i : Fin r, a i * b i) +
            (∑ i : Fin r, b i ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hdot]; ring
  have hMmem : MemLp M 2 (olsNoiseGaussianLaw r) := by
    rw [hMfun]
    exact olsNoiseGaussianLinear_memLp a
  have hQmem : MemLp Q 2 (olsNoiseGaussianLaw r) := by
    rw [hQfun]
    exact olsNoiseGaussianLinear_memLp b
  have hsumfun : (fun e => M e + Q e) =
      fun e => ∑ i : Fin r, (a i + b i) * e i := by
    funext e
    rw [hMfun, hQfun]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hvarM : variance M (olsNoiseGaussianLaw r) = ∑ i : Fin r, a i ^ 2 := by
    rw [hMfun]
    exact olsNoiseGaussianLinear_variance a
  have hvarQ : variance Q (olsNoiseGaussianLaw r) = ∑ i : Fin r, b i ^ 2 := by
    rw [hQfun]
    exact olsNoiseGaussianLinear_variance b
  have hvarSum : variance (fun e => M e + Q e) (olsNoiseGaussianLaw r) =
      ∑ i : Fin r, (a i + b i) ^ 2 := by
    rw [hsumfun]
    exact olsNoiseGaussianLinear_variance (fun i => a i + b i)
  have hvariance := variance_add hMmem hQmem
  have hvarSum' : variance (M + Q) (olsNoiseGaussianLaw r) =
      ∑ i : Fin r, (a i + b i) ^ 2 := by
    change variance (fun e => M e + Q e) (olsNoiseGaussianLaw r) = _
    exact hvarSum
  rw [hvarSum', hvarM, hvarQ, hsq] at hvariance
  change covariance M Q (olsNoiseGaussianLaw r) = 0
  linarith

private lemma olsFixedDesignWeightSquareSum {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ) (hs : 0 <
      ∑ i : Fin r, (x i - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2) (u : ℝ) :
    (∑ i : Fin r,
      (1 / (r : ℝ) + (x i - (∑ j : Fin r, x j) / (r : ℝ)) *
        (u - (∑ j : Fin r, x j) / (r : ℝ)) /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)) ^ 2) =
      1 / (r : ℝ) +
        (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
  let xb : ℝ := (∑ j : Fin r, x j) / (r : ℝ)
  let sx : ℝ := ∑ j : Fin r, (x j - xb) ^ 2
  let c : ℝ := 1 / (r : ℝ)
  let d : ℝ := (u - xb) / sx
  have hcenter : (∑ i : Fin r, (x i - xb)) = 0 := by
    simpa [xb] using olsFixedDesignCenteredSum hr x
  have hsumSq : (∑ i : Fin r, (x i - xb) ^ 2) = sx := rfl
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hsx : 0 < sx := by simpa [sx, xb] using hs
  have hsxne : sx ≠ 0 := hsx.ne'
  have hc : (∑ _i : Fin r, c ^ 2) = (r : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hlin : (∑ i : Fin r, 2 * c * d * (x i - xb)) =
      (2 * c * d) * (∑ i : Fin r, (x i - xb)) := by
    rw [Finset.mul_sum]
  have hquad : (∑ i : Fin r, d ^ 2 * (x i - xb) ^ 2) =
      d ^ 2 * (∑ i : Fin r, (x i - xb) ^ 2) := by
    rw [Finset.mul_sum]
  calc
    (∑ i : Fin r,
      (1 / (r : ℝ) + (x i - (∑ j : Fin r, x j) / (r : ℝ)) *
        (u - (∑ j : Fin r, x j) / (r : ℝ)) /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)) ^ 2) =
        ∑ i : Fin r, (c + d * (x i - xb)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [c, d, xb, sx]
          ring
    _ =
        (∑ _i : Fin r, c ^ 2) +
          (∑ i : Fin r, 2 * c * d * (x i - xb)) +
          (∑ i : Fin r, d ^ 2 * (x i - xb) ^ 2) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (r : ℝ) * c ^ 2 + (2 * c * d) * (∑ i : Fin r, (x i - xb)) +
          d ^ 2 * (∑ i : Fin r, (x i - xb) ^ 2) := by rw [hc, hlin, hquad]
    _ = 1 / (r : ℝ) + (u - xb) ^ 2 / sx := by
          rw [hcenter, hsumSq]
          simp only [mul_zero, add_zero]
          simp only [c, d]
          field_simp [hrne, hsxne]
    _ = 1 / (r : ℝ) + (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
          dsimp [xb, sx]

/-- Conditional on any fixed valid deterministic design and test point, the
actual OLS noise predictor has its exact fixed-test second moment. -/
theorem olsNoisePredictor_fixedTest_secondMoment {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ) (u : ℝ)
    (hs : 0 < ∑ i : Fin r,
      (x i - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2) :
    (∫ e : Fin r → ℝ,
      (olsNoisePredictor (fun i => (x i, e i)) u) ^ 2
        ∂olsNoiseGaussianLaw r) =
      1 / (r : ℝ) +
        (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
  let w : Fin r → ℝ := fun i =>
    1 / (r : ℝ) +
      (x i - (∑ j : Fin r, x j) / (r : ℝ)) *
        (u - (∑ j : Fin r, x j) / (r : ℝ)) /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)
  have hrep : ∀ e : Fin r → ℝ,
      olsNoisePredictor (fun i => (x i, e i)) u = ∑ i : Fin r, w i * e i := by
    intro e
    rw [olsNoisePredictor_eq_affine_noise_sum hr x e u]
  calc
    (∫ e : Fin r → ℝ,
      (olsNoisePredictor (fun i => (x i, e i)) u) ^ 2
        ∂olsNoiseGaussianLaw r) =
        ∫ e : Fin r → ℝ, (∑ i : Fin r, w i * e i) ^ 2
          ∂olsNoiseGaussianLaw r := by
            apply integral_congr_ae
            exact ae_of_all _ fun e =>
              congrArg (fun z : ℝ => z ^ 2) (hrep e)
    _ = ∑ i : Fin r, w i ^ 2 := integral_olsNoiseGaussianLinear_sq w
    _ = 1 / (r : ℝ) +
        (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
            simpa [w] using olsFixedDesignWeightSquareSum hr x hs u

private lemma olsStandardGaussian_shiftSq_integral {c : ℝ} :
    (∫ u : ℝ, (u - c) ^ 2 ∂standardGaussian) = 1 + c ^ 2 := by
  have hmean : (∫ u : ℝ, u ∂standardGaussian) = 0 := by
    simp [standardGaussian]
  have hsecond : (∫ u : ℝ, u ^ 2 ∂standardGaussian) = 1 := by
    calc
      (∫ u : ℝ, u ^ 2 ∂standardGaussian) =
          variance (fun u : ℝ => u) standardGaussian := by
            symm
            exact variance_of_integral_eq_zero (Measurable.aemeasurable measurable_id') hmean
      _ = 1 := by simp [standardGaussian]
  have hIdLp : MemLp id 2 standardGaussian :=
    olsStandardGaussian_id_memLp
  have hId : Integrable (fun u : ℝ => u ^ 2) standardGaussian :=
    hIdLp.integrable_sq
  have hconstLp : MemLp (fun _ : ℝ => c) 2 standardGaussian := memLp_const c
  have hshiftLp : MemLp (fun u : ℝ => u - c) 2 standardGaussian := by
    exact hIdLp.sub hconstLp
  have _hshiftInt : Integrable (fun u : ℝ => (u - c) ^ 2) standardGaussian :=
    hshiftLp.integrable_sq
  have hMul : Integrable (fun u : ℝ => (2 * c) * u) standardGaussian :=
    IsGaussian.integrable_id.const_mul _
  calc
    (∫ u : ℝ, (u - c) ^ 2 ∂standardGaussian) =
        ∫ u : ℝ, (u ^ 2 - (2 * c) * u) + c ^ 2 ∂standardGaussian := by
          apply integral_congr_ae
          exact ae_of_all _ fun u => by ring
    _ = (∫ u : ℝ, u ^ 2 ∂standardGaussian) -
        (∫ u : ℝ, (2 * c) * u ∂standardGaussian) + c ^ 2 := by
          calc
            (∫ u : ℝ, (u ^ 2 - (2 * c) * u) + c ^ 2 ∂standardGaussian) =
                (∫ u : ℝ, u ^ 2 - (2 * c) * u ∂standardGaussian) +
                  (∫ _ : ℝ, c ^ 2 ∂standardGaussian) :=
                    integral_add (hId.sub hMul) (integrable_const _)
            _ = (∫ u : ℝ, u ^ 2 ∂standardGaussian) -
                (∫ u : ℝ, (2 * c) * u ∂standardGaussian) + c ^ 2 := by
                  rw [integral_sub hId hMul, integral_const_mul, integral_const]
                  simp [standardGaussian]
    _ = 1 + c ^ 2 := by
          rw [integral_const_mul, hmean, hsecond]
          ring

/-- The actual predictor square is integrable under the independent product
law of the test covariate and all Gaussian noise coordinates. -/
theorem olsNoisePredictor_sq_integrable_product {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ)
    (hs : 0 < ∑ i : Fin r,
      (x i - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2) :
    Integrable
      (fun p : ℝ × (Fin r → ℝ) =>
        (olsNoisePredictor (fun i => (x i, p.2 i)) p.1) ^ 2)
      (standardGaussian.prod (olsNoiseGaussianLaw r)) := by
  let f : ℝ × (Fin r → ℝ) → ℝ := fun p =>
    (olsNoisePredictor (fun i => (x i, p.2 i)) p.1) ^ 2
  have hmeas : AEStronglyMeasurable f
      (standardGaussian.prod (olsNoiseGaussianLaw r)) := by
    dsimp only [f]
    have hm : Measurable (fun p : ℝ × (Fin r → ℝ) =>
        (olsNoisePredictor (fun i => (x i, p.2 i)) p.1) ^ 2) := by
      fun_prop [olsNoisePredictor, olsEBar, olsNoiseSlope, olsCenteredCross,
        olsCenteredDesign, olsXBar]
    exact hm.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with u
    let w : Fin r → ℝ := fun i =>
      1 / (r : ℝ) +
        (x i - (∑ j : Fin r, x j) / (r : ℝ)) *
          (u - (∑ j : Fin r, x j) / (r : ℝ)) /
            (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)
    have hrep : ∀ e : Fin r → ℝ,
        f (u, e) = (∑ i : Fin r, w i * e i) ^ 2 := by
      intro e
      dsimp only [f]
      rw [olsNoisePredictor_eq_affine_noise_sum hr x e u]
    have hlin := olsNoiseGaussianLinear_memLp w
    have hsq : Integrable (fun e : Fin r → ℝ => (∑ i : Fin r, w i * e i) ^ 2)
        (olsNoiseGaussianLaw r) := hlin.integrable_sq
    have hfun : (fun e : Fin r → ℝ => f (u, e)) =
        (fun e => (∑ i : Fin r, w i * e i) ^ 2) := funext hrep
    rw [hfun]
    exact hsq
  · have hshift : Integrable (fun u : ℝ =>
        (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2) standardGaussian := by
      have hIdLp : MemLp id 2 standardGaussian :=
        olsStandardGaussian_id_memLp
      have hconstLp : MemLp
          (fun _ : ℝ => (∑ j : Fin r, x j) / (r : ℝ)) 2 standardGaussian :=
        memLp_const _
      have hshiftLp : MemLp
          (fun u : ℝ => u - (∑ j : Fin r, x j) / (r : ℝ)) 2 standardGaussian :=
        hIdLp.sub hconstLp
      exact hshiftLp.integrable_sq
    have hq : Integrable (fun u : ℝ =>
        1 / (r : ℝ) +
          (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
            (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2))
        standardGaussian := by
      have hmul := hshift.const_mul
        ((∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2)⁻¹)
      have hconst : Integrable (fun _ : ℝ => (1 / (r : ℝ))) standardGaussian :=
        integrable_const _
      simpa [div_eq_mul_inv, mul_comm] using hconst.add hmul
    have hinner : ∀ u : ℝ,
        (∫ e : Fin r → ℝ, ‖f (u, e)‖ ∂olsNoiseGaussianLaw r) =
          1 / (r : ℝ) +
            (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
              (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
      intro u
      calc
        (∫ e : Fin r → ℝ, ‖f (u, e)‖ ∂olsNoiseGaussianLaw r) =
            ∫ e : Fin r → ℝ,
              (olsNoisePredictor (fun i => (x i, e i)) u) ^ 2
                ∂olsNoiseGaussianLaw r := by
                  apply integral_congr_ae
                  exact ae_of_all _ fun e => by
                    simp [f, Real.norm_eq_abs]
        _ = _ := olsNoisePredictor_fixedTest_secondMoment hr x u hs
    have hinnerFun :
        (fun u : ℝ => ∫ e : Fin r → ℝ, ‖f (u, e)‖ ∂olsNoiseGaussianLaw r) =
          fun u => 1 / (r : ℝ) +
            (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
              (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) :=
      funext hinner
    rw [hinnerFun]
    exact hq

/-- Averaging over an independent standard Gaussian test covariate gives the
deterministic-design contribution to the OLS mean squared prediction error. -/
theorem olsNoisePredictor_independentTest_secondMoment {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ)
    (hs : 0 < ∑ i : Fin r,
      (x i - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2) :
    (∫ p : ℝ × (Fin r → ℝ),
      (olsNoisePredictor (fun i => (x i, p.2 i)) p.1) ^ 2
        ∂(standardGaussian.prod (olsNoiseGaussianLaw r))) =
      1 / (r : ℝ) +
        (1 + ((∑ j : Fin r, x j) / (r : ℝ)) ^ 2) /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
  let f : ℝ × (Fin r → ℝ) → ℝ := fun p =>
    (olsNoisePredictor (fun i => (x i, p.2 i)) p.1) ^ 2
  have hf := olsNoisePredictor_sq_integrable_product hr x hs
  calc
    (∫ p : ℝ × (Fin r → ℝ), f p
        ∂(standardGaussian.prod (olsNoiseGaussianLaw r))) =
        ∫ u : ℝ, ∫ e : Fin r → ℝ, f (u, e) ∂olsNoiseGaussianLaw r
          ∂standardGaussian := integral_prod f hf
    _ = ∫ u : ℝ,
        (1 / (r : ℝ) +
          (u - (∑ j : Fin r, x j) / (r : ℝ)) ^ 2 /
            (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2))
          ∂standardGaussian := by
            apply integral_congr_ae
            exact ae_of_all _ fun u => by
              simpa [f] using olsNoisePredictor_fixedTest_secondMoment hr x u hs
    _ = 1 / (r : ℝ) +
        (1 + ((∑ j : Fin r, x j) / (r : ℝ)) ^ 2) /
          (∑ j : Fin r, (x j - (∑ k : Fin r, x k) / (r : ℝ)) ^ 2) := by
          let xb : ℝ := (∑ j : Fin r, x j) / (r : ℝ)
          let sx : ℝ := ∑ j : Fin r, (x j - xb) ^ 2
          have hshift := olsStandardGaussian_shiftSq_integral (c := xb)
          have hshiftInt : Integrable (fun u : ℝ => (u - xb) ^ 2) standardGaussian := by
            have hIdLp : MemLp id 2 standardGaussian := by
              exact olsStandardGaussian_id_memLp
            have hconstLp : MemLp (fun _ : ℝ => xb) 2 standardGaussian :=
              memLp_const _
            have hshiftLp : MemLp (fun u : ℝ => u - xb) 2 standardGaussian := by
              exact hIdLp.sub hconstLp
            exact hshiftLp.integrable_sq
          have hconstant : Integrable (fun _ : ℝ => (1 / (r : ℝ))) standardGaussian :=
            integrable_const _
          have hscaled : Integrable
              (fun u : ℝ => (sx⁻¹) * (u - xb) ^ 2) standardGaussian :=
            hshiftInt.const_mul _
          rw [show (fun u : ℝ => 1 / (r : ℝ) + (u - xb) ^ 2 / sx) =
              fun u => (1 / (r : ℝ)) + (sx⁻¹) * (u - xb) ^ 2 by
                funext u; simp [div_eq_mul_inv, mul_comm]]
          rw [integral_add hconstant hscaled, integral_const, integral_const_mul, hshift]
          simp [standardGaussian, xb, sx]
          ring

#print axioms integral_olsNoiseGaussianLinear_sq
#print axioms olsNoisePredictor_eq_affine_noise_sum
#print axioms olsNoiseMeanSlopeCovariance_eq_zero
#print axioms olsNoisePredictor_fixedTest_secondMoment
#print axioms olsNoisePredictor_sq_integrable_product
#print axioms olsNoisePredictor_independentTest_secondMoment

end LOOConcentration
