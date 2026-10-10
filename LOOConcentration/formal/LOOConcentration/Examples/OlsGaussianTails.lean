import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.GaussianSquareMGF
import LOOConcentration.Examples.GaussianCenteredDesign
import LOOConcentration.Examples.OlsDesign

set_option autoImplicit false

open MeasureTheory
open ProbabilityTheory
open scoped NNReal

namespace LOOConcentration

/-- The actual iid pair law for `N` observations. -/
noncomputable abbrev olsPairGaussianLaw (N : ℕ) : Measure (Fin N → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin N => standardGaussian.prod standardGaussian)

private def pairNormSq (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

private lemma integrable_exp_pairNormSq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℝ × ℝ => Real.exp (t * pairNormSq z))
      (standardGaussian.prod standardGaussian) := by
  have h := (integrable_exp_sq_standardGaussian ht).mul_prod
    (integrable_exp_sq_standardGaussian ht)
  convert h using 1
  funext z
  change Real.exp (t * (z.1 ^ 2 + z.2 ^ 2)) = _
  rw [← Real.exp_add]
  congr 1
  ring

private lemma integral_exp_pairNormSq {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : ℝ × ℝ, Real.exp (t * pairNormSq z)
      ∂(standardGaussian.prod standardGaussian)) =
      (1 - 2 * t)⁻¹ := by
  have hq : 0 < 1 - 2 * t := by linarith
  calc
    _ = ∫ z : ℝ × ℝ,
        Real.exp (t * z.1 ^ 2) * Real.exp (t * z.2 ^ 2)
          ∂(standardGaussian.prod standardGaussian) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change Real.exp (t * (z.1 ^ 2 + z.2 ^ 2)) =
          Real.exp (t * z.1 ^ 2) * Real.exp (t * z.2 ^ 2)
        rw [← Real.exp_add]
        congr 1
        ring
    _ = (∫ x : ℝ, Real.exp (t * x ^ 2) ∂standardGaussian) ^ 2 := by
      rw [integral_prod_mul (f := fun x : ℝ => Real.exp (t * x ^ 2))
        (g := fun x : ℝ => Real.exp (t * x ^ 2))]
      ring
    _ = (1 - 2 * t)⁻¹ := by
      rw [integral_exp_sq_standardGaussian ht]
      calc
        (1 / Real.sqrt (1 - 2 * t)) ^ 2 = 1 / (1 - 2 * t) := by
          rw [div_pow, Real.sq_sqrt hq.le]
          norm_num
        _ = (1 - 2 * t)⁻¹ := by rw [one_div]

private lemma rpow_neg_nat (q : ℝ) (hq : 0 < q) (N : ℕ) :
    q ^ (-(N : ℝ)) = (q⁻¹) ^ N := by
  calc
    q ^ (-(N : ℝ)) = (q ^ (N : ℝ))⁻¹ := Real.rpow_neg hq.le _
    _ = (q ^ N)⁻¹ := by rw [Real.rpow_natCast]
    _ = (q⁻¹) ^ N := by rw [inv_pow]

/-- The actual full Euclidean squared statistic has a finite MGF throughout
the Gaussian quadratic domain. -/
theorem integrable_exp_olsNoiseNormSq {N : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun G : Fin N → ℝ × ℝ => Real.exp (t * olsNoiseNormSq G))
      (olsPairGaussianLaw N) := by
  have hprod : Integrable
      (fun G : Fin N → ℝ × ℝ =>
        ∏ i : Fin N, Real.exp (t * pairNormSq (G i)))
      (Measure.pi fun _ : Fin N => standardGaussian.prod standardGaussian) :=
    Integrable.fintype_prod fun _ => integrable_exp_pairNormSq ht
  convert hprod using 1
  funext G
  rw [olsNoiseNormSq, Finset.mul_sum, Real.exp_sum]
  rfl

/-- Exact MGF of the actual full OLS noise norm squared. -/
theorem integral_exp_olsNoiseNormSq {N : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    (∫ G : Fin N → ℝ × ℝ, Real.exp (t * olsNoiseNormSq G)
      ∂olsPairGaussianLaw N) =
      (1 - 2 * t) ^ (-(N : ℝ)) := by
  have hq : 0 < 1 - 2 * t := by linarith
  have hfactor : ∀ G : Fin N → ℝ × ℝ,
      Real.exp (t * olsNoiseNormSq G) =
        ∏ i : Fin N, Real.exp (t * pairNormSq (G i)) := by
    intro G
    rw [olsNoiseNormSq, Finset.mul_sum, Real.exp_sum]
    rfl
  calc
    _ = ∫ G : Fin N → ℝ × ℝ,
        ∏ i : Fin N, Real.exp (t * pairNormSq (G i))
          ∂(Measure.pi fun _ : Fin N => standardGaussian.prod standardGaussian) := by
      apply integral_congr_ae
      exact ae_of_all _ hfactor
    _ = ∏ i : Fin N,
        ∫ z : ℝ × ℝ, Real.exp (t * pairNormSq z)
          ∂(standardGaussian.prod standardGaussian) := by
      simpa only [standardGaussian] using
        (integral_fintype_prod_eq_prod
          (f := fun _ : Fin N => fun z : ℝ × ℝ => Real.exp (t * pairNormSq z))
          (μ := fun _ : Fin N => standardGaussian.prod standardGaussian))
    _ = ((1 - 2 * t)⁻¹) ^ N := by
      simp_rw [integral_exp_pairNormSq ht]
      simp
    _ = (1 - 2 * t) ^ (-(N : ℝ)) := by
      rw [rpow_neg_nat (1 - 2 * t) hq N]

/-- Exact MGF transport for the actual centered-design statistic, including
negative parameters. The exponent is the residual dimension `r = N - 1`. -/
theorem integrable_exp_olsCenteredDesign {r : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun G : Fin (r + 1) → ℝ × ℝ =>
      Real.exp (t * olsCenteredDesign G)) (olsPairGaussianLaw (r + 1)) := by
  let μ := olsPairGaussianLaw (r + 1)
  let ν := Measure.pi (fun _ : Fin r => standardGaussian)
  let qsum : (Fin r → ℝ) → ℝ := fun x => ∑ i : Fin r, (x i) ^ 2
  have hdesign : Measure.map olsCenteredDesign μ =
      ν.map qsum := by
    simpa [μ, ν, qsum, standardGaussian] using
      (olsCenteredDesign_gaussian_pushforward r)
  have hqsum : Integrable (fun y : ℝ => Real.exp (t * y)) (ν.map qsum) := by
    have hbase : Integrable (fun x : Fin r → ℝ => Real.exp (t * qsum x)) ν := by
      simpa [ν, qsum, standardGaussianSqSum] using
        integrable_exp_sqSum_standardGaussian_pi (r := r) ht
    exact (integrable_map_measure (by fun_prop)
      (by fun_prop : Measurable qsum).aemeasurable).mpr
        hbase
  have hstat : Integrable (fun y : ℝ => Real.exp (t * y))
      (Measure.map olsCenteredDesign μ) := hdesign ▸ hqsum
  exact (integrable_map_measure (by fun_prop)
    (measurable_olsCenteredDesign.aemeasurable)).mp hstat

/-- Exact MGF of the actual centered design statistic for all `t < 1/2`;
the value is the chi-square-shaped formula but no named-law claim is made. -/
theorem integral_exp_olsCenteredDesign {r : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    (∫ G : Fin (r + 1) → ℝ × ℝ,
      Real.exp (t * olsCenteredDesign G) ∂olsPairGaussianLaw (r + 1)) =
      (1 - 2 * t) ^ (-(r : ℝ) / 2) := by
  let μ := olsPairGaussianLaw (r + 1)
  let ν := Measure.pi (fun _ : Fin r => standardGaussian)
  let qsum : (Fin r → ℝ) → ℝ := fun x => ∑ i : Fin r, (x i) ^ 2
  have hdesign : Measure.map olsCenteredDesign μ = ν.map qsum := by
    simpa [μ, ν, qsum, standardGaussian] using
      (olsCenteredDesign_gaussian_pushforward r)
  calc
    _ = ∫ y : ℝ, Real.exp (t * y) ∂Measure.map olsCenteredDesign μ := by
      symm
      exact integral_map measurable_olsCenteredDesign.aemeasurable (by fun_prop)
    _ = ∫ y : ℝ, Real.exp (t * y) ∂ν.map qsum := by rw [hdesign]
    _ = ∫ x : Fin r → ℝ, Real.exp (t * qsum x) ∂ν := by
      exact integral_map (by fun_prop : Measurable qsum).aemeasurable (by fun_prop)
    _ = (1 - 2 * t) ^ (-(r : ℝ) / 2) := by
      simpa [ν, qsum, standardGaussianSqSum, standardGaussian] using
        integral_exp_sqSum_standardGaussian_pi (r := r) ht

/-- Exponential-Markov bound for the upper tail of the actual full noise norm.
The right side is the exact Chernoff expression at parameter `1/4`. -/
theorem measure_olsNoiseNormSq_gt {N : ℕ} :
    olsPairGaussianLaw N {G | 9 * (N : ℝ) < olsNoiseNormSq G} ≤
      ENNReal.ofReal (Real.exp (-(9 * (N : ℝ)) / 4) *
        (1 - 2 * (1 / 4 : ℝ)) ^ (-(N : ℝ))) := by
  let μ := olsPairGaussianLaw N
  let f : (Fin N → ℝ × ℝ) → ℝ := fun G =>
    Real.exp ((1 / 4 : ℝ) * (olsNoiseNormSq G - 9 * (N : ℝ)))
  let c : ℝ := Real.exp (-(9 * (N : ℝ)) / 4)
  have hpoint : ∀ G, f G = c * Real.exp ((1 / 4 : ℝ) * olsNoiseNormSq G) := by
    intro G
    dsimp [f, c]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : Integrable f μ := by
    have h := (integrable_exp_olsNoiseNormSq
      (N := N) (t := (1 / 4 : ℝ)) (by norm_num)).const_mul c
    convert h using 1
    funext G
    exact hpoint G
  have hnonneg : 0 ≤ᵐ[μ] f := ae_of_all μ fun G => by
    simp only [f]
    exact (Real.exp_pos _).le
  have hmarkov : μ {G | 9 * (N : ℝ) < olsNoiseNormSq G} ≤
      ENNReal.ofReal (∫ G, f G ∂μ) := by
    apply hf.measure_le_integral hnonneg
    intro G hG
    change 9 * (N : ℝ) < olsNoiseNormSq G at hG
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (le_of_lt hG))
  have hint : (∫ G, f G ∂μ) = c *
      (1 - 2 * (1 / 4 : ℝ)) ^ (-(N : ℝ)) := by
    calc
      _ = ∫ G, c * Real.exp ((1 / 4 : ℝ) * olsNoiseNormSq G) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ hpoint
      _ = c * ∫ G, Real.exp ((1 / 4 : ℝ) * olsNoiseNormSq G) ∂μ := by
        rw [integral_const_mul]
      _ = _ := by rw [integral_exp_olsNoiseNormSq (by norm_num)]
  calc
    μ {G | 9 * (N : ℝ) < olsNoiseNormSq G} ≤
        ENNReal.ofReal (∫ G, f G ∂μ) := hmarkov
    _ = ENNReal.ofReal (c *
        (1 - 2 * (1 / 4 : ℝ)) ^ (-(N : ℝ))) := by rw [hint]
    _ = _ := rfl

/-- Exponential-Markov bound for the lower tail of the actual centered design
statistic, using the negative parameter `-1/2`. -/
theorem measure_olsCenteredDesign_lt {r : ℕ} :
    olsPairGaussianLaw (r + 1)
      {G | olsCenteredDesign G < ((r + 1 : ℕ) : ℝ) / 2} ≤
      ENNReal.ofReal (Real.exp (((r + 1 : ℕ) : ℝ) / 4) *
        (1 - 2 * (-1 / 2 : ℝ)) ^ (-(r : ℝ) / 2)) := by
  let μ := olsPairGaussianLaw (r + 1)
  let f : (Fin (r + 1) → ℝ × ℝ) → ℝ := fun G =>
    Real.exp ((-1 / 2 : ℝ) *
      (olsCenteredDesign G - ((r + 1 : ℕ) : ℝ) / 2))
  let c : ℝ := Real.exp (((r + 1 : ℕ) : ℝ) / 4)
  have hpoint : ∀ G, f G = c *
      Real.exp ((-1 / 2 : ℝ) * olsCenteredDesign G) := by
    intro G
    dsimp [f, c]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : Integrable f μ := by
    have h := (integrable_exp_olsCenteredDesign
      (r := r) (t := (-1 / 2 : ℝ)) (by norm_num)).const_mul c
    convert h using 1
    funext G
    exact hpoint G
  have hnonneg : 0 ≤ᵐ[μ] f := ae_of_all μ fun G => by
    simp only [f]
    exact (Real.exp_pos _).le
  have hmarkov : μ {G | olsCenteredDesign G < ((r + 1 : ℕ) : ℝ) / 2} ≤
      ENNReal.ofReal (∫ G, f G ∂μ) := by
    apply hf.measure_le_integral hnonneg
    intro G hG
    change olsCenteredDesign G < ((r + 1 : ℕ) : ℝ) / 2 at hG
    rw [Real.one_le_exp_iff]
    have hgap : 0 < ((r + 1 : ℕ) : ℝ) / 2 - olsCenteredDesign G := by linarith
    nlinarith
  have hint : (∫ G, f G ∂μ) = c *
      (1 - 2 * (-1 / 2 : ℝ)) ^ (-(r : ℝ) / 2) := by
    calc
      _ = ∫ G, c * Real.exp ((-1 / 2 : ℝ) * olsCenteredDesign G) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ hpoint
      _ = c * ∫ G, Real.exp ((-1 / 2 : ℝ) * olsCenteredDesign G) ∂μ := by
        rw [integral_const_mul]
      _ = _ := by rw [integral_exp_olsCenteredDesign (by norm_num)]
  calc
    μ {G | olsCenteredDesign G < ((r + 1 : ℕ) : ℝ) / 2} ≤
        ENNReal.ofReal (∫ G, f G ∂μ) := hmarkov
    _ = ENNReal.ofReal (c *
        (1 - 2 * (-1 / 2 : ℝ)) ^ (-(r : ℝ) / 2)) := by rw [hint]
    _ = _ := rfl

private lemma integral_exp_mul_standardGaussian (t : ℝ) :
    (∫ x : ℝ, Real.exp (t * x) ∂standardGaussian) = Real.exp (t ^ 2 / 2) := by
  have h := congrFun
    (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))) t
  simpa [ProbabilityTheory.mgf, standardGaussian, average_eq_integral] using h

private theorem measure_standardGaussian_gt {b : ℝ} (hb : 0 ≤ b) :
    standardGaussian {x | b < x} ≤ ENNReal.ofReal (Real.exp (-(b ^ 2) / 2)) := by
  let f : ℝ → ℝ := fun x => Real.exp (b * (x - b))
  let c : ℝ := Real.exp (-(b ^ 2))
  have hpoint : ∀ x, f x = c * Real.exp (b * x) := by
    intro x
    dsimp [f, c]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : Integrable f standardGaussian := by
    have h := (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0)
      (v := (1 : ℝ≥0)) b).const_mul c
    convert h using 1
    funext x
    exact hpoint x
  have hnonneg : 0 ≤ᵐ[standardGaussian] f := ae_of_all _ fun x => by
    simp only [f]
    exact (Real.exp_pos _).le
  have hmarkov : standardGaussian {x | b < x} ≤
      ENNReal.ofReal (∫ x, f x ∂standardGaussian) := by
    apply hf.measure_le_integral hnonneg
    intro x hx
    change b < x at hx
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hb (sub_nonneg.mpr (le_of_lt hx))
  have hint : (∫ x, f x ∂standardGaussian) =
      Real.exp (-(b ^ 2) / 2) := by
    calc
      _ = c * ∫ x, Real.exp (b * x) ∂standardGaussian := by
        calc
          _ = ∫ x, c * Real.exp (b * x) ∂standardGaussian := by
            apply integral_congr_ae
            exact ae_of_all _ hpoint
          _ = _ := by rw [integral_const_mul]
      _ = c * Real.exp (b ^ 2 / 2) := by
        rw [integral_exp_mul_standardGaussian]
      _ = _ := by
        dsimp [c]
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    standardGaussian {x | b < x} ≤ ENNReal.ofReal (∫ x, f x ∂standardGaussian) := hmarkov
    _ = ENNReal.ofReal (Real.exp (-(b ^ 2) / 2)) := by rw [hint]

private theorem measure_standardGaussian_lt_neg {b : ℝ} (hb : 0 ≤ b) :
    standardGaussian {x | x < -b} ≤ ENNReal.ofReal (Real.exp (-(b ^ 2) / 2)) := by
  let f : ℝ → ℝ := fun x => Real.exp ((-b) * (x + b))
  let c : ℝ := Real.exp (-(b ^ 2))
  have hpoint : ∀ x, f x = c * Real.exp ((-b) * x) := by
    intro x
    dsimp [f, c]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : Integrable f standardGaussian := by
    have h := (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0)
      (v := (1 : ℝ≥0)) (-b)).const_mul c
    convert h using 1
    funext x
    exact hpoint x
  have hnonneg : 0 ≤ᵐ[standardGaussian] f := ae_of_all _ fun x => by
    simp only [f]
    exact (Real.exp_pos _).le
  have hmarkov : standardGaussian {x | x < -b} ≤
      ENNReal.ofReal (∫ x, f x ∂standardGaussian) := by
    apply hf.measure_le_integral hnonneg
    intro x hx
    change x < -b at hx
    rw [Real.one_le_exp_iff]
    have hsum : x + b < 0 := by linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show -b ≤ 0 by linarith)
      (show x + b ≤ 0 by linarith)]
  have hint : (∫ x, f x ∂standardGaussian) =
      Real.exp (-(b ^ 2) / 2) := by
    calc
      _ = c * ∫ x, Real.exp ((-b) * x) ∂standardGaussian := by
        calc
          _ = ∫ x, c * Real.exp ((-b) * x) ∂standardGaussian := by
            apply integral_congr_ae
            exact ae_of_all _ hpoint
          _ = _ := by rw [integral_const_mul]
      _ = c * Real.exp ((-b) ^ 2 / 2) := by
        rw [integral_exp_mul_standardGaussian]
      _ = _ := by
        dsimp [c]
        rw [← Real.exp_add]
        congr 1
        ring_nf
  calc
    standardGaussian {x | x < -b} ≤ ENNReal.ofReal (∫ x, f x ∂standardGaussian) := hmarkov
    _ = ENNReal.ofReal (Real.exp (-(b ^ 2) / 2)) := by rw [hint]

private theorem measure_standardGaussian_sq_gt {a : ℝ} (ha : 0 ≤ a) :
    standardGaussian {x | a < x ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-a / 2)) := by
  let b : ℝ := Real.sqrt a
  have hb : 0 ≤ b := Real.sqrt_nonneg a
  have hsubset : {x : ℝ | a < x ^ 2} ⊆
      {x | b < x} ∪ {x | x < -b} := by
    intro x hx
    change a < x ^ 2 at hx
    have hsq : b ^ 2 < x ^ 2 := by
      dsimp [b]
      rw [Real.sq_sqrt ha]
      exact hx
    have hroot : Real.sqrt (b ^ 2) < |x| := by
      have hsqabs : b ^ 2 < |x| ^ 2 := by simpa [sq_abs] using hsq
      exact (Real.sqrt_lt (sq_nonneg b) (abs_nonneg x)).2 hsqabs
    rw [Real.sqrt_sq hb] at hroot
    by_cases hxsign : 0 ≤ x
    · left
      simpa [abs_of_nonneg hxsign] using hroot
    · right
      have hxneg : x < 0 := lt_of_not_ge hxsign
      rw [abs_of_neg hxneg] at hroot
      simpa using (neg_lt_neg hroot)
  have hpos := measure_standardGaussian_gt hb
  have hneg := measure_standardGaussian_lt_neg hb
  have hsquare : b ^ 2 = a := Real.sq_sqrt ha
  calc
    standardGaussian {x | a < x ^ 2} ≤
        standardGaussian ({x | b < x} ∪ {x | x < -b}) := measure_mono hsubset
    _ ≤ standardGaussian {x | b < x} + standardGaussian {x | x < -b} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-a / 2)) +
        ENNReal.ofReal (Real.exp (-a / 2)) := by
      exact add_le_add (by simpa [hsquare] using hpos) (by simpa [hsquare] using hneg)
    _ = ENNReal.ofReal (2 * Real.exp (-a / 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1
      ring

/-- Coordinate square tail under the actual iid pair law. -/
theorem measure_olsCovariateCoordinateSq_gt {N : ℕ} (i : Fin N) :
    olsPairGaussianLaw N {G | (N : ℝ) / 64 < (G i).1 ^ 2} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / 128)) := by
  let μs := fun _ : Fin N => standardGaussian.prod standardGaussian
  have heval := measurePreserving_eval μs i
  have hfst := measurePreserving_fst
    (μ := standardGaussian) (ν := standardGaussian)
  have hmp : MeasurePreserving (fun G : Fin N → ℝ × ℝ => (G i).1)
      (olsPairGaussianLaw N) standardGaussian := by
    simpa [Function.comp_def, Function.eval_apply, olsPairGaussianLaw, μs] using
      hfst.comp heval
  have hset : MeasurableSet {x : ℝ | (N : ℝ) / 64 < x ^ 2} := by
    exact measurableSet_lt measurable_const (measurable_id.pow_const 2)
  have hmap := hmp.measure_preimage (s := {x : ℝ | (N : ℝ) / 64 < x ^ 2})
    hset.nullMeasurableSet
  have hactual : olsPairGaussianLaw N {G | (N : ℝ) / 64 < (G i).1 ^ 2} =
      standardGaussian {x | (N : ℝ) / 64 < x ^ 2} := by
    simpa [Function.comp_def] using hmap
  have hstd := measure_standardGaussian_sq_gt (a := (N : ℝ) / 64) (by positivity)
  have hscale : -(N : ℝ) / 128 = -((N : ℝ) / 64) / 2 := by ring
  rw [hactual]
  simpa [hscale] using hstd

/-- Finite union bound for all actual covariate coordinates. -/
theorem measure_olsCovariateCoordinateSq_bad {N : ℕ} :
    olsPairGaussianLaw N {G | ∃ i : Fin N, (N : ℝ) / 64 < (G i).1 ^ 2} ≤
      ENNReal.ofReal (2 * (N : ℝ) * Real.exp (-(N : ℝ) / 128)) := by
  let μ := olsPairGaussianLaw N
  let s : Fin N → Set (Fin N → ℝ × ℝ) := fun i =>
    {G | (N : ℝ) / 64 < (G i).1 ^ 2}
  have hunion : {G : Fin N → ℝ × ℝ | ∃ i : Fin N, (N : ℝ) / 64 < (G i).1 ^ 2} =
      ⋃ i : Fin N, s i := by
    ext G
    simp [s]
  have hsum : ∑ i : Fin N, μ (s i) ≤
      ∑ i : Fin N, ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / 128)) :=
    Finset.sum_le_sum fun i _ => measure_olsCovariateCoordinateSq_gt i
  calc
    μ {G | ∃ i : Fin N, (N : ℝ) / 64 < (G i).1 ^ 2} = μ (⋃ i : Fin N, s i) := by
      rw [hunion]
    _ ≤ ∑ i : Fin N, μ (s i) := measure_iUnion_fintype_le μ s
    _ ≤ ∑ i : Fin N, ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / 128)) := hsum
    _ = ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(N : ℝ) / 128))) := by
      simp [Finset.sum_const, Fintype.card_fin, ENNReal.ofReal_mul]
    _ = ENNReal.ofReal (2 * (N : ℝ) * Real.exp (-(N : ℝ) / 128)) := by
      congr 1
      ring

private lemma rawTailRate {N : ℕ} :
    Real.exp (-(9 * (N : ℝ)) / 4) *
        (1 - 2 * (1 / 4 : ℝ)) ^ (-(N : ℝ)) ≤
      Real.exp (-(N : ℝ) / 128) := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hpow : (1 / 2 : ℝ) ^ (-(N : ℝ)) =
      Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    congr 1
    ring
  have hlogmul : (N : ℝ) * Real.log 2 ≤ (N : ℝ) := by
    calc
      (N : ℝ) * Real.log 2 ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog.le (by positivity)
      _ = (N : ℝ) := by ring
  have hproduct : Real.exp (-(9 * (N : ℝ)) / 4) *
      (1 - 2 * (1 / 4 : ℝ)) ^ (-(N : ℝ)) =
      Real.exp (-(9 * (N : ℝ)) / 4 + (N : ℝ) * Real.log 2) := by
    rw [show 1 - 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num, hpow,
      ← Real.exp_add]
  rw [hproduct]
  exact Real.exp_le_exp.mpr (by nlinarith)

private lemma centeredTailRate {r : ℕ} (hN : 192 ≤ r + 1) :
    Real.exp (((r + 1 : ℕ) : ℝ) / 4) *
        (1 - 2 * (-1 / 2 : ℝ)) ^ (-(r : ℝ) / 2) ≤
      Real.exp (-((r + 1 : ℕ) : ℝ) / 128) := by
  have hlog : (2 : ℝ) / 3 < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    simpa using h
  have hr : 191 ≤ r := by omega
  have hlogmul : (r : ℝ) / 3 ≤ (r : ℝ) / 2 * Real.log 2 := by
    have hr0 : 0 ≤ (r : ℝ) / 2 := by positivity
    have hlog0 : 0 ≤ Real.log 2 - (2 : ℝ) / 3 := by linarith
    have h := mul_nonneg hr0 hlog0
    nlinarith
  have hpow : (2 : ℝ) ^ (-(r : ℝ) / 2) =
      Real.exp (Real.log 2 * (-(r : ℝ) / 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hproduct : Real.exp (((r + 1 : ℕ) : ℝ) / 4) *
      (1 - 2 * (-1 / 2 : ℝ)) ^ (-(r : ℝ) / 2) =
      Real.exp (((r + 1 : ℕ) : ℝ) / 4 + Real.log 2 * (-(r : ℝ) / 2)) := by
    rw [show 1 - 2 * (-1 / 2 : ℝ) = (2 : ℝ) by norm_num, hpow,
      ← Real.exp_add]
  rw [hproduct]
  apply Real.exp_le_exp.mpr
  have hrreal : 191 ≤ (r : ℝ) := by exact_mod_cast hr
  calc
    ((r + 1 : ℕ) : ℝ) / 4 + Real.log 2 * (-(r : ℝ) / 2) =
        (r : ℝ) / 4 + 1 / 4 - (r : ℝ) / 2 * Real.log 2 := by
      push_cast
      ring
    _ ≤ (r : ℝ) / 4 + 1 / 4 - (r : ℝ) / 3 := by linarith [hlogmul]
    _ ≤ -((r + 1 : ℕ) : ℝ) / 128 := by
      push_cast
      linarith [hrreal]

private theorem measure_olsNoiseNormSq_gt_rate {N : ℕ} :
    olsPairGaussianLaw N {G | 9 * (N : ℝ) < olsNoiseNormSq G} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) := by
  exact (measure_olsNoiseNormSq_gt (N := N)).trans <|
    ENNReal.ofReal_le_ofReal rawTailRate

private theorem measure_olsCenteredDesign_lt_rate {r : ℕ} (hN : 192 ≤ r + 1) :
    olsPairGaussianLaw (r + 1)
      {G | olsCenteredDesign G < ((r + 1 : ℕ) : ℝ) / 2} ≤
      ENNReal.ofReal (Real.exp (-((r + 1 : ℕ) : ℝ) / 128)) := by
  exact (measure_olsCenteredDesign_lt (r := r)).trans <|
    ENNReal.ofReal_le_ofReal (centeredTailRate hN)

/-- The actual OLS good-set complement has an explicit exponential bound for
all sample sizes `N = n + 2` at least `192`. -/
theorem measure_compl_olsGoodSet_le {n : ℕ} (hN : 192 ≤ n + 2) :
    olsPairGaussianLaw (n + 2) (olsGoodSet n)ᶜ ≤
      ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ) *
        Real.exp (-((n + 2 : ℕ) : ℝ) / 128)) := by
  let N : ℕ := n + 2
  let μ := olsPairGaussianLaw N
  let raw : Set (Fin N → ℝ × ℝ) := {G | 9 * (N : ℝ) < olsNoiseNormSq G}
  let design : Set (Fin N → ℝ × ℝ) :=
    {G | olsCenteredDesign G < (N : ℝ) / 2}
  let coord : Set (Fin N → ℝ × ℝ) :=
    {G | ∃ i : Fin N, (N : ℝ) / 64 < (G i).1 ^ 2}
  have hN192 : 192 ≤ N := by simpa [N] using hN
  have hN2 : 2 ≤ N := by omega
  have hcover : (olsGoodSet n)ᶜ ⊆ raw ∪ design ∪ coord := by
    intro G hG
    have hbad : ¬(olsNoiseNorm G ≤ 3 * Real.sqrt (N : ℝ) ∧
        (N : ℝ) / 2 ≤ olsCenteredDesign G ∧
        ∀ i : Fin N, (G i).1 ^ 2 ≤ (N : ℝ) / 64) := by
      simpa [olsGoodSet, N, and_assoc] using hG
    rcases not_and_or.mp hbad with hnorm | hrest
    · left
      left
      change 9 * (N : ℝ) < olsNoiseNormSq G
      have hnorm' : 3 * Real.sqrt (N : ℝ) < olsNoiseNorm G := by
        simpa [not_le] using hnorm
      have hQnonneg : 0 ≤ olsNoiseNormSq G := by
        unfold olsNoiseNormSq
        positivity
      have hthreshold : 0 ≤ 3 * Real.sqrt (N : ℝ) := by positivity
      have hsquare : (3 * Real.sqrt (N : ℝ)) ^ 2 <
          (Real.sqrt (olsNoiseNormSq G)) ^ 2 :=
        (sq_lt_sq₀ hthreshold (Real.sqrt_nonneg _)).2 (by simpa [olsNoiseNorm] using hnorm')
      rw [Real.sq_sqrt hQnonneg] at hsquare
      have hNsqrt : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hthresholdSq : (3 * Real.sqrt (N : ℝ)) ^ 2 = 9 * (N : ℝ) := by
        rw [mul_pow, hNsqrt]
        norm_num
      rw [hthresholdSq] at hsquare
      exact hsquare
    rcases not_and_or.mp hrest with hdesign | hcoord
    · left
      right
      change olsCenteredDesign G < (N : ℝ) / 2
      simpa [not_le] using hdesign
    · right
      change ∃ i : Fin N, (N : ℝ) / 64 < (G i).1 ^ 2
      obtain ⟨i, hi⟩ := not_forall.mp hcoord
      refine ⟨i, ?_⟩
      exact lt_of_not_ge hi
  have hmeasure : μ (olsGoodSet n)ᶜ ≤ μ raw + μ design + μ coord := by
    calc
      μ (olsGoodSet n)ᶜ ≤ μ (raw ∪ design ∪ coord) := measure_mono hcover
      _ ≤ μ (raw ∪ design) + μ coord := measure_union_le _ _
      _ ≤ μ raw + μ design + μ coord := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (add_le_add_right (measure_union_le raw design) (μ coord))
  have hraw := measure_olsNoiseNormSq_gt_rate (N := N)
  have hdesign := measure_olsCenteredDesign_lt_rate (r := n + 1) (by omega)
  have hdesign' : μ design ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) := by
    dsimp [design, μ]
    convert hdesign using 1
  have hcoord := measure_olsCovariateCoordinateSq_bad (N := N)
  have hsum : μ raw + μ design + μ coord ≤
      ENNReal.ofReal (4 * (N : ℝ) * Real.exp (-(N : ℝ) / 128)) := by
    have hsum' : μ raw + μ design + μ coord ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) +
          ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) +
          ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(N : ℝ) / 128))) := by
      exact add_le_add (add_le_add (by simpa [raw, μ] using hraw)
        hdesign') (by simpa [coord, μ, mul_assoc, mul_comm, mul_left_comm] using hcoord)
    have hreal : Real.exp (-(N : ℝ) / 128) + Real.exp (-(N : ℝ) / 128) +
        (N : ℝ) * (2 * Real.exp (-(N : ℝ) / 128)) ≤
      4 * (N : ℝ) * Real.exp (-(N : ℝ) / 128) := by
      have hNreal : 2 ≤ (N : ℝ) := by exact_mod_cast hN2
      have he : 0 ≤ Real.exp (-(N : ℝ) / 128) := (Real.exp_pos _).le
      have hcoeff : 2 + 2 * (N : ℝ) ≤ 4 * (N : ℝ) := by linarith
      calc
        _ = (2 + 2 * (N : ℝ)) * Real.exp (-(N : ℝ) / 128) := by ring
        _ ≤ (4 * (N : ℝ)) * Real.exp (-(N : ℝ) / 128) :=
          mul_le_mul_of_nonneg_right hcoeff he
        _ = _ := by ring
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) +
          ENNReal.ofReal (Real.exp (-(N : ℝ) / 128)) +
          ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(N : ℝ) / 128))) := hsum'
      _ = ENNReal.ofReal (Real.exp (-(N : ℝ) / 128) +
          Real.exp (-(N : ℝ) / 128) +
          (N : ℝ) * (2 * Real.exp (-(N : ℝ) / 128))) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),
          ← ENNReal.ofReal_add (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
            (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (Real.exp_nonneg _)))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hfinal := hmeasure.trans hsum
  simpa [N] using hfinal

end LOOConcentration
