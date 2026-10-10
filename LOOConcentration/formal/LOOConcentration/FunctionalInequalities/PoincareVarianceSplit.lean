import LOOConcentration.FunctionalInequalities.OneSpacePoincareLimit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Variance form and product splitting for Poincaré inequalities

This module centers the accepted one-observation inequality and proves bounded
variance decompositions for two-factor products and finite coordinate products.
It does not assert product Poincaré without a product-energy argument.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- Integral variance, with the finite-measure real formula used in the paper. -/
noncomputable def integralVariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2

private abbrev OneObservationLip (k m : ℕ) :=
  {g : Observation (k + 1) (m + 1) → ℝ //
    ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |g w - g v| ≤ K * observationNorm (w - v)}

/-- The one-observation Poincaré bound in variance form, with no centering
assumption on the bounded test function. -/
theorem oneObservation_poincare_variance_from_logSobolev
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : OneObservationLip k m)
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ)
    (hbounded : ∀ z, |g.1 z| ≤ B) :
    integralVariance μ g.1 ≤
      C * (∫ z, observationLocalSlope g z ^ 2 ∂μ) := by
  have hB : 0 ≤ B := (abs_nonneg (g.1 0)).trans (hbounded 0)
  have hg : Integrable g.1 μ := oneObservationLip_integrable_of_bounded g hbounded
  have hmeanUpper : (∫ z, g.1 z ∂μ) ≤ B := by
    calc
      (∫ z, g.1 z ∂μ) ≤ ∫ _ : Observation (k + 1) (m + 1), B ∂μ :=
        integral_mono hg (integrable_const B) fun z => (abs_le.mp (hbounded z)).2
      _ = B := by simp
  have hmeanLower : -B ≤ (∫ z, g.1 z ∂μ) := by
    calc
      -B = ∫ _ : Observation (k + 1) (m + 1), (-B : ℝ) ∂μ := by simp
      _ ≤ ∫ z, g.1 z ∂μ :=
        integral_mono (integrable_const (-B)) hg fun z => (abs_le.mp (hbounded z)).1
  let mean : ℝ := ∫ z, g.1 z ∂μ
  let centered : OneObservationLip k m := ⟨fun z => g.1 z - mean, by
    intro z
    obtain ⟨U, hU, K, hK, hLip⟩ := g.2 z
    refine ⟨U, hU, K, hK, ?_⟩
    intro w hw v hv
    calc
      |(g.1 w - mean) - (g.1 v - mean)| = |g.1 w - g.1 v| := by congr 1; ring
      _ ≤ K * observationNorm (w - v) := hLip w hw v hv⟩
  have hcenterMean : ∫ z, centered.1 z ∂μ = 0 := by
    rw [show (fun z => centered.1 z) = (fun z => g.1 z - mean) by rfl]
    rw [integral_sub hg (integrable_const mean)]
    simp [mean]
  have hcenterBound : ∀ z, |centered.1 z| ≤ 2 * B := by
    intro z
    have hgz : -B ≤ g.1 z ∧ g.1 z ≤ B := abs_le.mp (hbounded z)
    have hm : -B ≤ mean ∧ mean ≤ B := ⟨hmeanLower, hmeanUpper⟩
    rw [abs_le]
    constructor <;> dsimp [centered] <;> linarith [hgz.1, hgz.2, hm.1, hm.2]
  have hslope : ∀ z, observationLocalSlope centered z = observationLocalSlope g z := by
    intro z
    unfold observationLocalSlope
    congr 1
    funext w
    dsimp [centered]
    congr 1
    ring_nf
  have hcenterEnergy : Integrable
      (fun z => observationLocalSlope centered z ^ 2) μ := by
    simpa only [hslope] using hgEnergy
  have hcenteredBound := oneObservation_poincare_from_logSobolev
    hLSI centered hcenterEnergy hcenterMean hcenterBound
  have hgSq : Integrable (fun z => g.1 z ^ 2) μ := (hLSI.2 g hgEnergy).1
  have hlinear : Integrable (fun z => (-2 * mean) * g.1 z) μ :=
    hg.const_mul _
  have hconstant : Integrable (fun _ : Observation (k + 1) (m + 1) => mean ^ 2) μ :=
    integrable_const _
  have hlinearInt : (∫ z, (-2 * mean) * g.1 z ∂μ) =
      (-2 * mean) * (∫ z, g.1 z ∂μ) := integral_const_mul _ _
  have hconstantInt :
      (∫ _ : Observation (k + 1) (m + 1), mean ^ 2 ∂μ) = mean ^ 2 := by simp
  have hsumFun :
      (fun z : Observation (k + 1) (m + 1) =>
        g.1 z ^ 2 + ((-2 * mean) * g.1 z + mean ^ 2)) =
      (fun z => g.1 z ^ 2) +
        ((fun z => (-2 * mean) * g.1 z) + fun _ => mean ^ 2) := by
    funext z
    rfl
  have hcenterVariance :
      (∫ z, centered.1 z ^ 2 ∂μ) = integralVariance μ g.1 := by
    have hpoint (z : Observation (k + 1) (m + 1)) :
        centered.1 z ^ 2 = g.1 z ^ 2 + ((-2 * mean) * g.1 z + mean ^ 2) := by
      dsimp [centered]
      ring
    calc
      (∫ z, centered.1 z ^ 2 ∂μ) =
          ∫ z, g.1 z ^ 2 + ((-2 * mean) * g.1 z + mean ^ 2) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (∫ z, g.1 z ^ 2 ∂μ) +
          ((∫ z, (-2 * mean) * g.1 z ∂μ) +
            ∫ _ : Observation (k + 1) (m + 1), mean ^ 2 ∂μ) := by
        rw [hsumFun, integral_add' hgSq (hlinear.add hconstant),
          integral_add' hlinear hconstant]
      _ = integralVariance μ g.1 := by
        rw [hlinearInt, hconstantInt]
        simp [integralVariance, mean]
        ring_nf
  calc
    integralVariance μ g.1 = ∫ z, centered.1 z ^ 2 ∂μ := hcenterVariance.symm
    _ ≤ C * (∫ z, observationLocalSlope centered z ^ 2 ∂μ) := hcenteredBound
    _ = C * (∫ z, observationLocalSlope g z ^ 2 ∂μ) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change observationLocalSlope centered z ^ 2 = observationLocalSlope g z ^ 2
        rw [hslope z]

private theorem integrable_of_measurable_norm_bound
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

/-- Bounded measurable functions satisfy the two-factor variance
decomposition, with variance expanded as `∫ f² - (∫ f)²`. -/
theorem integralVariance_prod_two_factor
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    integralVariance (μ.prod ν) F =
      (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) +
        integralVariance μ (fun x => ∫ y, F (x, y) ∂ν) := by
  let sectionMean : α → ℝ := fun x => ∫ y, F (x, y) ∂ν
  let sectionSecond : α → ℝ := fun x => ∫ y, F (x, y) ^ 2 ∂ν
  have hF2 : Measurable (fun p : α × β => F p ^ 2) := hF.pow_const 2
  have hF2bound (p : α × β) : ‖F p ^ 2‖ ≤ B ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F p))]
    calc
      F p ^ 2 = |F p| ^ 2 := by rw [sq_abs]
      _ ≤ B ^ 2 := by
        have hprod := mul_nonneg (sub_nonneg.mpr (hFbound p))
          (add_nonneg hB (abs_nonneg (F p)))
        nlinarith
  have hFint : Integrable F (μ.prod ν) :=
    integrable_of_measurable_norm_bound hF B fun p => by
      simpa only [Real.norm_eq_abs] using hFbound p
  have hF2int : Integrable (fun p : α × β => F p ^ 2) (μ.prod ν) :=
    integrable_of_measurable_norm_bound hF2 (B ^ 2) hF2bound
  have hFsectionMeas (x : α) : Measurable (fun y : β => F (x, y)) :=
    hF.comp (measurable_prodMk_left (x := x))
  have hFsectionInt (x : α) : Integrable (fun y : β => F (x, y)) ν :=
    integrable_of_measurable_norm_bound (hFsectionMeas x) B fun y => by
      simpa only [Real.norm_eq_abs] using hFbound (x, y)
  have hFsection2Int (x : α) : Integrable (fun y : β => F (x, y) ^ 2) ν :=
    integrable_of_measurable_norm_bound
      (hF2.comp (measurable_prodMk_left (x := x))) (B ^ 2) fun y => hF2bound (x, y)
  have hsectionMeanStrong : StronglyMeasurable sectionMean := by
    change StronglyMeasurable (fun x => ∫ y, F (x, y) ∂ν)
    exact hF.stronglyMeasurable.integral_prod_right'
  have hsectionMeanMeas : Measurable sectionMean := hsectionMeanStrong.measurable
  have hsectionMeanInt : Integrable sectionMean μ := by
    change Integrable (fun x => ∫ y, F (x, y) ∂ν) μ
    exact hFint.integral_prod_left
  have hsectionMeanBound (x : α) : |sectionMean x| ≤ B := by
    calc
      |sectionMean x| ≤ ∫ y, |F (x, y)| ∂ν :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ : β, B ∂ν :=
        integral_mono (hFsectionInt x).abs (integrable_const B) fun y => hFbound (x, y)
      _ = B := by simp
  have hsectionMean2 : Measurable (fun x => sectionMean x ^ 2) :=
    hsectionMeanMeas.pow_const 2
  have hsectionMean2Bound (x : α) : ‖sectionMean x ^ 2‖ ≤ B ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (sectionMean x))]
    calc
      sectionMean x ^ 2 = |sectionMean x| ^ 2 := by rw [sq_abs]
      _ ≤ B ^ 2 := by
        have hprod := mul_nonneg (sub_nonneg.mpr (hsectionMeanBound x))
          (add_nonneg hB (abs_nonneg (sectionMean x)))
        nlinarith
  have hsectionMean2Int : Integrable (fun x => sectionMean x ^ 2) μ :=
    integrable_of_measurable_norm_bound hsectionMean2 (B ^ 2) hsectionMean2Bound
  have hsectionSecondInt : Integrable sectionSecond μ := by
    change Integrable (fun x => ∫ y, F (x, y) ^ 2 ∂ν) μ
    exact hF2int.integral_prod_left
  have hF2Fubini :
      (∫ p, F p ^ 2 ∂(μ.prod ν)) = ∫ x, sectionSecond x ∂μ := by
    exact integral_prod (fun p : α × β => F p ^ 2) hF2int
  have hFFubini :
      (∫ p, F p ∂(μ.prod ν)) = ∫ x, sectionMean x ∂μ := by
    exact integral_prod F hFint
  have hsectionVarianceInt :
      (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) =
        (∫ x, sectionSecond x ∂μ) - ∫ x, sectionMean x ^ 2 ∂μ := by
    unfold integralVariance
    change (∫ x, sectionSecond x - sectionMean x ^ 2 ∂μ) = _
    exact integral_sub hsectionSecondInt hsectionMean2Int
  calc
    integralVariance (μ.prod ν) F =
        (∫ x, sectionSecond x ∂μ) - (∫ x, sectionMean x ∂μ) ^ 2 := by
      simp only [integralVariance, hF2Fubini, hFFubini]
    _ = (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) +
        integralVariance μ sectionMean := by
      rw [hsectionVarianceInt]
      simp only [integralVariance]
      ring

/-- Split the variance of a bounded measurable function on a finite i.i.d.
product by isolating any chosen coordinate. -/
theorem integralVariance_piFin_succ_split
    {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {r : ℕ}
    (f : (Fin (r + 1) → E) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hfbound : ∀ D, |f D| ≤ B)
    (i : Fin (r + 1)) :
    integralVariance (Measure.pi fun _ : Fin (r + 1) => μ) f =
      (∫ z, integralVariance (Measure.pi fun _ : Fin r => μ)
        (fun tail => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => E) i).symm (z, tail))) ∂μ) +
      integralVariance μ (fun z => ∫ tail,
        f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => E) i).symm (z, tail))
          ∂Measure.pi fun _ : Fin r => μ) := by
  let e : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let F : E × (Fin r → E) → ℝ := fun p => f (e.symm p)
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (r + 1) => μ)
      (μ.prod ν) := by
    simpa [e, ν] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) i)
  have hF : Measurable F := hf.comp e.symm.measurable
  have hFbound (p : E × (Fin r → E)) : |F p| ≤ B := hfbound (e.symm p)
  have hF2transport :
      (∫ D, f D ^ 2 ∂Measure.pi fun _ : Fin (r + 1) => μ) =
        ∫ p, F p ^ 2 ∂(μ.prod ν) := by
    calc
      (∫ D, f D ^ 2 ∂Measure.pi fun _ : Fin (r + 1) => μ) =
          ∫ D, F (e D) ^ 2 ∂Measure.pi fun _ : Fin (r + 1) => μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun D => by simp [F]
      _ = ∫ p, F p ^ 2 ∂(μ.prod ν) := hmp.integral_comp' (fun p => F p ^ 2)
  have hFtransport :
      (∫ D, f D ∂Measure.pi fun _ : Fin (r + 1) => μ) =
        ∫ p, F p ∂(μ.prod ν) := by
    calc
      (∫ D, f D ∂Measure.pi fun _ : Fin (r + 1) => μ) =
          ∫ D, F (e D) ∂Measure.pi fun _ : Fin (r + 1) => μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun D => by simp [F]
      _ = ∫ p, F p ∂(μ.prod ν) := hmp.integral_comp' F
  have hvarianceTransport :
      integralVariance (Measure.pi fun _ : Fin (r + 1) => μ) f =
        integralVariance (μ.prod ν) F := by
    unfold integralVariance
    rw [hF2transport, hFtransport]
  calc
    integralVariance (Measure.pi fun _ : Fin (r + 1) => μ) f =
        integralVariance (μ.prod ν) F := hvarianceTransport
    _ = (∫ z, integralVariance ν (fun tail => F (z, tail)) ∂μ) +
        integralVariance μ (fun z => ∫ tail, F (z, tail) ∂ν) :=
      integralVariance_prod_two_factor μ ν F B hB hF hFbound
    _ = (∫ z, integralVariance (Measure.pi fun _ : Fin r => μ)
          (fun tail => f (e.symm (z, tail))) ∂μ) +
        integralVariance μ (fun z => ∫ tail,
          f (e.symm (z, tail)) ∂Measure.pi fun _ : Fin r => μ) := by
      simp [F, ν, e]

end LOOConcentration
