import LOOConcentration.FunctionalInequalities.NonnegativeEntropyMixture
import LOOConcentration.Examples.GaussianBoundedLipschitzLSI
import LOOConcentration.Geometry.GaussianCoordinateEnergyIntegral
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# Bounded Lipschitz Gaussian product LSI on one observation

This module transports the actual two-coordinate Gaussian inequality to the
frozen `Observation 1 1` carrier. The coordinate reindexing is made explicit:
`ObservationCoordinate 1 1 = Fin 1 ⊕ Fin 1` is identified isometrically with
`Fin 2`, and its product standard Gaussian law is the literal pair law.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

noncomputable section

namespace LOOConcentration.Examples

private abbrev ObsIndex := LOOConcentration.ObservationCoordinate 1 1

/-- The source coordinate index `Fin 1 ⊕ Fin 1`, ordered feature then
response, is explicitly reindexed as `Fin 2`. -/
private def observationIndexFinTwo : ObsIndex ≃ Fin 2 :=
  finSumFinEquiv

/-- The reindexing acts by a genuine PiLp linear isometry, so it preserves the
Euclidean norm rather than the inherited max norm on a product type. -/
private def observationEuclideanFinTwoIsometry :
    EuclideanSpace ℝ ObsIndex ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft (2 : ENNReal) ℝ ℝ observationIndexFinTwo

@[simp]
private theorem observationEuclideanFinTwoIsometry_apply
    (x : EuclideanSpace ℝ ObsIndex) (i : Fin 2) :
    observationEuclideanFinTwoIsometry x i = x (observationIndexFinTwo.symm i) := rfl

/-- A Euclidean test pulled across the source-faithful coordinate isometry. -/
private def reindexedTest (f : EuclideanSpace ℝ ObsIndex → ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun x => f (observationEuclideanFinTwoIsometry.symm x)

private theorem lipschitzWith_reindexedTest
    {K : ℝ≥0} {f : EuclideanSpace ℝ ObsIndex → ℝ}
    (hf : LipschitzWith K f) : LipschitzWith K (reindexedTest f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (f (observationEuclideanFinTwoIsometry.symm x))
      (f (observationEuclideanFinTwoIsometry.symm y)) ≤ (K : ℝ) * dist x y
  calc
    dist (f (observationEuclideanFinTwoIsometry.symm x))
        (f (observationEuclideanFinTwoIsometry.symm y)) ≤
        (K : ℝ) * dist (observationEuclideanFinTwoIsometry.symm x)
          (observationEuclideanFinTwoIsometry.symm y) := hf.dist_le_mul _ _
    _ = (K : ℝ) * dist x y := by simp

private theorem norm_reindexedTest_le
    {B : ℝ≥0} {f : EuclideanSpace ℝ ObsIndex → ℝ}
    (hB : ∀ x, ‖f x‖ ≤ (B : ℝ)) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖reindexedTest f x‖ ≤ (B : ℝ) := hB _

private abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

private noncomputable def finTwoPair : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)

private noncomputable def pairToEuclideanFinTwo (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp (2 : ENNReal) (finTwoPair.symm p)

@[simp]
private theorem pairToEuclideanFinTwo_zero (p : ℝ × ℝ) :
    pairToEuclideanFinTwo p 0 = p.1 := by
  simp [pairToEuclideanFinTwo, finTwoPair]

@[simp]
private theorem pairToEuclideanFinTwo_one (p : ℝ × ℝ) :
    pairToEuclideanFinTwo p 1 = p.2 := by
  simp [pairToEuclideanFinTwo, finTwoPair]

private theorem finTwoPair_measurePreserving :
    MeasurePreserving finTwoPair (LOOConcentration.standardGaussianPiLaw (Fin 2)) (γ.prod γ) := by
  simpa [finTwoPair, LOOConcentration.standardGaussianPiLaw, γ] using
    (MeasureTheory.measurePreserving_piFinTwo
      (μ := fun _ : Fin 2 => γ))

/-- The literal independent real-pair law, transported through `Fin 2` and
the PiLp `toLp` map, is the canonical two-dimensional Gaussian law. -/
private theorem pairToEuclideanFinTwo_map_law :
    (γ.prod γ).map pairToEuclideanFinTwo =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
  have hmp := finTwoPair_measurePreserving.symm
  calc
    (γ.prod γ).map pairToEuclideanFinTwo =
        ((γ.prod γ).map finTwoPair.symm).map
          (WithLp.toLp (2 : ENNReal)) := by
            rw [Measure.map_map
              (PiLp.continuous_toLp (p := (2 : ENNReal))
                (β := fun _ : Fin 2 => ℝ)).measurable
              finTwoPair.symm.measurable]
            rfl
    _ = (LOOConcentration.standardGaussianPiLaw (Fin 2)).map
          (WithLp.toLp (2 : ENNReal)) := by rw [hmp.map_eq]
    _ = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
          simpa [LOOConcentration.standardGaussianPiLaw, γ] using
            (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin 2))

private noncomputable def pairTest (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ℝ × ℝ → ℝ := fun p => f (pairToEuclideanFinTwo p)

private noncomputable def secondPairSection
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : ℝ) : ℝ → ℝ :=
  fun y => pairTest f (x, y)

private noncomputable def firstPairSection
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (y : ℝ) : ℝ → ℝ :=
  fun x => pairTest f (x, y)

private theorem pairToEuclideanFinTwo_path_second (x y : ℝ) :
    pairToEuclideanFinTwo (x, y) = LOOConcentration.euclideanCoordinatePath
      (pairToEuclideanFinTwo (x, 0)) 1 y := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [LOOConcentration.euclideanCoordinatePath, EuclideanSpace.single_apply]

private theorem pairToEuclideanFinTwo_path_second_base (x y t : ℝ) :
    pairToEuclideanFinTwo (x, t) = LOOConcentration.euclideanCoordinatePath
      (pairToEuclideanFinTwo (x, y)) 1 t := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [LOOConcentration.euclideanCoordinatePath, EuclideanSpace.single_apply]

private theorem pairToEuclideanFinTwo_path_first (x y : ℝ) :
    pairToEuclideanFinTwo (x, y) = LOOConcentration.euclideanCoordinatePath
      (pairToEuclideanFinTwo (0, y)) 0 x := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [LOOConcentration.euclideanCoordinatePath, EuclideanSpace.single_apply]

private theorem pairToEuclideanFinTwo_path_first_base (x y t : ℝ) :
    pairToEuclideanFinTwo (t, y) = LOOConcentration.euclideanCoordinatePath
      (pairToEuclideanFinTwo (x, y)) 0 t := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [LOOConcentration.euclideanCoordinatePath, EuclideanSpace.single_apply]

private theorem secondPairSection_eq_coordinateSection
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : ℝ) :
    secondPairSection f x = LOOConcentration.euclideanCoordinateSection f
      (pairToEuclideanFinTwo (x, 0)) 1 := by
  funext y
  change f (pairToEuclideanFinTwo (x, y)) =
    f (LOOConcentration.euclideanCoordinatePath (pairToEuclideanFinTwo (x, 0)) 1 y)
  rw [pairToEuclideanFinTwo_path_second]

private theorem firstPairSection_eq_coordinateSection
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (y : ℝ) :
    firstPairSection f y = LOOConcentration.euclideanCoordinateSection f
      (pairToEuclideanFinTwo (0, y)) 0 := by
  funext x
  change f (pairToEuclideanFinTwo (x, y)) =
    f (LOOConcentration.euclideanCoordinatePath (pairToEuclideanFinTwo (0, y)) 0 x)
  rw [pairToEuclideanFinTwo_path_first]

private theorem deriv_secondPairSection_eq_coordinateDerivative
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x y : ℝ) :
    deriv (secondPairSection f x) y =
      LOOConcentration.euclideanCoordinateSectionDerivative f 1
        (pairToEuclideanFinTwo (x, y)) := by
  have hsections : LOOConcentration.euclideanCoordinateSection f
      (pairToEuclideanFinTwo (x, 0)) 1 =
      LOOConcentration.euclideanCoordinateSection f
        (pairToEuclideanFinTwo (x, y)) 1 := by
    funext t
    change f (LOOConcentration.euclideanCoordinatePath
        (pairToEuclideanFinTwo (x, 0)) 1 t) =
      f (LOOConcentration.euclideanCoordinatePath (pairToEuclideanFinTwo (x, y)) 1 t)
    rw [← pairToEuclideanFinTwo_path_second x t,
      ← pairToEuclideanFinTwo_path_second_base x y t]
  rw [secondPairSection_eq_coordinateSection]
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g y) hsections
  unfold LOOConcentration.euclideanCoordinateSectionDerivative
  simpa only [pairToEuclideanFinTwo_one] using hderiv

private theorem deriv_firstPairSection_eq_coordinateDerivative
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x y : ℝ) :
    deriv (firstPairSection f y) x =
      LOOConcentration.euclideanCoordinateSectionDerivative f 0
        (pairToEuclideanFinTwo (x, y)) := by
  have hsections : LOOConcentration.euclideanCoordinateSection f
      (pairToEuclideanFinTwo (0, y)) 0 =
      LOOConcentration.euclideanCoordinateSection f
        (pairToEuclideanFinTwo (x, y)) 0 := by
    funext t
    change f (LOOConcentration.euclideanCoordinatePath
        (pairToEuclideanFinTwo (0, y)) 0 t) =
      f (LOOConcentration.euclideanCoordinatePath (pairToEuclideanFinTwo (x, y)) 0 t)
    rw [← pairToEuclideanFinTwo_path_first t y,
      ← pairToEuclideanFinTwo_path_first_base x y t]
  rw [firstPairSection_eq_coordinateSection]
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g x) hsections
  unfold LOOConcentration.euclideanCoordinateSectionDerivative
  simpa only [pairToEuclideanFinTwo_zero] using hderiv

private theorem lipschitz_secondPairSection
    {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : LipschitzWith K f) (x : ℝ) :
    LipschitzWith K (secondPairSection f x) := by
  rw [secondPairSection_eq_coordinateSection]
  exact LOOConcentration.lipschitzWith_euclideanCoordinateSection f hf _ 1

private theorem lipschitz_firstPairSection
    {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : LipschitzWith K f) (y : ℝ) :
    LipschitzWith K (firstPairSection f y) := by
  rw [firstPairSection_eq_coordinateSection]
  exact LOOConcentration.lipschitzWith_euclideanCoordinateSection f hf _ 0

private theorem measurable_pairToEuclideanFinTwo :
    Measurable pairToEuclideanFinTwo := by
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => ℝ)).measurable.comp finTwoPair.symm.measurable

private noncomputable def pairSecondDerivative
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (p : ℝ × ℝ) : ℝ :=
  LOOConcentration.euclideanCoordinateSectionDerivative f 1 (pairToEuclideanFinTwo p)

private noncomputable def pairFirstDerivative
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (p : ℝ × ℝ) : ℝ :=
  LOOConcentration.euclideanCoordinateSectionDerivative f 0 (pairToEuclideanFinTwo p)

private theorem integrable_pairDerivative_sq
    {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : LipschitzWith K f) (i : Fin 2) :
    Integrable
      (fun p : ℝ × ℝ =>
        (LOOConcentration.euclideanCoordinateSectionDerivative f i
          (pairToEuclideanFinTwo p)) ^ 2) (γ.prod γ) := by
  have hstd := LOOConcentration.integrable_euclideanCoordinateSectionDerivative_sq K f hf i
  have hMapped : Integrable
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2)
      ((γ.prod γ).map pairToEuclideanFinTwo) := by
    simpa only [pairToEuclideanFinTwo_map_law] using hstd
  have hmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2) := by
    exact (LOOConcentration.measurable_euclideanCoordinateSectionDerivative f hf i).pow_const 2
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    measurable_pairToEuclideanFinTwo.aemeasurable).mp hMapped

private theorem integrable_bounded_square
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable (fun x => (f x) ^ 2) μ := by
  have hsqMeas : Measurable (fun x => (f x) ^ 2) := hf.pow_const 2
  have hsqBound : ∀ x, ‖(f x) ^ 2‖ ≤ B ^ 2 := by
    intro x
    have hAbs : |f x| ≤ B := by simpa [Real.norm_eq_abs] using hbound x
    have hsq := mul_self_le_mul_self (abs_nonneg (f x)) hAbs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))]
    simpa [sq_abs, pow_two] using hsq
  refine Integrable.mono' (integrable_const (B ^ 2)) hsqMeas.aestronglyMeasurable ?_
  filter_upwards with x
  exact hsqBound x

private theorem integrable_bounded_square_mul_log
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2)) μ := by
  have hsqMeas : Measurable (fun x => (f x) ^ 2) := hf.pow_const 2
  obtain ⟨C, hC0, hC⟩ :=
    isCompact_Icc.bddAbove_image
      (continuous_norm.comp Real.continuous_mul_log).continuousOn |>.exists_ge 0
  have hrange (x : Ω) : (f x) ^ 2 ∈ Set.Icc (0 : ℝ) (B ^ 2) := by
    constructor
    · exact sq_nonneg _
    · have hAbs : |f x| ≤ B := by simpa [Real.norm_eq_abs] using hbound x
      have hsq := mul_self_le_mul_self (abs_nonneg (f x)) hAbs
      simpa [sq_abs, pow_two] using hsq
  have hmeas := (Real.continuous_mul_log.measurable.comp hsqMeas)
  refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
  filter_upwards with x
  exact hC _ ⟨(f x) ^ 2, hrange x, rfl⟩

/-- Actual two-coordinate Gaussian LSI for a signed bounded globally
Lipschitz Euclidean test. Tensorization is applied to the genuine
nonnegative function f², and the two scalar conditionals are actual affine
coordinate sections. -/
private theorem standardGaussian_finTwo_boundedLipschitz_square_logSobolev
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {B K : ℝ≥0}
    (hf : LipschitzWith K f) (hbounded : ∀ x, ‖f x‖ ≤ (B : ℝ)) :
    Integrable (fun x => (f x) ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) ∧
      Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) ∧
      Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) ∧
      LOOConcentration.looconcentrationEntropy (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)))
          (fun x => (f x) ^ 2) ≤
        2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  let μ := γ.prod γ
  let F : ℝ × ℝ → ℝ := fun p => (pairTest f p) ^ 2
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, γ]
    infer_instance
  have hFmeas : Measurable F := by
    exact (hf.continuous.measurable.comp measurable_pairToEuclideanFinTwo).pow_const 2
  have hFnonneg (p : ℝ × ℝ) : 0 ≤ F p := sq_nonneg _
  have hFle (p : ℝ × ℝ) : F p ≤ (B : ℝ) ^ 2 := by
    have hAbs : |pairTest f p| ≤ (B : ℝ) := by
      simpa [Real.norm_eq_abs, pairTest, pairToEuclideanFinTwo] using
        hbounded (pairToEuclideanFinTwo p)
    have hsq := mul_self_le_mul_self (abs_nonneg (pairTest f p)) hAbs
    simpa [F, pairTest, sq_abs, pow_two] using hsq
  have hTensor := LOOConcentration.entropy_two_factor_subadditive_bounded_nonnegative
    γ γ F ((B : ℝ) ^ 2) (sq_nonneg _) hFmeas hFnonneg hFle
  have hCondIntegrable :=
    LOOConcentration.entropy_two_factor_conditional_integrable_bounded_nonnegative
      γ γ F ((B : ℝ) ^ 2) hFmeas hFnonneg hFle
  have hSecondLSI (x : ℝ) :=
    LOOConcentration.Examples.GaussianBoundedLipschitzLSI.standardGaussian_boundedLipschitz_square_logSobolev
      (u := secondPairSection f x) (B := B) (K := K)
      (lipschitz_secondPairSection hf x)
      (fun y => hbounded (pairToEuclideanFinTwo (x, y)))
  have hFirstLSI (y : ℝ) :=
    LOOConcentration.Examples.GaussianBoundedLipschitzLSI.standardGaussian_boundedLipschitz_square_logSobolev
      (u := firstPairSection f y) (B := B) (K := K)
      (lipschitz_firstPairSection hf y)
      (fun x => hbounded (pairToEuclideanFinTwo (x, y)))
  have hSecondEntropy (x : ℝ) :
      LOOConcentration.entropy γ (fun y => F (x, y)) ≤
        2 * (∫ y, (deriv (secondPairSection f x) y) ^ 2 ∂γ) := by
    change LOOConcentration.looconcentrationEntropy γ
      (fun y => (secondPairSection f x y) ^ 2) ≤ _
    exact (hSecondLSI x).2.2.2
  have hFirstEntropy (y : ℝ) :
      LOOConcentration.entropy γ (fun x => F (x, y)) ≤
        2 * (∫ x, (deriv (firstPairSection f y) x) ^ 2 ∂γ) := by
    change LOOConcentration.looconcentrationEntropy γ
      (fun x => (firstPairSection f y x) ^ 2) ≤ _
    exact (hFirstLSI y).2.2.2
  have hSecondKernelMeas : Measurable (fun p : ℝ × ℝ =>
      (deriv (secondPairSection f p.1) p.2) ^ 2) := by
    have hcoord := LOOConcentration.measurable_euclideanCoordinateSectionDerivative f hf 1
    convert (hcoord.comp measurable_pairToEuclideanFinTwo).pow_const 2 using 1
    ext p
    exact congrArg (fun z : ℝ => z ^ 2)
      (deriv_secondPairSection_eq_coordinateDerivative f p.1 p.2)
  have hFirstKernelMeas : Measurable (fun p : ℝ × ℝ =>
      (deriv (firstPairSection f p.2) p.1) ^ 2) := by
    have hcoord := LOOConcentration.measurable_euclideanCoordinateSectionDerivative f hf 0
    convert (hcoord.comp measurable_pairToEuclideanFinTwo).pow_const 2 using 1
    ext p
    exact congrArg (fun z : ℝ => z ^ 2)
      (deriv_firstPairSection_eq_coordinateDerivative f p.1 p.2)
  have hSecondKernelInt : Integrable (fun p : ℝ × ℝ =>
      (deriv (secondPairSection f p.1) p.2) ^ 2) μ := by
    have hcoord := integrable_pairDerivative_sq hf 1
    convert hcoord using 1
    ext p
    exact congrArg (fun z : ℝ => z ^ 2)
      (deriv_secondPairSection_eq_coordinateDerivative f p.1 p.2)
  have hFirstKernelInt : Integrable (fun p : ℝ × ℝ =>
      (deriv (firstPairSection f p.2) p.1) ^ 2) μ := by
    have hcoord := integrable_pairDerivative_sq hf 0
    convert hcoord using 1
    ext p
    exact congrArg (fun z : ℝ => z ^ 2)
      (deriv_firstPairSection_eq_coordinateDerivative f p.1 p.2)
  have hSecondOuterInt : Integrable (fun x : ℝ =>
      ∫ y : ℝ, (deriv (secondPairSection f x) y) ^ 2 ∂γ) γ :=
    hSecondKernelInt.integral_prod_left
  have hFirstOuterInt : Integrable (fun y : ℝ =>
      ∫ x : ℝ, (deriv (firstPairSection f y) x) ^ 2 ∂γ) γ :=
    hFirstKernelInt.integral_prod_right
  have hSecondIntegrated :
      (∫ x, LOOConcentration.entropy γ (fun y => F (x, y)) ∂γ) ≤
        2 * (∫ x, ∫ y, (deriv (secondPairSection f x) y) ^ 2 ∂γ ∂γ) := by
    calc
      _ ≤ ∫ x, 2 * (∫ y, (deriv (secondPairSection f x) y) ^ 2 ∂γ) ∂γ :=
        integral_mono hCondIntegrable.1 (hSecondOuterInt.const_mul 2) hSecondEntropy
      _ = _ := by rw [integral_const_mul]
  have hFirstIntegrated :
      (∫ y, LOOConcentration.entropy γ (fun x => F (x, y)) ∂γ) ≤
        2 * (∫ y, ∫ x, (deriv (firstPairSection f y) x) ^ 2 ∂γ ∂γ) := by
    calc
      _ ≤ ∫ y, 2 * (∫ x, (deriv (firstPairSection f y) x) ^ 2 ∂γ) ∂γ :=
        integral_mono hCondIntegrable.2 (hFirstOuterInt.const_mul 2) hFirstEntropy
      _ = _ := by rw [integral_const_mul]
  have hSecondFubini :
      (∫ x, ∫ y, (deriv (secondPairSection f x) y) ^ 2 ∂γ ∂γ) =
        ∫ p, (deriv (secondPairSection f p.1) p.2) ^ 2 ∂μ := by
    symm
    exact integral_prod _ hSecondKernelInt
  have hFirstFubini :
      (∫ y, ∫ x, (deriv (firstPairSection f y) x) ^ 2 ∂γ ∂γ) =
        ∫ p, (deriv (firstPairSection f p.2) p.1) ^ 2 ∂μ := by
    symm
    exact integral_prod_symm _ hFirstKernelInt
  have hSecondToStd :
      (∫ p, (deriv (secondPairSection f p.1) p.2) ^ 2 ∂μ) =
        ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f 1 x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    have hcoord := LOOConcentration.integrable_euclideanCoordinateSectionDerivative_sq K f hf 1
    have hcoordMapped : Integrable
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          (LOOConcentration.euclideanCoordinateSectionDerivative f 1 x) ^ 2)
        (μ.map pairToEuclideanFinTwo) := by
      simpa [μ, pairToEuclideanFinTwo_map_law] using hcoord
    calc
      _ = ∫ p, (LOOConcentration.euclideanCoordinateSectionDerivative f 1
          (pairToEuclideanFinTwo p)) ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards with p
            exact congrArg (fun z : ℝ => z ^ 2)
              (deriv_secondPairSection_eq_coordinateDerivative f p.1 p.2)
      _ = ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f 1 x) ^ 2
          ∂(μ.map pairToEuclideanFinTwo) := by
            symm
            exact integral_map measurable_pairToEuclideanFinTwo.aemeasurable
              hcoordMapped.aestronglyMeasurable
      _ = _ := by rw [pairToEuclideanFinTwo_map_law]
  have hFirstToStd :
      (∫ p, (deriv (firstPairSection f p.2) p.1) ^ 2 ∂μ) =
        ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f 0 x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    have hcoord := LOOConcentration.integrable_euclideanCoordinateSectionDerivative_sq K f hf 0
    have hcoordMapped : Integrable
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          (LOOConcentration.euclideanCoordinateSectionDerivative f 0 x) ^ 2)
        (μ.map pairToEuclideanFinTwo) := by
      simpa [μ, pairToEuclideanFinTwo_map_law] using hcoord
    calc
      _ = ∫ p, (LOOConcentration.euclideanCoordinateSectionDerivative f 0
          (pairToEuclideanFinTwo p)) ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards with p
            exact congrArg (fun z : ℝ => z ^ 2)
              (deriv_firstPairSection_eq_coordinateDerivative f p.1 p.2)
      _ = ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f 0 x) ^ 2
          ∂(μ.map pairToEuclideanFinTwo) := by
            symm
            exact integral_map measurable_pairToEuclideanFinTwo.aemeasurable
              hcoordMapped.aestronglyMeasurable
      _ = _ := by rw [pairToEuclideanFinTwo_map_law]
  have hEnergy := LOOConcentration.integral_fderiv_norm_sq_eq_sum_integral_coordinateDerivative_sq
    K f hf
  have htotalEnergy :
      (∫ x, ∫ y, (deriv (secondPairSection f x) y) ^ 2 ∂γ ∂γ) +
        (∫ y, ∫ x, (deriv (firstPairSection f y) x) ^ 2 ∂γ ∂γ) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    rw [hSecondFubini, hFirstFubini, hSecondToStd, hFirstToStd,
      hEnergy, Fin.sum_univ_two]
    ring
  have hEntropyBound : LOOConcentration.entropy μ F ≤
      2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
    calc
      LOOConcentration.entropy μ F ≤
          (∫ x, LOOConcentration.entropy γ (fun y => F (x, y)) ∂γ) +
            (∫ y, LOOConcentration.entropy γ (fun x => F (x, y)) ∂γ) := hTensor
      _ ≤ 2 * (∫ x, ∫ y,
            (deriv (secondPairSection f x) y) ^ 2 ∂γ ∂γ) +
          2 * (∫ y, ∫ x,
            (deriv (firstPairSection f y) x) ^ 2 ∂γ ∂γ) :=
        add_le_add hSecondIntegrated hFirstIntegrated
      _ = _ := by rw [← mul_add, htotalEnergy]
  have hPairTestMeas : Measurable (pairTest f) :=
    hf.continuous.measurable.comp measurable_pairToEuclideanFinTwo
  have hPairTestBound (p : ℝ × ℝ) : ‖pairTest f p‖ ≤ (B : ℝ) :=
    hbounded (pairToEuclideanFinTwo p)
  have hPairSquareInt : Integrable F μ := by
    have h := integrable_bounded_square (μ := μ) hPairTestMeas (B := (B : ℝ))
      B.coe_nonneg hPairTestBound
    simpa [F] using h
  have hPairLogInt : Integrable (fun p => F p * Real.log (F p)) μ := by
    have h := integrable_bounded_square_mul_log (μ := μ) hPairTestMeas
      (B := (B : ℝ))
      B.coe_nonneg hPairTestBound
    simpa [F] using h
  have hSquareInt := integrable_bounded_square (μ :=
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)))
      hf.continuous.measurable (B := (B : ℝ)) B.coe_nonneg hbounded
  have hLogInt := integrable_bounded_square_mul_log (μ :=
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)))
      hf.continuous.measurable (B := (B : ℝ)) B.coe_nonneg hbounded
  have hGradientInt :=
    LOOConcentration.integrable_fderiv_norm_sq_of_lipschitz K f hf
  have hEntropyMap :
      LOOConcentration.looconcentrationEntropy
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)))
          (fun x => (f x) ^ 2) = LOOConcentration.entropy μ F := by
    unfold LOOConcentration.looconcentrationEntropy LOOConcentration.entropy
    rw [← pairToEuclideanFinTwo_map_law]
    have hLogAEM : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          (f x) ^ 2 * Real.log ((f x) ^ 2))
        (μ.map pairToEuclideanFinTwo) := by
      simpa [μ, pairToEuclideanFinTwo_map_law] using hLogInt.aestronglyMeasurable
    have hSquareAEM : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin 2) => (f x) ^ 2)
        (μ.map pairToEuclideanFinTwo) := by
      simpa [μ, pairToEuclideanFinTwo_map_law] using hSquareInt.aestronglyMeasurable
    rw [integral_map measurable_pairToEuclideanFinTwo.aemeasurable
        hLogAEM,
      integral_map measurable_pairToEuclideanFinTwo.aemeasurable
        hSquareAEM]
    rfl
  refine ⟨hSquareInt, hLogInt, hGradientInt, ?_⟩
  rw [hEntropyMap]
  exact hEntropyBound

/-- The actual bounded Lipschitz Gaussian LSI on the Euclidean observation
carrier. It has the literal full Fréchet derivative energy and coefficient
one inside the displayed factor two. -/
theorem standardGaussian_observation_boundedLipschitz_square_logSobolev
    {f : EuclideanSpace ℝ ObsIndex → ℝ} {B K : ℝ≥0}
    (hf : LipschitzWith K f) (hbounded : ∀ x, ‖f x‖ ≤ (B : ℝ)) :
    Integrable (fun x => (f x) ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex)) ∧
      Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex)) ∧
      Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex)) ∧
      LOOConcentration.looconcentrationEntropy (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex))
          (fun x => (f x) ^ 2) ≤
        2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex)) := by
  let μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ObsIndex)
  let ν := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))
  let e := observationEuclideanFinTwoIsometry
  let g := reindexedTest f
  have hf' : LipschitzWith K g := lipschitzWith_reindexedTest hf
  have hbounded' : ∀ y, ‖g y‖ ≤ (B : ℝ) := fun y => norm_reindexedTest_le hbounded y
  have hcore := standardGaussian_finTwo_boundedLipschitz_square_logSobolev
    hf' hbounded'
  have hMap : μ.map e = ν := by
    simpa [μ, ν, e] using
      (ProbabilityTheory.stdGaussian_map observationEuclideanFinTwoIsometry)
  have hSquareMapped : Integrable (fun y : EuclideanSpace ℝ (Fin 2) => (g y) ^ 2)
      (μ.map e) := by
    simpa only [ν, hMap] using hcore.1
  have hLogMapped : Integrable
      (fun y : EuclideanSpace ℝ (Fin 2) => (g y) ^ 2 * Real.log ((g y) ^ 2))
      (μ.map e) := by
    simpa only [ν, hMap] using hcore.2.1
  have hSquareInt : Integrable (fun x => (f x) ^ 2) μ := by
    have h := (integrable_map_measure hSquareMapped.aestronglyMeasurable
      e.continuous.measurable.aemeasurable).mp hSquareMapped
    change Integrable (fun x : EuclideanSpace ℝ ObsIndex =>
      f (e.symm (e x)) ^ 2) μ at h
    simpa only [e.symm_apply_apply] using h
  have hLogInt : Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2)) μ := by
    have h := (integrable_map_measure hLogMapped.aestronglyMeasurable
      e.continuous.measurable.aemeasurable).mp hLogMapped
    change Integrable (fun x : EuclideanSpace ℝ ObsIndex =>
      f (e.symm (e x)) ^ 2 * Real.log (f (e.symm (e x)) ^ 2)) μ at h
    simpa only [e.symm_apply_apply] using h
  have hGradientInt :=
    LOOConcentration.integrable_fderiv_norm_sq_of_lipschitz K f hf
  have hDiff := LOOConcentration.standardGaussian_ae_differentiableAt_of_locallyLipschitz
    f hf.locallyLipschitz
  have hGradientAE : (fun x : EuclideanSpace ℝ ObsIndex =>
      ‖fderiv ℝ g (e x)‖ ^ 2) =ᵐ[μ]
      (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
    filter_upwards [hDiff] with x hx
    have hcomp : fderiv ℝ g (e x) =
        (fderiv ℝ f x).comp (e.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ ObsIndex) := by
      have houter : DifferentiableAt ℝ f (e.symm (e x)) := by
        simpa using hx
      change fderiv ℝ (f ∘ e.symm) (e x) = _
      simpa only [e.symm_apply_apply, e.symm.fderiv] using
        (fderiv_comp (f := (e.symm : EuclideanSpace ℝ (Fin 2) →
          EuclideanSpace ℝ ObsIndex)) (x := e x) houter e.symm.differentiableAt)
    rw [hcomp]
    congr 1
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
      (fderiv ℝ f x) e.symm
  have hGradientAEMapped :
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 2) =>
        ‖fderiv ℝ g y‖ ^ 2) (μ.map e) := by
    simpa [ν, hMap] using hcore.2.2.1.aestronglyMeasurable
  have hGradientMapIntegral :
      (∫ y : EuclideanSpace ℝ (Fin 2), ‖fderiv ℝ g y‖ ^ 2 ∂ν) =
        ∫ x : EuclideanSpace ℝ ObsIndex, ‖fderiv ℝ g (e x)‖ ^ 2 ∂μ := by
    rw [← hMap]
    exact integral_map e.continuous.measurable.aemeasurable hGradientAEMapped
  have hGradientIntegral :
      (∫ y : EuclideanSpace ℝ (Fin 2), ‖fderiv ℝ g y‖ ^ 2 ∂ν) =
        ∫ x : EuclideanSpace ℝ ObsIndex, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    calc
      _ = ∫ x : EuclideanSpace ℝ ObsIndex, ‖fderiv ℝ g (e x)‖ ^ 2 ∂μ :=
        hGradientMapIntegral
      _ = _ := integral_congr_ae hGradientAE
  have hEntropy :
      LOOConcentration.looconcentrationEntropy μ (fun x => (f x) ^ 2) =
        LOOConcentration.looconcentrationEntropy ν (fun y => (g y) ^ 2) := by
    unfold LOOConcentration.looconcentrationEntropy
    rw [← hMap]
    have hsqAEM : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 2) => (g y) ^ 2)
        (μ.map e) := hSquareMapped.aestronglyMeasurable
    have hlogAEM : AEStronglyMeasurable
        (fun y : EuclideanSpace ℝ (Fin 2) => (g y) ^ 2 * Real.log ((g y) ^ 2))
        (μ.map e) := hLogMapped.aestronglyMeasurable
    rw [integral_map e.continuous.measurable.aemeasurable hlogAEM,
      integral_map e.continuous.measurable.aemeasurable hsqAEM]
    simp [g, reindexedTest, e]
  have hBound := hcore.2.2.2
  refine ⟨hSquareInt, hLogInt, hGradientInt, ?_⟩
  rw [hEntropy, ← hGradientIntegral]
  exact hBound

/-- The bounded globally Lipschitz result on the actual frozen
`Observation 1 1` carrier. The function is the source's locally Lipschitz
pullback, and the slope energy is its literal frozen local-slope energy. -/
theorem gaussianObservation_boundedLipschitz_pullback_square_logSobolev
    {f : EuclideanSpace ℝ ObsIndex → ℝ} {B K : ℝ≥0}
    (hf : LipschitzWith K f) (hbounded : ∀ x, ‖f x‖ ≤ (B : ℝ)) :
    let u := LOOConcentration.locallyLipschitzObservationPullback f hf.locallyLipschitz
    Integrable (fun z => (u.1 z) ^ 2) LOOConcentration.gaussianObservationLaw ∧
      Integrable (fun z => (u.1 z) ^ 2 * Real.log ((u.1 z) ^ 2))
        LOOConcentration.gaussianObservationLaw ∧
      Integrable (fun z => (LOOConcentration.observationLocalSlope u z) ^ 2)
        LOOConcentration.gaussianObservationLaw ∧
      LOOConcentration.looconcentrationEntropy LOOConcentration.gaussianObservationLaw (fun z => (u.1 z) ^ 2) ≤
        2 * (∫ z, (LOOConcentration.observationLocalSlope u z) ^ 2
          ∂LOOConcentration.gaussianObservationLaw) := by
  let E := EuclideanSpace ℝ ObsIndex
  let μ := LOOConcentration.gaussianObservationLaw
  let obs : LOOConcentration.Observation 1 1 → E := LOOConcentration.observationToEuclidean
  let u := LOOConcentration.locallyLipschitzObservationPullback f hf.locallyLipschitz
  have hLaw : μ.map obs = ProbabilityTheory.stdGaussian E := by
    simpa [μ, obs, E] using LOOConcentration.gaussianObservationLaw_map_observationToEuclidean
  have hObsMeas : Measurable obs := by
    change Measurable (LOOConcentration.observationToEuclidean :
      LOOConcentration.Observation 1 1 → E)
    exact LOOConcentration.observationCoordinateContinuousLinearEquiv.continuous.measurable
  have hEuclidean := standardGaussian_observation_boundedLipschitz_square_logSobolev
    hf hbounded
  have hSquareMapped : Integrable (fun x : E => (f x) ^ 2) (μ.map obs) := by
    rw [hLaw]
    exact hEuclidean.1
  have hLogMapped : Integrable
      (fun x : E => (f x) ^ 2 * Real.log ((f x) ^ 2)) (μ.map obs) := by
    rw [hLaw]
    exact hEuclidean.2.1
  have hSquareInt : Integrable (fun z => (u.1 z) ^ 2) μ := by
    change Integrable ((fun x : E => (f x) ^ 2) ∘ obs) μ
    have h := (integrable_map_measure hSquareMapped.aestronglyMeasurable
      hObsMeas.aemeasurable).mp
        hSquareMapped
    change Integrable ((fun x : E => (f x) ^ 2) ∘ obs) μ at h
    exact h
  have hLogInt : Integrable
      (fun z => (u.1 z) ^ 2 * Real.log ((u.1 z) ^ 2)) μ := by
    change Integrable
      ((fun x : E => (f x) ^ 2 * Real.log ((f x) ^ 2)) ∘ obs) μ
    have h := (integrable_map_measure hLogMapped.aestronglyMeasurable
      hObsMeas.aemeasurable).mp
        hLogMapped
    change Integrable
      ((fun x : E => (f x) ^ 2 * Real.log ((f x) ^ 2)) ∘ obs) μ at h
    exact h
  have hSlopeInt : Integrable
      (fun z => (LOOConcentration.observationLocalSlope u z) ^ 2) μ := by
    simpa [u, μ] using
      LOOConcentration.integrable_gaussianObservation_localSlope_sq K f hf
  have hEntropy :
      LOOConcentration.looconcentrationEntropy μ (fun z => (u.1 z) ^ 2) =
        LOOConcentration.looconcentrationEntropy (ProbabilityTheory.stdGaussian E)
          (fun x => (f x) ^ 2) := by
    unfold LOOConcentration.looconcentrationEntropy
    rw [← hLaw]
    have hSquareAEM : AEStronglyMeasurable (fun x : E => (f x) ^ 2)
        (μ.map obs) := hSquareMapped.aestronglyMeasurable
    have hLogAEM : AEStronglyMeasurable
        (fun x : E => (f x) ^ 2 * Real.log ((f x) ^ 2)) (μ.map obs) :=
      hLogMapped.aestronglyMeasurable
    rw [integral_map hObsMeas.aemeasurable hLogAEM,
      integral_map hObsMeas.aemeasurable hSquareAEM]
    rfl
  have hCoordEnergy (i : ObsIndex) :
      (∫ z, (LOOConcentration.euclideanCoordinateSectionDerivative f i (obs z)) ^ 2 ∂μ) =
        ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2
          ∂ProbabilityTheory.stdGaussian E := by
    have hstd := LOOConcentration.integrable_euclideanCoordinateSectionDerivative_sq K f hf i
    have hmapped : Integrable
        (fun x : E => (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2)
        (μ.map obs) := by
      rw [hLaw]
      exact hstd
    calc
      _ = ∫ x, (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2
          ∂(μ.map obs) := by
            symm
            exact integral_map hObsMeas.aemeasurable hmapped.aestronglyMeasurable
      _ = _ := by rw [hLaw]
  have hSlopeEnergy :
      (∫ z, (LOOConcentration.observationLocalSlope u z) ^ 2 ∂μ) =
        ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ProbabilityTheory.stdGaussian E := by
    calc
      _ = ∑ i : ObsIndex, ∫ z,
          (LOOConcentration.euclideanCoordinateSectionDerivative f i (obs z)) ^ 2 ∂μ := by
            simpa [u, μ, obs, E] using
              LOOConcentration.integral_gaussianObservation_localSlope_sq_eq_sum_coordinateDerivative_sq
                K f hf
      _ = ∑ i : ObsIndex, ∫ x,
          (LOOConcentration.euclideanCoordinateSectionDerivative f i x) ^ 2
            ∂ProbabilityTheory.stdGaussian E := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hCoordEnergy i
      _ = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ProbabilityTheory.stdGaussian E := by
            symm
            exact LOOConcentration.integral_fderiv_norm_sq_eq_sum_integral_coordinateDerivative_sq
              K f hf
  refine ⟨hSquareInt, hLogInt, hSlopeInt, ?_⟩
  rw [hEntropy, hSlopeEnergy]
  exact hEuclidean.2.2.2

#print axioms standardGaussian_observation_boundedLipschitz_square_logSobolev
#print axioms gaussianObservation_boundedLipschitz_pullback_square_logSobolev

end LOOConcentration.Examples

end
