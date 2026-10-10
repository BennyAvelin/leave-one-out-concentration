import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Measurable representatives for parameterized Euclidean gradients

This file develops the source-level bridge for jointly measurable losses whose
data sections are locally Lipschitz almost everywhere in the parameter.  The
representative is built from coordinate difference quotients, so its
measurability does not require joint continuity.
-/

set_option autoImplicit false

namespace LOOConcentration.Correspondence

open Filter MeasureTheory
open scoped Topology
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/-- A coordinate difference quotient, with step `1 / (n + 1)`. -/
noncomputable def coordinateDifferenceQuotient (F : E × α → ℝ) (i : ι) (n : ℕ)
    (p : E × α) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    (F (p.1 + (((n + 1 : ℕ) : ℝ)⁻¹) • EuclideanSpace.single i (1 : ℝ), p.2) - F p)

/-- The pointwise filter limit of coordinate difference quotients, using the canonical
`limUnder` value at nonconvergence points. -/
noncomputable def coordinateDerivativeRepresentative (F : E × α → ℝ) (i : ι)
    (p : E × α) : ℝ :=
  Filter.limUnder atTop (coordinateDifferenceQuotient F i · p)

/-- A measurable candidate for the norm of the partial Euclidean gradient. -/
noncomputable def partialGradientNormRepresentative (F : E × α → ℝ) (p : E × α) : ℝ :=
  Real.sqrt (∑ i, coordinateDerivativeRepresentative F i p ^ 2)

theorem measurable_coordinateDifferenceQuotient [MeasurableSpace α] [MeasurableSpace E]
    [BorelSpace E]
    (F : E × α → ℝ) (hF : Measurable F)
    (i : ι) (n : ℕ) : Measurable (coordinateDifferenceQuotient F i n) := by
  let t : ℝ := (((n + 1 : ℕ) : ℝ)⁻¹)
  have hshift : Measurable (fun p : E × α => (p.1 + t • EuclideanSpace.single i (1 : ℝ), p.2)) :=
    (measurable_fst.add_const _).prodMk measurable_snd
  have hmove : Measurable (fun p : E × α => F (p.1 + t • EuclideanSpace.single i (1 : ℝ), p.2)) :=
    hF.comp hshift
  have hbase : Measurable (fun p : E × α => F p) := hF
  change Measurable (fun p : E × α =>
    ((n + 1 : ℕ) : ℝ) * (F (p.1 + t • EuclideanSpace.single i (1 : ℝ), p.2) - F p))
  exact measurable_const.mul (hmove.sub hbase)

theorem measurable_coordinateDerivativeRepresentative [MeasurableSpace α] [MeasurableSpace E]
    [BorelSpace E]
    (F : E × α → ℝ) (hF : Measurable F) (i : ι) :
    Measurable (coordinateDerivativeRepresentative F i) :=
  (MeasureTheory.StronglyMeasurable.limUnder fun n =>
    (measurable_coordinateDifferenceQuotient F hF i n).stronglyMeasurable).measurable

theorem measurable_partialGradientNormRepresentative [MeasurableSpace α] [MeasurableSpace E]
    [BorelSpace E]
    (F : E × α → ℝ) (hF : Measurable F) :
    Measurable (partialGradientNormRepresentative F) := by
  have hsum : Measurable (fun p : E × α =>
      ∑ i, coordinateDerivativeRepresentative F i p ^ 2) := by
    exact Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_coordinateDerivativeRepresentative F hF i).pow_const 2
  exact Real.continuous_sqrt.measurable.comp hsum

theorem coordinateDerivativeRepresentative_eq_fderiv (F : E × α → ℝ) (x : E) (z : α)
    (i : ι) (hF : DifferentiableAt ℝ (fun y : E => F (y, z)) x) :
    coordinateDerivativeRepresentative F i (x, z) =
      fderiv ℝ (fun y : E => F (y, z)) x (EuclideanSpace.single i (1 : ℝ)) := by
  let f : E → ℝ := fun y => F (y, z)
  let v : E := EuclideanSpace.single i (1 : ℝ)
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop 1 hcast)
  have hlim := hF.hasFDerivAt.lim_real v
  have hq : (fun n : ℕ => coordinateDifferenceQuotient F i n (x, z)) =
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        (f (x + (((n + 1 : ℕ) : ℝ)⁻¹) • v) - f x)) := by
    funext n
    rfl
  have hreal : Tendsto (fun n : ℕ => coordinateDifferenceQuotient F i n (x, z))
      atTop (𝓝 (fderiv ℝ f x v)) := by
    rw [hq]
    simpa only [smul_eq_mul, Function.comp_def, f] using hlim.comp hn
  exact hreal.limUnder_eq

theorem partialGradientNormRepresentative_eq_gradient_norm (F : E × α → ℝ) (x : E) (z : α)
    (hF : DifferentiableAt ℝ (fun y : E => F (y, z)) x) :
    partialGradientNormRepresentative F (x, z) =
      ‖gradient (fun y : E => F (y, z)) x‖ := by
  let f : E → ℝ := fun y => F (y, z)
  have hcoord (i : ι) : fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) = gradient f x i := by
    rw [← inner_gradient_left]
    change inner ℝ (gradient f x) (EuclideanSpace.single i (1 : ℝ)) = gradient f x i
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [partialGradientNormRepresentative, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change coordinateDerivativeRepresentative F i (x, z) ^ 2 = ‖gradient f x i‖ ^ 2
  rw [coordinateDerivativeRepresentative_eq_fderiv F x z i hF, hcoord i]
  simp

omit [DecidableEq ι] in
theorem locallyLipschitz_ae_differentiableAt (f : E → ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure E), DifferentiableAt ℝ f x := by
  have hlocal (n : ℕ) :
      LocallyLipschitzOn (Metric.closedBall (0 : E) (n : ℝ)) f :=
    LocallyLipschitzOn.mono hf.locallyLipschitzOn (Set.subset_univ _)
  have hae_ball (n : ℕ) : ∀ᵐ x ∂(volume : Measure E),
      x ∈ Metric.closedBall (0 : E) (n : ℝ) →
        DifferentiableWithinAt ℝ f (Metric.closedBall (0 : E) (n : ℝ)) x := by
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : E) (n : ℝ)) (hlocal n)
    exact hK.ae_differentiableWithinAt_of_mem
  have hae_all : ∀ᵐ x ∂(volume : Measure E), ∀ n : ℕ,
      x ∈ Metric.closedBall (0 : E) (n : ℝ) →
        DifferentiableWithinAt ℝ f (Metric.closedBall (0 : E) (n : ℝ)) x :=
    ae_all_iff.2 hae_ball
  filter_upwards [hae_all] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hxBall : x ∈ Metric.ball (0 : E) (n : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hn
  have hxClosed : x ∈ Metric.closedBall (0 : E) (n : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hn.le
  exact (hx n hxClosed).differentiableAt
    (Metric.closedBall_mem_nhds_of_mem hxBall)

theorem locallyLipschitz_section_ae_nativeGradient_bound (F : E × α → ℝ) (xBound : E → ℝ)
    (z : α) (hF : LocallyLipschitz (fun y : E => F (y, z)))
    (hbound : ∀ᵐ y ∂(volume : Measure E),
      partialGradientNormRepresentative F (y, z) ≤ xBound y) :
    ∀ᵐ y ∂(volume : Measure E),
      DifferentiableAt ℝ (fun y : E => F (y, z)) y ∧
        ‖gradient (fun y : E => F (y, z)) y‖ ≤ xBound y := by
  filter_upwards [locallyLipschitz_ae_differentiableAt (fun y => F (y, z)) hF, hbound]
    with y hy hb
  refine ⟨hy, ?_⟩
  rw [← partialGradientNormRepresentative_eq_gradient_norm F y z hy]
  exact hb

theorem nativeGradient_ae_bound_to_representative_ae_bound (F : E × α → ℝ)
    (xBound : E → ℝ) (z : α)
    (hbound : ∀ᵐ y ∂(volume : Measure E),
      DifferentiableAt ℝ (fun y : E => F (y, z)) y ∧
        ‖gradient (fun y : E => F (y, z)) y‖ ≤ xBound y) :
    ∀ᵐ y ∂(volume : Measure E),
      partialGradientNormRepresentative F (y, z) ≤ xBound y := by
  filter_upwards [hbound] with y hy
  rw [partialGradientNormRepresentative_eq_gradient_norm F y z hy.1]
  exact hy.2

end LOOConcentration.Correspondence
