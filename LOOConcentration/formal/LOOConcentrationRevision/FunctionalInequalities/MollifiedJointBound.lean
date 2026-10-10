import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A finite second moment supplies the actual L² affine growth majorant. -/
theorem memLp_affine_norm_of_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x => ‖x‖ ^ 2) μ) (a b : NNReal) :
    MemLp (fun x => (a : ℝ) + (b : ℝ) + (b : ℝ) * ‖x‖) 2 μ := by
  have hn : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) 2 μ :=
    (memLp_two_iff_integrable_sq continuous_norm.aestronglyMeasurable).mpr hmoment
  exact (memLp_const ((a : ℝ) + (b : ℝ))).add (hn.const_mul (b : ℝ))

/-- A single joint Hilbert norm is bounded by the two component norms. -/
theorem joint_lp_norm_le_sum {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] (μ : Measure α)
    (p : WithLp 2 (Lp ℝ 2 μ × Lp E 2 μ)) :
    ‖p‖ ≤ ‖(WithLp.ofLp p).1‖ + ‖(WithLp.ofLp p).2‖ := by
  have heq : p = WithLp.toLp 2 ((WithLp.ofLp p).1, (0 : Lp E 2 μ)) +
      WithLp.toLp 2 ((0 : Lp ℝ 2 μ), (WithLp.ofLp p).2) := by
    apply (WithLp.ofLp_injective 2)
    simp only [WithLp.ofLp_add, Prod.mk_add_mk,
      add_zero, zero_add, Prod.mk.eta]
  calc
    ‖p‖ ≤ ‖WithLp.toLp 2 ((WithLp.ofLp p).1, (0 : Lp E 2 μ))‖ +
        ‖WithLp.toLp 2 ((0 : Lp ℝ 2 μ), (WithLp.ofLp p).2)‖ := by
      conv_lhs => rw [heq]
      exact norm_add_le _ _
    _ = _ := by rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd]

/-- The actual fixed-radius approximants have a uniform JOINT bound when their
radii are at most one. Their scalar and gradient representatives stay paired. -/
theorem exists_uniform_joint_bound_clipThenMollify {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (a b R : NNReal)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)))
    (η : ℕ → ℝ) (hη : ∀ n, 0 < η n ∧ η n ≤ 1)
    (f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
    (hs : ∀ n, (WithLp.ofLp (f n)).1 =ᵐ[μ] clipThenMollify F R (η n))
    (hg : ∀ n, (WithLp.ofLp (f n)).2 =ᵐ[μ] gradient (clipThenMollify F R (η n))) :
    ∃ B : ℝ, ∀ n, ‖f n‖ ≤ B := by
  let q : EuclideanSpace ℝ ι → ℝ := fun x => (a : ℝ) + (b : ℝ) + (b : ℝ) * ‖x‖
  let hq : MemLp q 2 μ := memLp_affine_norm_of_second_moment μ hmoment a b
  let Q : Lp ℝ 2 μ := hq.toLp q
  refine ⟨(R : ℝ) + ‖Q‖, ?_⟩
  intro n
  have hscalar : ‖(WithLp.ofLp (f n)).1‖ ≤ R := by
    have hb := Lp.norm_le_of_ae_bound R.property (f := (WithLp.ofLp (f n)).1) ?_
    · simpa [measureUnivNNReal] using hb
    · filter_upwards [hs n] with x hx
      rw [hx, Real.norm_eq_abs]
      exact abs_le.mpr (clipThenMollify_range hF R.property (hη n).1 x)
  have hgradient : ‖(WithLp.ofLp (f n)).2‖ ≤ ‖Q‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hg n, hq.coeFn_toLp] with x hx hQ
    rw [hx, hQ, Real.norm_eq_abs, abs_of_nonneg (by dsimp [q]; positivity)]
    have h := clipThenMollify_gradient_growth F hF a b R (η n) (hη n).1 hseg x
    dsimp [q]
    apply h.trans
    gcongr
    exact (mul_le_mul_of_nonneg_left (hη n).2 b.property).trans_eq (mul_one _)
  exact (joint_lp_norm_le_sum μ (f n)).trans (add_le_add hscalar hgradient)

end LOOConcentration.Revision
