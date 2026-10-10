import LOOConcentrationRevision.FunctionalInequalities.MollifiedScalarLimit
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.FunctionalInequalities.JointLimitAdmission

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Full bounded-truncation admission from the source premises. All approximation,
scalar-limit, joint boundedness, weak-limit and generator inputs are produced here. -/
theorem bounded_truncation_admission_of_ae_gradient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hloc : LocallyLipschitz F) (a b R : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖) :
    ∃ u : SobolevPair μ,
      ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ]
        (fun x => max (-(R : ℝ)) (min (F x) (R : ℝ))) ∧
      ∀ᵐ x ∂μ,
        ‖((WithLp.ofLp u.val).2 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤
          (a : ℝ) + (b : ℝ) * ‖x‖ := by
  have hseg := ae_gradient_segment_estimate F hloc a b hgrad
  obtain ⟨hclip, f, hf, hs, hg, hstrong⟩ :=
    exists_scalar_strongL2_clipThenMollify μ hmoment F hloc.continuous a b R hseg
  have hη (n : ℕ) : 0 < mollificationRadius n ∧ mollificationRadius n ≤ 1 := by
    constructor
    · dsimp [mollificationRadius]
      positivity
    · dsimp [mollificationRadius]
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨B, hB⟩ := exists_uniform_joint_bound_clipThenMollify μ hmoment
    F hloc.continuous a b R hseg mollificationRadius hη f hs hg
  let q : EuclideanSpace ℝ ι → ℝ := fun x => (a : ℝ) + (b : ℝ) * ‖x‖
  let err : ℕ → ℝ := fun n => (b : ℝ) * mollificationRadius n
  have hηzero : Tendsto mollificationRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have herr : Tendsto err atTop (nhds 0) := by
    simpa only [mul_zero] using hηzero.const_mul (b : ℝ)
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖(WithLp.ofLp (f n)).2 x‖ ≤ q x + err n := by
    filter_upwards [hg n] with x hx
    rw [hx]
    have hb := clipThenMollify_gradient_growth F hloc.continuous a b R
      (mollificationRadius n) (hη n).1 hseg x
    convert hb using 1
    dsimp [q, err]
    ring
  obtain ⟨u, hu, hgu⟩ := exists_sobolevPair_of_bounded_generators_with_gradient_bound
    μ f B hB hf (hclip.toLp (clipFunction (R : ℝ) F)) hstrong q err herr hbound
  refine ⟨u, ?_, hgu⟩
  rw [hu]
  exact hclip.coeFn_toLp

end LOOConcentration.Revision
