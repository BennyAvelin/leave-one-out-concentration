import LOOConcentrationRevision.FunctionalInequalities.MollifiedGradientGrowth

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory InnerProductSpace Filter
open scoped ENNReal Convolution

/-- Fixed-radius clipped mollification has a single global bound for its value
and actual gradient, as required by the approved smooth generators. -/
theorem clipThenMollify_bounded_smooth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (R : NNReal)
    (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (clipThenMollify F R η) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
        |clipThenMollify F R η x| ≤ B ∧ ‖gradient (clipThenMollify F R η) x‖ ≤ B := by
  let E := EuclideanSpace ℝ ι
  let K : E → ℝ := ExistsContDiffBumpBase.w η
  let C : ℝ := (R : ℝ) * ∫ t, ‖fderiv ℝ K t‖ ∂(Measure.addHaar : Measure E)
  have hC : 0 ≤ C := mul_nonneg R.property (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨contDiff_clipThenMollify hF hη, max (R : ℝ) C,
    le_trans R.property (le_max_left _ _), ?_⟩
  intro x
  have hr := clipThenMollify_range (N := (R : ℝ)) hF R.property hη x
  have hg : ∀ y, |clipFunction (R : ℝ) F y| ≤ R := by
    intro y
    exact abs_le.mpr (clipValue_bounds R.property)
  have hk : ContDiff ℝ 1 K := (contDiff_contDiffBump_w η).of_le (by simp)
  have hc := gradient_convolution_uniform_bound K (clipFunction R F) hk
    (ExistsContDiffBumpBase.w_compact_support E hη) (continuous_clipFunction hF)
    R R.property hg x
  refine ⟨(abs_le.mpr hr).trans (le_max_left _ _), ?_⟩
  exact (show ‖gradient (clipThenMollify F R η) x‖ ≤ C from hc).trans (le_max_right _ _)

/-- Every positive-radius approximation is in the literal bounded-smooth image,
with the same function and gradient representatives. -/
theorem exists_smooth_pair_clipThenMollify {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (R : NNReal)
    (η : ℝ) (hη : 0 < η) :
    ∃ p : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ),
      p ∈ smoothSobolevPairs μ ∧
      (WithLp.ofLp p).1 =ᵐ[μ] clipThenMollify F R η ∧
      (WithLp.ofLp p).2 =ᵐ[μ] gradient (clipThenMollify F R η) := by
  obtain ⟨hsmooth, B, hB, hbound⟩ := clipThenMollify_bounded_smooth F hF R η hη
  let G := clipThenMollify F R η
  have hgradContinuous : Continuous (gradient G) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hsmooth.continuous_fderiv (by simp))
  let hf : MemLp G 2 μ := MemLp.of_bound hsmooth.continuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbound x).1)
  let hg : MemLp (gradient G) 2 μ := MemLp.of_bound hgradContinuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => (hbound x).2)
  refine ⟨WithLp.toLp 2 (hf.toLp G, hg.toLp (gradient G)),
    ⟨G, hsmooth, ⟨B, hB, hbound⟩, hf, hg, rfl⟩, ?_, ?_⟩
  · simpa only [WithLp.ofLp_toLp] using hf.coeFn_toLp
  · simpa only [WithLp.ofLp_toLp] using hg.coeFn_toLp

end LOOConcentration.Revision
