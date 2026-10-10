import LOOConcentrationRevision.FunctionalInequalities.MollifiedGradientGrowth
import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator
import LOOConcentrationRevision.Analysis.CenteredFatouLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration.Revision

/-- The source radius sequence, represented in the exact nonnegative cap type
expected by clipThenMollify. -/
def normApproximationCap (j : ℕ) : NNReal :=
  ⟨(j : ℝ) + 1, by positivity⟩

/-- The source mollifier radius, tending to zero independently of the cap. -/
noncomputable def normApproximationRadius (j : ℕ) : ℝ :=
  ((j : ℝ) + 1)⁻¹

/-- The literal source approximation of the Euclidean norm. -/
noncomputable def normClipThenMollify {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) : EuclideanSpace ℝ ι → ℝ :=
  clipThenMollify (fun x : EuclideanSpace ℝ ι => ‖x‖)
    (normApproximationCap j) (normApproximationRadius j)

theorem normApproximationRadius_pos (j : ℕ) :
    0 < normApproximationRadius j := by
  dsimp [normApproximationRadius]
  positivity

theorem normApproximationRadius_le_one (j : ℕ) :
    normApproximationRadius j ≤ 1 := by
  dsimp [normApproximationRadius]
  have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  rw [inv_le_one₀ (by positivity)]
  exact hden

theorem normApproximationRadius_tendsto_zero :
    Tendsto normApproximationRadius atTop (𝓝 0) := by
  change Tendsto ((fun x : ℝ => x⁻¹) ∘
    (fun j : ℕ => (j : ℝ) + 1)) atTop (𝓝 0)
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp hden

/-- Every member of the actual clipped-convolution sequence is globally
smooth and bounded. -/
theorem normClipThenMollify_bounded_smooth
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (normClipThenMollify (ι := ι) j) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
        |normClipThenMollify (ι := ι) j x| ≤ B ∧
        ‖gradient (normClipThenMollify (ι := ι) j) x‖ ≤ B := by
  exact clipThenMollify_bounded_smooth
    (fun x : EuclideanSpace ℝ ι => ‖x‖) continuous_norm
    (normApproximationCap j) (normApproximationRadius j)
    (normApproximationRadius_pos j)

/-- The actual gradient of every approximant has norm at most one. The
endpoint-average segment estimate for the literal norm is derived internally. -/
theorem normClipThenMollify_gradient_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ)
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (normClipThenMollify (ι := ι) j) x‖ ≤ 1 := by
  have hseg : HasLinearGrowthSegmentBound
      (fun y : EuclideanSpace ℝ ι => ‖y‖) 1 0 := by
    intro y z
    simpa [dist_eq_norm] using abs_norm_sub_norm_le y z
  have h := clipThenMollify_gradient_growth
    (fun y : EuclideanSpace ℝ ι => ‖y‖) continuous_norm
    1 0 (normApproximationCap j : ℝ) (normApproximationRadius j)
    (normApproximationRadius_pos j) hseg x
  simpa [normClipThenMollify, normApproximationRadius,
    normApproximationCap] using h

/-- Pointwise convergence of the actual clipped mollifications to the
untruncated norm, with the source caps and radii fixed above. -/
theorem normClipThenMollify_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun j => normClipThenMollify (ι := ι) j x) atTop (𝓝 ‖x‖) := by
  have hclip := clipValueSequence_tendsto
    (fun y : EuclideanSpace ℝ ι => ‖y‖) x
  have hclose (j : ℕ) :
      |normClipThenMollify (ι := ι) j x -
        clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| ≤
          normApproximationRadius j := by
    have hseg : HasLinearGrowthSegmentBound
        (clipFunction (normApproximationCap j : ℝ)
          (fun y : EuclideanSpace ℝ ι => ‖y‖)) 1 0 :=
      clipFunction_segmentBound (by
        intro y z
        simpa [dist_eq_norm] using abs_norm_sub_norm_le y z)
    have h := clipThenMollify_close
      (f := fun y : EuclideanSpace ℝ ι => ‖y‖)
      (N := (normApproximationCap j : ℝ))
      (η := normApproximationRadius j) (a := 1) (b := 0)
      continuous_norm (normApproximationRadius_pos j) hseg
      (by norm_num) (by norm_num) x
    have hfun : clipFunction (normApproximationCap j : ℝ)
        (fun y : EuclideanSpace ℝ ι => ‖y‖) =
          clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j := by
      funext y
      rfl
    rw [hfun] at h
    simpa [normClipThenMollify, normApproximationRadius] using h
  have herr_norm : Tendsto
      (fun j => ‖normClipThenMollify (ι := ι) j x -
        clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x‖)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun j => norm_nonneg _)
      (fun j => by rw [Real.norm_eq_abs]; exact hclose j)
      normApproximationRadius_tendsto_zero
  have herr : Tendsto
      (fun j => normClipThenMollify (ι := ι) j x -
        clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x)
      atTop (𝓝 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa using herr_norm)
  have hsum := herr.add hclip
  simpa using hsum

/-- Under a probability law with finite second moment, the squared error of
the source-faithful norm approximants has integral tending to zero. The
integrable domination is derived from the clip contraction and mollifier
close estimate. -/
theorem normClipThenMollify_L2_error_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ) :
    Tendsto (fun j => ∫ x,
      (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2 ∂μ) atTop (𝓝 0) := by
  let bound : EuclideanSpace ℝ ι → ℝ := fun x => 2 + 2 * ‖x‖ ^ 2
  have hboundInt : Integrable bound μ := by
    dsimp [bound]
    exact (integrable_const (2 : ℝ)).add (hmoment.const_mul (2 : ℝ))
  have hcont (j : ℕ) : Continuous (normClipThenMollify (ι := ι) j) :=
    ((normClipThenMollify_bounded_smooth (ι := ι) j).1).continuous
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (fun x => (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2) μ :=
    (((hcont j).sub continuous_norm).pow 2).aestronglyMeasurable
  have herr_bound (j : ℕ) (x : EuclideanSpace ℝ ι) :
      ‖(normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2‖ ≤ bound x := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hclose (j : ℕ) :
        |normClipThenMollify (ι := ι) j x -
          clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| ≤
            normApproximationRadius j := by
      have hseg : HasLinearGrowthSegmentBound
          (clipFunction (normApproximationCap j : ℝ)
            (fun y : EuclideanSpace ℝ ι => ‖y‖)) 1 0 :=
        clipFunction_segmentBound (by
          intro y z
          simpa [dist_eq_norm] using abs_norm_sub_norm_le y z)
      have h := clipThenMollify_close
        (f := fun y : EuclideanSpace ℝ ι => ‖y‖)
        (N := (normApproximationCap j : ℝ))
        (η := normApproximationRadius j) (a := 1) (b := 0)
        continuous_norm (normApproximationRadius_pos j) hseg
        (by norm_num) (by norm_num) x
      have hfun : clipFunction (normApproximationCap j : ℝ)
          (fun y : EuclideanSpace ℝ ι => ‖y‖) =
            clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j := by
        funext y
        rfl
      rw [hfun] at h
      simpa [normClipThenMollify, normApproximationRadius] using h
    have hclip : |clipValueSequence
        (fun y : EuclideanSpace ℝ ι => ‖y‖) j x - ‖x‖| ≤ ‖x‖ := by
      have hA : 0 ≤ (j : ℝ) + 1 := by positivity
      have hu : 0 ≤ ‖x‖ := norm_nonneg x
      have hc0 : 0 ≤ clipValue ((j : ℝ) + 1) ‖x‖ := by
        change 0 ≤ max (-((j : ℝ) + 1)) (min ‖x‖ ((j : ℝ) + 1))
        exact le_trans (le_min hu hA) (le_max_right _ _)
      have hcle : clipValue ((j : ℝ) + 1) ‖x‖ ≤ ‖x‖ := by
        change max (-((j : ℝ) + 1)) (min ‖x‖ ((j : ℝ) + 1)) ≤ ‖x‖
        exact max_le (by linarith) (min_le_left _ _)
      change |clipValue ((j : ℝ) + 1) ‖x‖ - ‖x‖| ≤ ‖x‖
      rw [abs_of_nonpos (sub_nonpos.mpr hcle)]
      linarith
    have hdiff : |normClipThenMollify (ι := ι) j x - ‖x‖| ≤ 1 + ‖x‖ := by
      calc
        _ ≤ |normClipThenMollify (ι := ι) j x -
            clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x| +
              |clipValueSequence (fun y : EuclideanSpace ℝ ι => ‖y‖) j x - ‖x‖| :=
          abs_sub_le _ _ _
        _ ≤ normApproximationRadius j + ‖x‖ :=
          add_le_add (hclose j) hclip
        _ ≤ 1 + ‖x‖ := add_le_add (normApproximationRadius_le_one j) le_rfl
    have hprod : (1 + ‖x‖) ^ 2 ≤ 2 + 2 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - 1)]
    have herrsq :
        (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2 ≤
          (1 + ‖x‖) ^ 2 := by
      have ha0 : 0 ≤ |normClipThenMollify (ι := ι) j x - ‖x‖| :=
        abs_nonneg _
      have hB0 : 0 ≤ 1 + ‖x‖ := by positivity
      have hmul₁ := mul_le_mul_of_nonneg_left hdiff ha0
      have hmul₂ := mul_le_mul_of_nonneg_right hdiff hB0
      calc
        (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2 =
            |normClipThenMollify (ι := ι) j x - ‖x‖| ^ 2 := by
          rw [sq_abs]
        _ = |normClipThenMollify (ι := ι) j x - ‖x‖| *
            |normClipThenMollify (ι := ι) j x - ‖x‖| := by ring
        _ ≤ |normClipThenMollify (ι := ι) j x - ‖x‖| * (1 + ‖x‖) := hmul₁
        _ ≤ (1 + ‖x‖) * (1 + ‖x‖) := hmul₂
        _ = (1 + ‖x‖) ^ 2 := by ring
    exact herrsq.trans hprod
  have hpoint (x : EuclideanSpace ℝ ι) :
      Tendsto (fun j =>
        (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2) atTop (𝓝 0) := by
    have hsub : Tendsto
        (fun j => normClipThenMollify (ι := ι) j x - ‖x‖) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖) :=
        tendsto_const_nhds
      simpa using (normClipThenMollify_tendsto x).sub hc
    have hsq := (continuous_pow 2).continuousAt.tendsto.comp hsub
    change Tendsto
      (fun j => (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2)
      atTop (𝓝 ((0 : ℝ) ^ 2)) at hsq
    simpa using hsq
  have h := tendsto_integral_of_dominated_convergence
    (bound := bound) (F := fun j x => (normClipThenMollify (ι := ι) j x - ‖x‖) ^ 2)
    (f := fun _ : EuclideanSpace ℝ ι => (0 : ℝ))
    (fun j => hmeas j) hboundInt
    (fun j => Filter.Eventually.of_forall (herr_bound j))
    (Filter.Eventually.of_forall hpoint)
  simpa [bound] using h

#print axioms normClipThenMollify_gradient_bound
#print axioms normClipThenMollify_tendsto
#print axioms normClipThenMollify_L2_error_tendsto

end LOOConcentration.Revision
