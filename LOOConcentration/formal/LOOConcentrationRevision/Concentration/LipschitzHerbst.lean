import LOOConcentrationRevision.Concentration.BoundedSmoothHerbst
import LOOConcentrationRevision.Analysis.CenteredFatouLimit
import LOOConcentration.Analysis.ClipMollify
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology

/-- The bounded smooth MGF estimate passes to the same integrable globally
Lipschitz function through its actual clipped mollifications. -/
theorem lipschitz_centered_exp_integrable_and_mgf_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal)
    (hLip : LipschitzWith L F) (hF : Integrable F μ) (lam : ℝ) :
    Integrable (fun x => Real.exp (lam * (F x - ∫ y, F y ∂μ))) μ ∧
      (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
        Real.exp ((C * (L : ℝ)^2 / 2) * lam^2) := by
  let η : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let f : ℕ → EuclideanSpace ℝ ι → ℝ := fun j =>
    LOOConcentration.clipThenMollify F ((j : ℝ) + 1) (η j)
  have hη (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hηlim : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (L : ℝ) + (0 : NNReal) * ‖x‖ := by
    simpa only [NNReal.coe_zero, zero_mul, add_zero] using
      lipschitzWith_ae_differentiableAt_gradient_norm_le hLip
  have hseg : LOOConcentration.HasLinearGrowthSegmentBound F (L : ℝ) 0 := by
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_zero] using
      ae_gradient_segment_estimate F hLip.locallyLipschitz L 0 hgrad x y
  have hclipseg (j : ℕ) := LOOConcentration.clipFunction_segmentBound
    (N := (j : ℝ) + 1) hseg
  have hsmooth (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) :=
    LOOConcentration.contDiff_clipThenMollify hLip.continuous (hη j)
  have hb (j : ℕ) (x : EuclideanSpace ℝ ι) : |f j x| ≤ (j : ℝ) + 1 :=
    abs_le.mpr (LOOConcentration.clipThenMollify_range hLip.continuous
      (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) (hη j) x)
  have hg (j : ℕ) (x : EuclideanSpace ℝ ι) : ‖gradient (f j) x‖ ≤ L := by
    rw [show ‖gradient (f j) x‖ = ‖fderiv ℝ (f j) x‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map _]
    simpa only [zero_mul, add_zero] using
      LOOConcentration.clipThenMollify_fderiv_bound hLip.continuous (hη j)
        (hclipseg j) L.property (by norm_num : (0 : ℝ) ≤ 0) x
  have hf (j : ℕ) : Integrable (f j) μ := by
    apply Integrable.of_bound (hsmooth j).continuous.aestronglyMeasurable ((j : ℝ) + 1)
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb j x
  have hcl (j : ℕ) (x : EuclideanSpace ℝ ι) :
      |f j x - LOOConcentration.clipValueSequence F j x| ≤ η j * (L : ℝ) := by
    simpa only [f, LOOConcentration.clipFunction, LOOConcentration.clipValueSequence,
      zero_mul, zero_div, add_zero] using
      LOOConcentration.clipThenMollify_close hLip.continuous (hη j) (hclipseg j)
        L.property (by norm_num : (0 : ℝ) ≤ 0) x
  have hL1 : Tendsto (fun j => ∫ x, |f j x - F x| ∂μ) atTop (𝓝 0) := by
    have hupper (j : ℕ) :
        (∫ x, |f j x - F x| ∂μ) ≤ η j * (L : ℝ) +
          ∫ x, |LOOConcentration.clipValueSequence F j x - F x| ∂μ := by
      have hcapInt : Integrable (LOOConcentration.clipValueSequence F j) μ := by
        apply Integrable.of_bound
          ((LOOConcentration.continuous_clipValue ((j : ℝ) + 1)).comp_aestronglyMeasurable hF.1)
          ((j : ℝ) + 1)
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr (LOOConcentration.clipValue_bounds (by positivity))
      have heInt := (hcapInt.sub hF).norm
      have heInt' : Integrable (fun x => |LOOConcentration.clipValueSequence F j x - F x|) μ :=
        heInt
      calc
        _ ≤ ∫ x, η j * (L : ℝ) + |LOOConcentration.clipValueSequence F j x - F x| ∂μ := by
          apply integral_mono ((hf j).sub hF).norm ((integrable_const _).add heInt')
          intro x
          calc
            |f j x - F x| ≤ |f j x - LOOConcentration.clipValueSequence F j x| +
                |LOOConcentration.clipValueSequence F j x - F x| := abs_sub_le _ _ _
            _ ≤ _ := add_le_add (hcl j x) le_rfl
        _ = _ := by rw [integral_add (integrable_const _) heInt', integral_const]; simp
    have hu := (hηlim.mul_const (L : ℝ)).add (LOOConcentration.clipValueSequence_L1_tendsto hF)
    exact squeeze_zero (fun j => integral_nonneg fun x => abs_nonneg _) hupper (by simpa using hu)
  let B := ENNReal.ofReal (Real.exp ((C * (L : ℝ)^2 / 2) * lam^2))
  have hbound (j : ℕ) : ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (f j x - ∫ y, f j y ∂μ))) ∂μ ≤ B := by
    have h := bounded_smooth_centered_exp_integrable_and_mgf_le μ C hC hLC
      (f j) (hsmooth j) ((j : ℝ) + 1) L (by positivity) L.property
      (hb j) (hg j) lam
    rw [← ofReal_integral_eq_lintegral_ofReal h.1
      (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h.2
  have hlim := centeredExp_le_of_L1_tendsto hf hF hL1 lam B hbound
  have hmeas : Measurable (fun x => Real.exp (lam * (F x - ∫ y, F y ∂μ))) :=
    (measurable_const.mul (hLip.continuous.measurable.sub measurable_const)).exp
  have hInt : Integrable (fun x => Real.exp (lam * (F x - ∫ y, F y ∂μ))) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
    exact hlim.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)] at hlim
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp hlim

end LOOConcentration.Revision
