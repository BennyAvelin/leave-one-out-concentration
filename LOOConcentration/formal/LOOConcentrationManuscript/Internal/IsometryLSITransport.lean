import LOOConcentrationRevision.FunctionalInequalities.GeneratorLSIClosure
import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped ENNReal

private theorem norm_gradient_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (F : E → ℝ) (x : E) :
    ‖gradient F x‖ = ‖fderiv ℝ F x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _

private theorem gradient_comp_linearIsometry_norm_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (F : EuclideanSpace ℝ κ → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (e : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (fun z => F (e z)) x‖ ≤ ‖gradient F (e x)‖ := by
  have hcomp : fderiv ℝ (fun z : EuclideanSpace ℝ ι => F (e z)) x =
      (fderiv ℝ F (e x)).comp e.toContinuousLinearMap := by
    change fderiv ℝ (F ∘ (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)) x = _
    calc
      _ = (fderiv ℝ F (e x)).comp
          (fderiv ℝ (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) x) :=
        fderiv_comp (f := (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ))
          (x := x) ((hF.differentiable (by simp)).differentiableAt)
          e.toContinuousLinearMap.differentiableAt
      _ = _ := by
        congr 1
        exact e.toContinuousLinearMap.fderiv
  calc
    ‖gradient (fun z => F (e z)) x‖ =
        ‖(fderiv ℝ F (e x)).comp e.toContinuousLinearMap‖ := by
      rw [gradient, hcomp, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
    _ ≤ ‖fderiv ℝ F (e x)‖ * ‖e.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F (e x)‖ * 1 :=
      mul_le_mul_of_nonneg_left e.norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = ‖gradient F (e x)‖ := by rw [mul_one, ← norm_gradient_eq_fderiv]

private theorem integrable_sq_norm_of_continuous_bound
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure α) [TopologicalSpace α] [OpensMeasurableSpace α] [IsFiniteMeasure μ]
    (f : α → E) (hf : Continuous f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun x => ‖f x‖ ^ 2) μ := by
  refine Integrable.of_bound ((continuous_norm.comp hf).measurable.pow_const 2).aestronglyMeasurable
    (B ^ 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x)

private theorem gradient_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    Continuous (gradient F) := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
    (hF.continuous_fderiv (by simp))

/-- An actual linear isometric padding cannot increase the native completed
log-Sobolev constant. The generator estimate is produced from the true smooth
pullback and the contraction of its gradient. -/
theorem logSobolevConstant_map_linearIsometry_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (e : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    letI : IsProbabilityMeasure (μ.map e) :=
      μ.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
    LOOConcentration.Revision.logSobolevConstant (μ.map e) ≤
      LOOConcentration.Revision.logSobolevConstant μ := by
  let ν := μ.map e
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  change LOOConcentration.Revision.logSobolevConstant ν ≤
    LOOConcentration.Revision.logSobolevConstant μ
  by_cases htop : LOOConcentration.Revision.logSobolevConstant μ = ⊤
  · rw [htop]
    exact le_top
  · let C := (LOOConcentration.Revision.logSobolevConstant μ).toReal
    have hfinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hC : 0 ≤ C := ENNReal.toReal_nonneg
    have hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C := by
      change LOOConcentration.Revision.logSobolevConstant μ ≤
        ENNReal.ofReal (LOOConcentration.Revision.logSobolevConstant μ).toReal
      rw [ENNReal.ofReal_toReal hfinite.ne]
    have hGenerator : ∀ (F : EuclideanSpace ℝ κ → ℝ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ∀ B : ℝ, 0 ≤ B → (∀ y, |F y| ≤ B ∧ ‖gradient F y‖ ≤ B) →
        LOOConcentration.entropy ν (fun y => (F y)^2) ≤
          2 * C * ∫ y, ‖gradient F y‖^2 ∂ν := by
      intro F hF B hB hbound
      let G : EuclideanSpace ℝ ι → ℝ := fun x => F (e x)
      have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
        change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (F ∘ (e.toContinuousLinearMap : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ))
        exact hF.comp_continuousLinearMap
      have hGbound (x : EuclideanSpace ℝ ι) :
          |G x| ≤ B ∧ ‖gradient G x‖ ≤ B := by
        constructor
        · exact (hbound (e x)).1
        · exact (gradient_comp_linearIsometry_norm_le F hF e x).trans (hbound (e x)).2
      obtain ⟨M, hM0, hM⟩ :=
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (B ^ 2))).bddAbove_image
          (continuous_norm.comp Real.continuous_mul_log).continuousOn |>.exists_ge 0
      have hFsq (y : EuclideanSpace ℝ κ) : (F y)^2 ≤ B^2 := by
        rw [sq_le_sq, abs_of_nonneg hB]
        exact (hbound y).1
      have hSqInt : Integrable (fun y : EuclideanSpace ℝ κ => (F y)^2) ν := by
        refine Integrable.of_bound (hF.continuous.measurable.pow_const 2).aestronglyMeasurable
          (B ^ 2) ?_
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFsq y
      have hLogInt : Integrable (fun y : EuclideanSpace ℝ κ =>
          (F y)^2 * Real.log ((F y)^2)) ν := by
        refine Integrable.of_bound
          (Real.continuous_mul_log.measurable.comp (hF.continuous.measurable.pow_const 2)).aestronglyMeasurable
          M ?_
        filter_upwards with y
        exact hM _ ⟨(F y)^2, ⟨sq_nonneg _, hFsq y⟩, rfl⟩
      have hGradFCont := gradient_continuous F hF
      have hGradFInt := integrable_sq_norm_of_continuous_bound ν (gradient F)
        hGradFCont B hB (fun y => (hbound y).2)
      have hGradGCont : Continuous (gradient G) := gradient_continuous G hG
      have hGradGInt := integrable_sq_norm_of_continuous_bound μ (gradient G)
        hGradGCont B hB (fun x => hGbound x |>.2)
      have hGradPullCont : Continuous (fun x : EuclideanSpace ℝ ι => gradient F (e x)) :=
        hGradFCont.comp e.continuous
      have hGradPullInt := integrable_sq_norm_of_continuous_bound μ
        (fun x : EuclideanSpace ℝ ι => gradient F (e x)) hGradPullCont B hB
        (fun x => (hbound (e x)).2)
      have hEnergyMap :
          (∫ y, ‖gradient F y‖^2 ∂ν) =
            ∫ x, ‖gradient F (e x)‖^2 ∂μ := by
        exact integral_map e.continuous.measurable.aemeasurable
          hGradFInt.aestronglyMeasurable
      have hEnergyLe :
          (∫ x, ‖gradient G x‖^2 ∂μ) ≤
            ∫ y, ‖gradient F y‖^2 ∂ν := by
        calc
          (∫ x, ‖gradient G x‖^2 ∂μ) ≤
              ∫ x, ‖gradient F (e x)‖^2 ∂μ := by
            apply integral_mono hGradGInt hGradPullInt
            intro x
            exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
              (gradient_comp_linearIsometry_norm_le F hF e x)
          _ = ∫ y, ‖gradient F y‖^2 ∂ν := hEnergyMap.symm
      have hEntropyMap :
          LOOConcentration.entropy ν (fun y => (F y)^2) =
            LOOConcentration.entropy μ (fun x => (G x)^2) := by
        unfold LOOConcentration.entropy
        rw [integral_map e.continuous.measurable.aemeasurable hLogInt.aestronglyMeasurable,
          integral_map e.continuous.measurable.aemeasurable hSqInt.aestronglyMeasurable]
      have hBase :=
        LOOConcentration.Revision.bounded_smooth_entropy_le_of_logSobolevConstant_le
          μ C hC hLC G hG B hB hGbound
      change LOOConcentration.entropy μ (fun x => (G x)^2) ≤
          2 * C * ∫ x, ‖gradient G x‖^2 ∂μ at hBase
      rw [hEntropyMap]
      exact hBase.trans (mul_le_mul_of_nonneg_left hEnergyLe (by positivity))
    have h := LOOConcentration.Revision.logSobolevConstant_le_of_bounded_generator_bound
      ν C hC hGenerator
    simpa only [C, ENNReal.ofReal_toReal hfinite.ne] using h

end LOOConcentration.Manuscript.Internal
