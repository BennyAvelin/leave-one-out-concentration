import LOOConcentrationRevision.Concentration.SourceSegmentIntegrability
import LOOConcentrationRevision.FunctionalInequalities.MollifiedScalarLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory Filter
open scoped Topology

/-- From the source gradient hypothesis, the actual fixed-cap mollifications are
integrable and converge pointwise, in `L¹`, and in mean to the clipped source
function. The segment estimate and original integrability are produced internally. -/
theorem source_clipThenMollify_L1_and_mean_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hloc : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖) :
    Integrable F μ ∧ ∀ R : NNReal,
      (∀ j, Integrable (clipThenMollify F (R : ℝ) (mollificationRadius j)) μ) ∧
      Integrable (clipFunction (R : ℝ) F) μ ∧
      Tendsto (fun j => ∫ x,
        |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x| ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ x,
        clipThenMollify F (R : ℝ) (mollificationRadius j) x ∂μ) atTop
        (𝓝 (∫ x, clipFunction (R : ℝ) F x ∂μ)) ∧
      ∀ x, Tendsto (fun j =>
        clipThenMollify F (R : ℝ) (mollificationRadius j) x) atTop
        (𝓝 (clipFunction (R : ℝ) F x)) := by
  obtain ⟨hseg, hFint⟩ := source_segment_estimate_and_integrable μ hM2 F hloc a b hgrad
  have hFcont : Continuous F := hloc.continuous
  have hηpos (j : ℕ) : 0 < mollificationRadius j := by
    dsimp [mollificationRadius]
    positivity
  have hηzero : Tendsto mollificationRadius atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsegF : HasLinearGrowthSegmentBound F (a : ℝ) (b : ℝ) := by
    intro x y
    simpa only [dist_eq_norm] using hseg x y
  have ha : 0 ≤ (a : ℝ) := a.property
  have hb : 0 ≤ (b : ℝ) := b.property
  refine ⟨hFint, ?_⟩
  intro R
  have hclipSeg : HasLinearGrowthSegmentBound (clipFunction (R : ℝ) F)
      (a : ℝ) (b : ℝ) := clipFunction_segmentBound hsegF
  have hclipCont : Continuous (clipFunction (R : ℝ) F) := continuous_clipFunction hFcont
  have hclipInt : Integrable (clipFunction (R : ℝ) F) μ := by
    apply (integrable_const (R : ℝ)).mono' hclipCont.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (clipValue_bounds R.property)
  have happCont (j : ℕ) : Continuous
      (clipThenMollify F (R : ℝ) (mollificationRadius j)) :=
    (contDiff_clipThenMollify hFcont (hηpos j)).continuous
  have happRange (j : ℕ) (x : EuclideanSpace ℝ ι) :
      |clipThenMollify F (R : ℝ) (mollificationRadius j) x| ≤ (R : ℝ) := by
    rw [abs_le]
    exact clipThenMollify_range hFcont R.property (hηpos j) x
  have happInt (j : ℕ) :
      Integrable (clipThenMollify F (R : ℝ) (mollificationRadius j)) μ := by
    apply (integrable_const (R : ℝ)).mono' (happCont j).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact happRange j x
  have hpoint : ∀ x : EuclideanSpace ℝ ι,
      Tendsto (fun j => clipThenMollify F (R : ℝ) (mollificationRadius j) x)
        atTop (𝓝 (clipFunction (R : ℝ) F x)) := by
    intro x
    have hfactor : Tendsto
        (fun j : ℕ => (a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ) * mollificationRadius j / 2)
        atTop (𝓝 ((a : ℝ) + (b : ℝ) * ‖x‖)) := by
      have hbase : Tendsto (fun _ : ℕ => (a : ℝ) + (b : ℝ) * ‖x‖)
          atTop (𝓝 ((a : ℝ) + (b : ℝ) * ‖x‖)) := tendsto_const_nhds
      have hbconst : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ)) :=
        tendsto_const_nhds
      have hterm : Tendsto
          (fun j : ℕ => (b : ℝ) * mollificationRadius j / 2)
          atTop (𝓝 0) := by
        simpa [mul_zero] using (hbconst.mul hηzero).div_const 2
      simpa only [add_zero] using hbase.add hterm
    have herr : Tendsto
        (fun j : ℕ => mollificationRadius j *
          ((a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ) * mollificationRadius j / 2))
        atTop (𝓝 0) := by
      simpa using hηzero.mul hfactor
    have herrAbs : Tendsto
        (fun j : ℕ => |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x|) atTop (𝓝 0) := by
      apply squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) herr
      exact clipThenMollify_close hFcont (hηpos j) hclipSeg ha hb x
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa only [Real.norm_eq_abs] using herrAbs
  have herrorMeas (j : ℕ) : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ ι =>
        |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x|) μ := by
    exact ((continuous_abs.comp ((happCont j).sub hclipCont)).aestronglyMeasurable)
  have herrorBound (j : ℕ) (x : EuclideanSpace ℝ ι) :
      |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
        clipFunction (R : ℝ) F x| ≤ 2 * (R : ℝ) := by
    calc
      _ ≤ |clipThenMollify F (R : ℝ) (mollificationRadius j) x| +
          |clipFunction (R : ℝ) F x| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (clipThenMollify F (R : ℝ) (mollificationRadius j) x)
            0 (clipFunction (R : ℝ) F x))
      _ ≤ (R : ℝ) + (R : ℝ) := add_le_add (happRange j x)
        (abs_le.mpr (clipValue_bounds R.property))
      _ = 2 * (R : ℝ) := by ring
  have herrorLim (x : EuclideanSpace ℝ ι) :
      Tendsto (fun j : ℕ =>
        |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x|) atTop (𝓝 0) := by
    have hsub := (hpoint x).sub_const (clipFunction (R : ℝ) F x)
    have habs := (continuous_abs.continuousAt.tendsto.comp hsub)
    have hEq : (abs ∘ (fun j : ℕ =>
        clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x)) = (fun j =>
        |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x|) := by
      funext j
      rfl
    rw [hEq] at habs
    simpa only [sub_self, abs_zero] using habs
  have hL1 : Tendsto (fun j : ℕ => ∫ x,
      |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
        clipFunction (R : ℝ) F x| ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun (j : ℕ) (x : EuclideanSpace ℝ ι) =>
        |clipThenMollify F (R : ℝ) (mollificationRadius j) x -
          clipFunction (R : ℝ) F x|)
      (f := fun _ : EuclideanSpace ℝ ι => (0 : ℝ))
      (bound := fun _ => 2 * (R : ℝ)) herrorMeas
      (integrable_const (2 * (R : ℝ)))
      (fun j => ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs, abs_abs]
        exact herrorBound j x))
      (Filter.Eventually.of_forall herrorLim)
    simpa using h
  have hmean : Tendsto (fun j : ℕ => ∫ x,
      clipThenMollify F (R : ℝ) (mollificationRadius j) x ∂μ) atTop
        (𝓝 (∫ x, clipFunction (R : ℝ) F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence
      (F := fun (j : ℕ) (x : EuclideanSpace ℝ ι) =>
        clipThenMollify F (R : ℝ) (mollificationRadius j) x)
      (f := clipFunction (R : ℝ) F)
      (bound := fun _ => (R : ℝ)) (fun j => (happCont j).aestronglyMeasurable)
      (integrable_const (R : ℝ))
      (fun j => ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs]
        exact happRange j x))
      (Filter.Eventually.of_forall hpoint)
  exact ⟨happInt, hclipInt, hL1, hmean, hpoint⟩

end LOOConcentration.Revision
