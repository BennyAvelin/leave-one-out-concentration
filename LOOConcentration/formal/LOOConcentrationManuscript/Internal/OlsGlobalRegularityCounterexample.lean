import LOOConcentration.Frozen.Examples.OlsPrediction
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open Filter
open scoped Topology

private theorem ols_twoPoint_prediction (t : ℝ) (ht : t ≠ 0) :
    LOOConcentration.olsPrediction (![(0, 0), (t, 1)] : Fin 2 → ℝ × ℝ) 1 =
      t⁻¹ := by
  dsimp only [LOOConcentration.olsPrediction]
  norm_num [Fin.sum_univ_succ]
  field_simp [ht]
  ring

/-- Two nondegenerate observations already exhibit the source's blow-up as
the centered design variance approaches zero. -/
theorem ols_twoPoint_absoluteLoss_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ =>
      |LOOConcentration.olsPrediction (![(0, 0), (s, 1)] : Fin 2 → ℝ × ℝ) 1|)
      (-(t ^ 2)⁻¹) t := by
  have heq : (fun s : ℝ =>
      |LOOConcentration.olsPrediction (![(0, 0), (s, 1)] : Fin 2 → ℝ × ℝ) 1|)
      =ᶠ[𝓝 t] (fun s : ℝ => s⁻¹) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [ols_twoPoint_prediction s hs.ne', abs_of_pos (inv_pos.2 hs)]
  simpa only [id_eq, neg_div, one_div] using
    ((hasDerivAt_id t).inv ht.ne').congr_of_eventuallyEq heq

/-- The actual OLS absolute fitted loss cannot be continuous on all possible
data configurations, so it cannot satisfy the global regularity assumption. -/
theorem ols_absoluteLoss_not_continuous_at_zeroVariance :
    ¬ ContinuousAt
      (fun D : Fin 2 → ℝ × ℝ => |LOOConcentration.olsPrediction D 1|)
      (![(0, 0), (0, 1)] : Fin 2 → ℝ × ℝ) := by
  intro hc
  let curve : ℝ → (Fin 2 → ℝ × ℝ) := fun t => ![(0, 0), (t, 1)]
  have hcurve : Continuous curve := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [curve] <;> fun_prop
  have hzero : curve 0 = (![(0, 0), (0, 1)] : Fin 2 → ℝ × ℝ) := rfl
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hcCurve : ContinuousAt (fun t => |LOOConcentration.olsPrediction (curve t) 1|) 0 :=
    (show ContinuousAt (fun D : Fin 2 → ℝ × ℝ =>
      |LOOConcentration.olsPrediction D 1|) (curve 0) from hc).comp
        (f := curve) (x := 0) (hcurve.continuousAt : ContinuousAt curve 0)
  have hlimit := hcCurve.tendsto.comp hseq
  have hvalues (n : ℕ) :
      |LOOConcentration.olsPrediction (curve (((n : ℝ) + 1)⁻¹)) 1| =
        (n : ℝ) + 1 := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    rw [ols_twoPoint_prediction _ (inv_ne_zero hn.ne'), inv_inv, abs_of_pos hn]
  have htop : Tendsto (fun n : ℕ =>
      |LOOConcentration.olsPrediction (curve (((n : ℝ) + 1)⁻¹)) 1|) atTop atTop := by
    simp_rw [hvalues]
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact not_tendsto_nhds_of_tendsto_atTop htop _ hlimit

/-- The global-instability witness is consumed on the actual full paired
Euclidean training carrier used by the standing regularity assumption. -/
theorem ols_actualEuclidean_absoluteLoss_not_locallyLipschitz :
    ¬ LocallyLipschitz (fun E : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate 1 1 2) =>
      |LOOConcentration.olsPrediction
        (fun i : Fin 2 =>
          ((LOOConcentration.Revision.datasetOfEuclidean E i).1 0,
            (LOOConcentration.Revision.datasetOfEuclidean E i).2 0)) 1|) := by
  intro h
  let embed : (Fin 2 → ℝ × ℝ) → EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate 1 1 2) := fun D =>
    WithLp.toLp 2 (fun i => Sum.elim (fun _ => (D i.1).1)
      (fun _ => (D i.1).2) i.2)
  have hembed : Continuous embed := by
    apply (PiLp.continuous_toLp 2
      (fun _ : LOOConcentration.DatasetCoordinate 1 1 2 => ℝ)).comp
    apply continuous_pi
    intro i
    cases i.2 <;> dsimp only [Sum.elim] <;> fun_prop
  have hback (D : Fin 2 → ℝ × ℝ) :
      (fun i : Fin 2 =>
        ((LOOConcentration.Revision.datasetOfEuclidean (embed D) i).1 0,
          (LOOConcentration.Revision.datasetOfEuclidean (embed D) i).2 0)) = D := by
    funext i
    rfl
  have hc : Continuous (fun D : Fin 2 → ℝ × ℝ =>
      |LOOConcentration.olsPrediction D 1|) := by
    have hc := h.continuous.comp hembed
    change Continuous (fun D : Fin 2 → ℝ × ℝ =>
      |LOOConcentration.olsPrediction
        (fun i : Fin 2 =>
          ((LOOConcentration.Revision.datasetOfEuclidean (embed D) i).1 0,
            (LOOConcentration.Revision.datasetOfEuclidean (embed D) i).2 0)) 1|) at hc
    simpa only [hback] using hc
  exact ols_absoluteLoss_not_continuous_at_zeroVariance hc.continuousAt

end LOOConcentration.Manuscript.Internal
