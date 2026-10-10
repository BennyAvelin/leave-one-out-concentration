import LOOConcentrationManuscript.Internal.LocalSlopeCompositionConsumer
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The loss and estimator Lipschitz assumptions in the source remark imply
the actual composed fitted-loss bound, with zero data-growth term. -/
theorem lipschitz_loss_composition_source_full_carrier
    {ι : Type*} [Fintype ι]
    {G : Type*} [PseudoMetricSpace G]
    (T : EuclideanSpace ℝ ι → G) (L : G → ℝ) (C K : NNReal)
    (hL : LipschitzWith C L) (hT : LipschitzWith K T) :
    LipschitzWith (C * K) (fun E => L (T E)) ∧
      LocallyLipschitz (fun E => L (T E)) ∧
      ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ ι)),
        DifferentiableAt ℝ (fun D => L (T D)) E ∧
          ‖gradient (fun D => L (T D)) E‖ ≤ (C : ℝ) * (K : ℝ) := by
  have hLip := hL.comp hT
  refine ⟨hLip, hLip.locallyLipschitz, ?_⟩
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    have hConst : (fun D : EuclideanSpace ℝ ι => L (T D)) =
        (fun _ => L (T 0)) := by
      funext D
      rw [Subsingleton.elim D 0]
    rw [hConst]
    filter_upwards with E
    refine ⟨differentiableAt_const _, ?_⟩
    rw [gradient_fun_const, norm_zero]
    positivity
  | inr hι =>
    let _ := hι
    have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean
      (fun D => L (T D)) hLip.locallyLipschitz
    filter_upwards [hAE] with E hdiff
    refine ⟨hdiff, ?_⟩
    calc
      ‖gradient (fun D => L (T D)) E‖ = ‖fderiv ℝ (fun D => L (T D)) E‖ := by
        rw [gradient]
        exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map _
      _ ≤ ((C * K : NNReal) : ℝ) := hdiff.hasFDerivAt.le_of_lipschitz hLip
      _ = (C : ℝ) * (K : ℝ) := rfl

/-- A real source consumer: the actual empirical mean and absolute loss
consume the composition result with the original sample normalization. -/
theorem empiricalMean_absoluteLoss_composition_full_carrier_consumer (r : ℕ) (y : ℝ) :
    LipschitzWith (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (fun D => |empiricalMean r D - y|) ∧
      LocallyLipschitz (fun D => |empiricalMean r D - y|) ∧
      ∀ᵐ D ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1)))),
        DifferentiableAt ℝ (fun E => |empiricalMean r E - y|) D ∧
          ‖gradient (fun E => |empiricalMean r E - y|) D‖ ≤
            (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
  have hL : LipschitzWith 1 (fun a : ℝ => |a - y|) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    calc
      abs (abs (a - y) - abs (b - y)) ≤ abs ((a - y) - (b - y)) :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = |a - b| := by congr 1; ring
  have hs : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  simpa only [one_mul, NNReal.coe_one,
    Real.coe_toNNReal _ (inv_nonneg.2 hs.le)] using
    lipschitz_loss_composition_source_full_carrier (empiricalMean r) (fun a : ℝ => |a - y|)
      1 (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) hL
        (empiricalMean_lipschitz r)

end LOOConcentration.Manuscript.Internal
