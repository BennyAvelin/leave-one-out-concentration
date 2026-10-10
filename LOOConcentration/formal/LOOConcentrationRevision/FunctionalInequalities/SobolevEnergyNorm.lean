import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergy

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

/-- The retained gradient energy is the square of its actual L2 norm. -/
theorem sobolevEnergy_eq_ofReal_norm_sq (u : SobolevPair μ) :
    sobolevEnergy μ u = ENNReal.ofReal (‖(WithLp.ofLp u.val).2‖^2) := by
  let G : Lp (EuclideanSpace ℝ ι) 2 μ := (WithLp.ofLp u.val).2
  have hi : Integrable (fun x => ‖G x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp G).aestronglyMeasurable).mp (Lp.memLp G)
  have heq : (∫ x, ‖G x‖^2 ∂μ) = ‖G‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  calc
    sobolevEnergy μ u = ∫⁻ x, ENNReal.ofReal (‖G x‖^2) ∂μ := by
      unfold sobolevEnergy
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∫ x, ‖G x‖^2 ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
        fun x => sq_nonneg ‖G x‖)).symm
    _ = ENNReal.ofReal (‖G‖^2) := congrArg ENNReal.ofReal heq

end LOOConcentration.Revision
