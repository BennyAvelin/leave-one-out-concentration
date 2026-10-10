import LOOConcentrationRevision.Frozen.Bridges.LogSobolevConstant_inequality
import LOOConcentrationRevision.FunctionalInequalities.BoundedSmoothPair
import LOOConcentrationRevision.FunctionalInequalities.EntropyComputation
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal

/-- The certified completed-pair LSI acts on the actual scalar and gradient of
a bounded smooth generator, with the same finite admissible constant. -/
theorem bounded_smooth_entropy_le_of_logSobolevConstant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) :
    (∫ x, (F x)^2 * Real.log ((F x)^2) ∂μ) -
      (∫ x, (F x)^2 ∂μ) * Real.log (∫ x, (F x)^2 ∂μ) ≤
      2 * C * ∫ x, ‖gradient F x‖^2 ∂μ := by
  obtain ⟨u, hs, hg⟩ := exists_sobolevPair_of_bounded_smooth μ F hF B hB hbound
  have hfinite : logSobolevConstant μ < ⊤ := hLC.trans_lt ENNReal.ofReal_lt_top
  have hroot := logSobolevConstant_inequality μ hfinite u
  have hupper : squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * ENNReal.ofReal C * sobolevEnergy μ u :=
    hroot.trans (mul_le_mul_left (mul_le_mul_right hLC (2 : ℝ≥0∞)) (sobolevEnergy μ u))
  have hfinEntropy : squareEntropy μ (WithLp.ofLp u.val).1 < ⊤ :=
    hupper.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) (sobolevEnergy_lt_top u))
  have hDensity := (squareEntropy_lt_top_iff_integrable_density (WithLp.ofLp u.val).1).mp hfinEntropy
  have hgradInt : Integrable (fun x => ‖gradient F x‖^2) μ := by
    have h := (memLp_two_iff_integrable_sq_norm
      (Lp.memLp (WithLp.ofLp u.val).2).aestronglyMeasurable).mp
        (Lp.memLp (WithLp.ofLp u.val).2)
    exact h.congr (hg.mono fun x hx => by simpa only using congrArg (fun y => ‖y‖^2) hx)
  have hEnergy : sobolevEnergy μ u = ENNReal.ofReal (∫ x, ‖gradient F x‖^2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgradInt
      (Eventually.of_forall fun x => sq_nonneg ‖gradient F x‖)]
    unfold sobolevEnergy
    apply lintegral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  rw [squareEntropy_eq_of_integrable_density _ hDensity, hEnergy] at hupper
  have hSq : (∫ x, ((WithLp.ofLp u.val).1 x)^2 ∂μ) = ∫ x, (F x)^2 ∂μ :=
    integral_congr_ae (hs.mono fun x hx => by simpa only using congrArg (fun y : ℝ => y^2) hx)
  have hD : (∫ x, ((WithLp.ofLp u.val).1 x)^2 *
      Real.log (((WithLp.ofLp u.val).1 x)^2) ∂μ) =
      ∫ x, (F x)^2 * Real.log ((F x)^2) ∂μ :=
    integral_congr_ae (hs.mono fun x hx => by simpa only using congrArg (fun y : ℝ => y^2 * Real.log (y^2)) hx)
  rw [hSq, hD] at hupper
  have hE : 0 ≤ ∫ x, ‖gradient F x‖^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hconst : 2 * ENNReal.ofReal C *
      ENNReal.ofReal (∫ x, ‖gradient F x‖^2 ∂μ) =
      ENNReal.ofReal (2 * C * ∫ x, ‖gradient F x‖^2 ∂μ) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hconst] at hupper
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hupper

/-- A real mollified importing consumer produces its generator premises before
applying the certified same-constant completed LSI. -/
theorem clipThenMollify_entropy_le_of_constant_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (R : NNReal)
    (η : ℝ) (hη : 0 < η) :
    (∫ x, (clipThenMollify F R η x)^2 * Real.log ((clipThenMollify F R η x)^2) ∂μ) -
      (∫ x, (clipThenMollify F R η x)^2 ∂μ) *
        Real.log (∫ x, (clipThenMollify F R η x)^2 ∂μ) ≤
      2 * C * ∫ x, ‖gradient (clipThenMollify F R η) x‖^2 ∂μ := by
  obtain ⟨hsmooth, B, hB, hbound⟩ := clipThenMollify_bounded_smooth F hF R η hη
  exact bounded_smooth_entropy_le_of_logSobolevConstant_le μ C hC hLC
    (clipThenMollify F R η) hsmooth B hB hbound

end LOOConcentration.Revision
