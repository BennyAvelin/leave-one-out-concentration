import LOOConcentrationRevision.Frozen.Bridges.LogSobolevConstant_inequality
import LOOConcentrationRevision.FunctionalInequalities.SmoothSeparation
import LOOConcentrationRevision.FunctionalInequalities.BoundedSmoothPair
import LOOConcentrationRevision.FunctionalInequalities.EntropyZero
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory InnerProductSpace
open scoped ENNReal

/-- A zero optimal constant forces a point mass. The sign needed by strict
Jensen is supplied by shifting the same bounded smooth separator. -/
theorem exists_dirac_of_logSobolevConstant_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hzero : logSobolevConstant μ = 0) : ∃ a, μ = Measure.dirac a := by
  by_contra! hnot
  obtain ⟨F, hF, ⟨B, hB, hbound⟩, _hMem, hVar⟩ :=
    exists_bounded_smooth_generator_positive_variance μ hnot
  let G : EuclideanSpace ℝ ι → ℝ := fun x => F x + B
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := hF.add contDiff_const
  have hgrad : gradient G = gradient F := by
    funext x
    change (toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ (fun y => F y + B) x) =
      (toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ F x)
    rw [fderiv_add_const]
  have hGbound : ∀ x, |G x| ≤ 2 * B ∧ ‖gradient G x‖ ≤ 2 * B := by
    intro x
    refine ⟨?_, ?_⟩
    · calc
        |G x| ≤ |F x| + |B| := abs_add_le _ _
        _ ≤ 2 * B := by rw [abs_of_nonneg hB]; linarith [(hbound x).1]
    · rw [hgrad]; linarith [(hbound x).2]
  obtain ⟨u, hf, _hg⟩ := exists_sobolevPair_of_bounded_smooth μ G hG
    (2 * B) (mul_nonneg (by norm_num) hB) hGbound
  have hfinite : logSobolevConstant μ < ⊤ := by rw [hzero]; exact bot_lt_top
  have hent : squareEntropy μ (WithLp.ofLp u.val).1 = 0 := by
    have h := logSobolevConstant_inequality μ hfinite u
    rw [hzero, mul_zero, zero_mul] at h
    exact le_antisymm h bot_le
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ (WithLp.ofLp u.val).1 x := by
    filter_upwards [hf] with x hx
    rw [hx]
    have h := (abs_le.mp (hbound x).1).1
    change 0 ≤ F x + B
    linarith
  have hconst := ae_eq_sqrt_mean_of_squareEntropy_eq_zero
    (WithLp.ofLp u.val).1 hent hnonneg
  have hFconst : F =ᵐ[μ] (fun _ =>
      Real.sqrt (∫ x, ((WithLp.ofLp u.val).1 x)^2 ∂μ) - B) := by
    filter_upwards [hf, hconst] with x hx hc
    change (WithLp.ofLp u.val).1 x = F x + B at hx
    linarith
  have hvzero : ProbabilityTheory.variance F μ = 0 := by
    rw [ProbabilityTheory.variance_congr hFconst]
    simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]
  exact (ne_of_gt hVar) hvzero

end LOOConcentration.Revision
