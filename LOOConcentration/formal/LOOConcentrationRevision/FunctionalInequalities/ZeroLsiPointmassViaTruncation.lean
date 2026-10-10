import LOOConcentrationRevision.FunctionalInequalities.FiniteLsiTruncation
import LOOConcentrationRevision.Frozen.Bridges.Bounded_truncation_admission
import LOOConcentrationRevision.Frozen.Bridges.LogSobolevConstant_inequality
import LOOConcentrationRevision.FunctionalInequalities.SmoothSeparation
import LOOConcentrationRevision.FunctionalInequalities.EntropyZero
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory InnerProductSpace
open scoped ENNReal

/-- A zero optimal constant forces a point mass using the sealed truncation
admission and finite-constant inequality on the same admitted Sobolev pair. -/
theorem exists_dirac_of_logSobolevConstant_eq_zero_via_truncation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hMoment : Integrable (fun x => ‖x‖ ^ 2) μ)
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
  have hloc : LocallyLipschitz G := by
    have hG1 : ContDiff ℝ (1 : WithTop ℕ∞) G := hG.of_le (by
      exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top))
    exact hG1.locallyLipschitz
  let A : NNReal := ⟨(2 : ℝ) * B, mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hB⟩
  have hA : (A : ℝ) = (2 : ℝ) * B := rfl
  have hgradVol : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ G x ∧ ‖gradient G x‖ ≤ (A : ℝ) + (0 : ℝ) * ‖x‖ := by
    filter_upwards [] with x
    refine ⟨(hG.differentiable (by simp)) x, ?_⟩
    simpa [hA] using (hGbound x).2
  obtain ⟨u, huclip, _⟩ :=
    bounded_truncation_admission μ hMoment G hloc A 0 A hgradVol
  let f : Lp ℝ 2 μ := (WithLp.ofLp u.val).1
  have hclipG (x : EuclideanSpace ℝ ι) :
      max (-(A : ℝ)) (min (G x) (A : ℝ)) = G x := by
    have habs : |G x| ≤ (A : ℝ) := by simpa [hA] using (hGbound x).1
    have hlo : -(A : ℝ) ≤ G x := (abs_le.mp habs).1
    have hhi : G x ≤ (A : ℝ) := (abs_le.mp habs).2
    rw [min_eq_left hhi, max_eq_right hlo]
  have hfG : (fun x => f x) =ᵐ[μ] G := by
    filter_upwards [huclip] with x hx
    change f x = max (-(A : ℝ)) (min (G x) (A : ℝ)) at hx
    rw [hx, hclipG]
  have hGnonneg : ∀ x, 0 ≤ G x := by
    intro x
    have hlower : -B ≤ F x := (abs_le.mp (hbound x).1).1
    dsimp [G]
    linarith
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hfG] with x hx
    rw [hx]
    exact hGnonneg x
  have hfinite : logSobolevConstant μ < ⊤ := by rw [hzero]; exact bot_lt_top
  have hent : squareEntropy μ f = 0 := by
    have h := (completed_lsi_and_bounded_truncations_of_finite μ hfinite).1 u
    rw [hzero, mul_zero, zero_mul] at h
    exact le_antisymm h bot_le
  have hconst := ae_eq_sqrt_mean_of_squareEntropy_eq_zero f hent hnonneg
  have hFconst : F =ᵐ[μ] (fun _ =>
      Real.sqrt (∫ x, f x ^ 2 ∂μ) - B) := by
    filter_upwards [hfG, hconst] with x hx hc
    have hxG : f x = F x + B := by simpa [G] using hx
    linarith
  have hvzero : ProbabilityTheory.variance F μ = 0 := by
    rw [ProbabilityTheory.variance_congr hFconst]
    simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]
  exact (ne_of_gt hVar) hvzero

end LOOConcentration.Revision
