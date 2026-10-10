import BoundedCenteredLpFinalEpsilonSource
import LOOConcentrationRevision.Analysis.RealQDerivativeHolderSource

set_option autoImplicit false
open MeasureTheory
open InnerProductSpace

namespace LOOConcentration.Revision
noncomputable section

/-- Source-facing bounded centered Lp estimate with no derivative-bound premise.
The actual real-q derivative producer is applied internally to the centered source. -/
theorem boundedSmoothCenteredLp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, |F x - ∫ y, F y ∂μ| ^ p ∂μ) ^ (2 / p) ≤
      C * (p - 1) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
  have hFint : Integrable F μ := by
    apply Integrable.of_bound hF.continuous.aestronglyMeasurable B
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using (hbound x).1
  let mean : ℝ := ∫ x, F x ∂μ
  let G : EuclideanSpace ℝ ι → ℝ := fun x => F x - mean
  have hMeanBound : |mean| ≤ B := by
    calc
      |mean| = |∫ x, F x ∂μ| := rfl
      _ ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, B ∂μ := by
        apply integral_mono_ae hFint.abs (integrable_const B)
        exact Filter.Eventually.of_forall fun x => (hbound x).1
      _ = B := by simp
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    simpa [G] using hF.sub contDiff_const
  have hGabs : ∀ x, |G x| ≤ 2 * B := by
    intro x
    calc
      |G x| = |F x - mean| := rfl
      _ ≤ |F x| + |mean| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbound x).1 hMeanBound
      _ = 2 * B := by ring
  have hGgrad (x : EuclideanSpace ℝ ι) : gradient G x = gradient F x := by
    apply (toDual ℝ (EuclideanSpace ℝ ι)).injective
    simp [G, toDual_gradient, fderiv_sub_const]
  have hGbound : ∀ x, |G x| ≤ 2 * B ∧ ‖gradient G x‖ ≤ 2 * B := by
    intro x
    constructor
    · exact hGabs x
    · rw [hGgrad x]
      nlinarith [hB, (hbound x).2]
  have hGradMomentEq :
      (∫ x, ‖gradient G x‖ ^ p ∂μ) =
        (∫ x, ‖gradient F x‖ ^ p ∂μ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hGgrad x]
  have hDerivativeUpperBound :
      ∀ ε, 0 < ε → ∀ q ∈ Set.Ioo 2 p,
        LOOConcentrationRevision.regularizedSourceLpCurveDerivative μ
          (fun x => F x - ∫ y, F y ∂μ) ε q ≤
        C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
    intro ε hε q hq
    have hCurveDeriv :=
      LOOConcentrationRevision.regularizedSourceLpCurve_hasDerivAt
        (μ := μ) (F := G) (B := 2 * B) (ε := ε) (q := q)
        hG.continuous.measurable (by positivity) hGabs hε hq.1.le
    have hProducer := bounded_smooth_regularized_realQ_derivative_le
      μ C hC hLC G hG (2 * B) (by positivity) hGbound ε q p hε hq.1 hq.2.le
    have hProducerCurve :
        deriv (fun r : ℝ => LOOConcentrationRevision.regularizedSourceLpCurve μ G ε r) q ≤
          C * (∫ x, ‖gradient G x‖ ^ p ∂μ) ^ (2 / p) := by
      simpa [LOOConcentrationRevision.regularizedSourceLpCurve] using hProducer
    calc
      LOOConcentrationRevision.regularizedSourceLpCurveDerivative μ
          (fun x => F x - ∫ y, F y ∂μ) ε q =
        deriv (fun r : ℝ => LOOConcentrationRevision.regularizedSourceLpCurve μ G ε r) q := by
          dsimp [G, mean]
          exact hCurveDeriv.deriv.symm
      _ ≤ C * (∫ x, ‖gradient G x‖ ^ p ∂μ) ^ (2 / p) := hProducerCurve
      _ = C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by rw [hGradMomentEq]
  exact boundedSmoothCenteredLp_of_actualRegularizedDerivativeBound
    μ C hC hLC F hF B hB hbound hp (by simpa [G, mean] using hDerivativeUpperBound)

end
end LOOConcentration.Revision
