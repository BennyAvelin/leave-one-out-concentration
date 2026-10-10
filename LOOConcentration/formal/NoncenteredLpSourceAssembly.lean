import BoundedCenteredLpFinalEpsilonSource
import LOOConcentrationRevision.Analysis.RealQDerivativeHolderSource
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory
open InnerProductSpace
open scoped ENNReal

namespace LOOConcentration.Revision
noncomputable section

/-- Bounded noncentered source Lp interpolation. The accepted real-q derivative
producer is consumed internally on the literal `sqrt (F^2 + ε)` curve. -/
theorem boundedSmoothNoncenteredLp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, |F x| ^ p ∂μ) ^ (2 / p) ≤
      (∫ x, F x ^ 2 ∂μ) + C * (p - 2) *
        (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
  let D : ℝ := C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)
  have hFabs (x : EuclideanSpace ℝ ι) : |F x| ≤ B := (hbound x).1
  have hFmem : MemLp F (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound hF.continuous.aestronglyMeasurable B
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hFabs x
  have hRawInt : Integrable (fun x => |F x| ^ p) μ := by
    have h := hFmem.integrable_norm_rpow'
    simpa only [Real.norm_eq_abs,
      ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using h
  have hFinal : ∀ ε, 0 < ε →
      (∫ x, |F x| ^ p ∂μ) ^ (2 / p) ≤
        (∫ x, F x ^ 2 ∂μ) + C * (p - 2) *
          (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) + ε := by
    intro ε hε
    let H : EuclideanSpace ℝ ι → ℝ := fun x => Real.sqrt (F x ^ 2 + ε)
    have hHcont : Continuous H := by
      dsimp [H]
      fun_prop
    have hFsqBound (x : EuclideanSpace ℝ ι) : F x ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (F x)) hB).2 (hFabs x)
    have hHbound (x : EuclideanSpace ℝ ι) :
        ‖H x‖ ≤ Real.sqrt (B ^ 2 + ε) := by
      have hrad : F x ^ 2 + ε ≤ B ^ 2 + ε := by linarith [hFsqBound x]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt hrad
    have hHmem : MemLp H (ENNReal.ofReal p) μ := by
      apply MemLp.of_bound hHcont.aestronglyMeasurable (Real.sqrt (B ^ 2 + ε))
      filter_upwards with x
      exact hHbound x
    have hRegInt : Integrable (fun x => |Real.sqrt (F x ^ 2 + ε)| ^ p) μ := by
      have h := hHmem.integrable_norm_rpow'
      simpa only [Real.norm_eq_abs, H, abs_of_nonneg (Real.sqrt_nonneg _),
        ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using h
    have hPoint (x : EuclideanSpace ℝ ι) :
        |F x| ^ p ≤ |Real.sqrt (F x ^ 2 + ε)| ^ p := by
      have hbase : |F x| ≤ Real.sqrt (F x ^ 2 + ε) := by
        calc
          |F x| = Real.sqrt (F x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (F x ^ 2 + ε) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (F x), hε.le])
      have hsqrt : 0 ≤ Real.sqrt (F x ^ 2 + ε) := Real.sqrt_nonneg _
      calc
        |F x| ^ p ≤ Real.sqrt (F x ^ 2 + ε) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)
        _ = |Real.sqrt (F x ^ 2 + ε)| ^ p := by rw [abs_of_nonneg hsqrt]
    have hIntMono :
        (∫ x, |F x| ^ p ∂μ) ≤
          ∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ p ∂μ :=
      integral_mono hRawInt hRegInt hPoint
    have hCurveLower :
        (∫ x, |F x| ^ p ∂μ) ^ (2 / p) ≤
          LOOConcentrationRevision.regularizedSourceLpCurve μ F ε p := by
      unfold LOOConcentrationRevision.regularizedSourceLpCurve
      exact Real.rpow_le_rpow
        (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (abs_nonneg _) _)) hIntMono (by positivity)
    have hDerivativeBound :
        ∀ q ∈ Set.Ioo 2 p,
          LOOConcentrationRevision.regularizedSourceLpCurveDerivative μ F ε q ≤ D := by
      intro q hq
      have hProducer :=
        bounded_smooth_regularized_realQ_derivative_le
          μ C hC hLC F hF B hB hbound ε q p hε hq.1 (le_of_lt hq.2)
      have hCurveDeriv :=
        LOOConcentrationRevision.regularizedSourceLpCurve_hasDerivAt
          (μ := μ) (F := F) (B := B) (ε := ε) (q := q)
          hF.continuous.measurable hB hFabs hε hq.1.le
      calc
        LOOConcentrationRevision.regularizedSourceLpCurveDerivative μ F ε q =
            deriv (fun r : ℝ => LOOConcentrationRevision.regularizedSourceLpCurve μ F ε r) q :=
          hCurveDeriv.deriv.symm
        _ ≤ D := by
          simpa only [LOOConcentrationRevision.regularizedSourceLpCurve, D] using hProducer
    have hCurveIncrement :=
      actualRegularizedCurveIncrement_of_interior_derivative_bound
        (μ := μ) (G := F) (B := B) (ε := ε) (p := p) (D := D)
        hF.continuous.measurable hB hFabs hε hp hDerivativeBound
    have hFsqInt : Integrable (fun x => F x ^ 2) μ := by
      apply Integrable.of_bound (hF.continuous.pow 2).aestronglyMeasurable (B ^ 2)
      filter_upwards with x
      change ‖F x ^ 2‖ ≤ B ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F x))]
      exact hFsqBound x
    have hCurveTwo :
        LOOConcentrationRevision.regularizedSourceLpCurve μ F ε 2 =
          (∫ x, F x ^ 2 ∂μ) + ε := by
      unfold LOOConcentrationRevision.regularizedSourceLpCurve
      rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
      have hpoint (x : EuclideanSpace ℝ ι) :
          |Real.sqrt (F x ^ 2 + ε)| ^ (2 : ℝ) = F x ^ 2 + ε := by
        calc
          |Real.sqrt (F x ^ 2 + ε)| ^ (2 : ℝ) =
              Real.sqrt (F x ^ 2 + ε) ^ (2 : ℕ) := by
                rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                exact Real.rpow_natCast _ 2
          _ = F x ^ 2 + ε := Real.sq_sqrt (by positivity)
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      rw [integral_add hFsqInt (integrable_const ε)]
      simp
    calc
      (∫ x, |F x| ^ p ∂μ) ^ (2 / p)
          ≤ LOOConcentrationRevision.regularizedSourceLpCurve μ F ε p := hCurveLower
      _ ≤ LOOConcentrationRevision.regularizedSourceLpCurve μ F ε 2 + D * (p - 2) :=
        hCurveIncrement
      _ = (∫ x, F x ^ 2 ∂μ) +
            C * (p - 2) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) + ε := by
        rw [hCurveTwo]
        dsimp [D]
        ring
  apply le_of_forall_pos_le_add
  intro ε hε
  exact hFinal ε hε

end
end LOOConcentration.Revision
