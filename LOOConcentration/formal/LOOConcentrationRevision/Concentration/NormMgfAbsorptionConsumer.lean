import LOOConcentrationRevision.Concentration.NormMgfLimit
import LOOConcentration.Concentration.EntropyAbsorption

set_option autoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory

/-- Conditional entropy absorption for the actual product law. The norm-MGF
and its integrability are produced inside this consumer. The two tilted
entropy inequalities remain separate predecessor obligations. -/
theorem product_norm_mgf_entropy_absorption_of_tilt_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (a b lam H Qtilt : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hlam : 0 < |lam|) (hcut : |lam| ≤ 1 / (4 * C * b))
    (hEntropy : H ≤ C * lam ^ 2 * (a ^ 2 + b ^ 2 * Qtilt))
    (hTiltNorm : (2 * C * lam ^ 2 * b ^ 2) * Qtilt ≤ H +
      Real.log (∫ x : EuclideanSpace ℝ (Fin r × ι),
        Real.exp ((2 * C * lam ^ 2 * b ^ 2) * ‖x‖ ^ 2)
          ∂euclideanProductLaw (κ := Fin r) μ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin r × ι) =>
      Real.exp ((2 * C * lam ^ 2 * b ^ 2) * ‖x‖ ^ 2))
        (euclideanProductLaw (κ := Fin r) μ) ∧
      H ≤ 2 * C * lam ^ 2 *
        (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ)) := by
  let s := 2 * C * lam ^ 2 * b ^ 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hscaled : |lam| * (4 * C * b) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * C * b)).mp hcut
  have hsq : (4 * C * b * |lam|) ^ 2 ≤ 1 := by
    have hn : 0 ≤ 4 * C * b * |lam| := by positivity
    have hl : 4 * C * b * |lam| ≤ 1 := by nlinarith [hscaled]
    nlinarith
  have hcutS : 2 * C * s < 1 := by
    dsimp [s]
    rw [mul_pow, mul_pow, sq_abs] at hsq
    nlinarith
  let ν := euclideanProductLaw (κ := Fin r) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hNorm : Integrable (fun x : EuclideanSpace ℝ (Fin r × ι) =>
      Real.exp (s * ‖x‖ ^ 2)) ν ∧
      Real.log (∫ x, Real.exp (s * ‖x‖ ^ 2) ∂ν) ≤
        s * (r : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ) / (1 - 2 * C * s) := by
    cases r with
    | zero =>
      have heq : (fun x : EuclideanSpace ℝ (Fin 0 × ι) => Real.exp (s * ‖x‖ ^ 2)) =
          fun _ => (1 : ℝ) := by
        funext x
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [hx, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero]
      simp only [heq, integral_const, probReal_univ, one_smul, Real.log_one,
        Nat.cast_zero, mul_zero, zero_mul, zero_div, le_refl, and_true]
      exact integrable_const 1
    | succ r =>
      have hfinite : logSobolevConstant μ < ⊤ :=
        lt_of_le_of_lt hLC ENNReal.ofReal_lt_top
      have hνLC : logSobolevConstant (euclideanProductLaw (κ := Fin (r+1)) μ) ≤
          ENNReal.ofReal C :=
        (logSobolevConstant_euclideanProductLaw_le r μ hfinite).trans hLC
      have h := norm_sq_log_mgf_le_of_admissible_constant
        (euclideanProductLaw (κ := Fin (r+1)) μ) C hC.le hνLC
        (integrable_euclideanProductLaw_norm_sq μ hM2) s hs hcutS
      have hmean := integral_euclideanProductLaw_norm_sq (κ := Fin (r+1)) μ hM2
      simp only [Fintype.card_fin] at hmean
      rw [hmean] at h
      simpa only [ν, Nat.succ_eq_add_one, mul_assoc] using h
  obtain ⟨hInt, hLog⟩ := hNorm
  refine ⟨hInt, ?_⟩
  exact LOOConcentration.quadratic_entropy_absorption_of_predecessor_bounds
    r hC hb ha (integral_nonneg fun _ => sq_nonneg _) hlam hcut rfl
      hEntropy hTiltNorm (by simpa only [s, ν, mul_assoc] using hLog)

end LOOConcentration.Revision
