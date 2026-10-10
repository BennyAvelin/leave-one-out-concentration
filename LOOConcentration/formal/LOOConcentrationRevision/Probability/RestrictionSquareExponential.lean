import LOOConcentrationRevision.Probability.ConditionalMeanShift
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- An actual raw exponential-square bound yields its logarithmic conditional
scale. The raw bound is an internal premise supplied by the scalar SG producer. -/
theorem normalizedRestriction_square_exponential_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hq : 0 < μ.real K) (X : α → ℝ)
    (hX : AEStronglyMeasurable X μ) (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp ((X x)^2 / a)) μ)
    (hBound : (∫ x, Real.exp ((X x)^2 / a) ∂μ) ≤ 2) :
    Integrable (fun x => Real.exp ((X x)^2 / (2*a*Real.log (Real.exp 1 / μ.real K))))
      (normalizedRestriction μ K) ∧
    (∫ x, Real.exp ((X x)^2 / (2*a*Real.log (Real.exp 1 / μ.real K)))
      ∂normalizedRestriction μ K) ≤ 2 := by
  let q := μ.real K
  have hq1 : q ≤ 1 := measureReal_le_one
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
  let ℓ := Real.log (Real.exp 1 / q)
  have hℓ : ℓ = 1 - Real.log q := by
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hℓpos : 0 < ℓ := by linarith
  let θ := 1 / (2*ℓ)
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply (div_le_iff₀ (by positivity : 0 < 2*ℓ)).2
    linarith
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  have hK0 : μ K ≠ 0 := by
    intro hz
    have : μ.real K = 0 := by simp [Measure.real, hz]
    exact hq.ne' this
  have hInv : (μ K)⁻¹ ≠ (⊤ : ENNReal) := ENNReal.inv_ne_top.mpr hK0
  have hExpν : Integrable (fun x => Real.exp ((X x)^2/a)) ν :=
    hExp.restrict.smul_measure hInv
  have hXν : AEStronglyMeasurable X ν :=
    hX.restrict.smul_measure ((μ K)⁻¹)
  have hsmall : Integrable (fun x => Real.exp ((X x)^2/a * θ)) ν := by
    apply hExpν.mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (div_nonneg (sq_nonneg _) ha.le) hθ1
  have hEq : (fun x => Real.exp ((X x)^2/(2*a*ℓ))) =
      fun x => Real.exp ((X x)^2/a * θ) := by
    funext x
    congr 1
    dsimp [θ]
    field_simp
  change Integrable (fun x => Real.exp ((X x)^2/(2*a*ℓ))) ν ∧ _
  refine ⟨hEq ▸ hsmall, ?_⟩
  rw [hEq]
  have hRaw : (∫ x, Real.exp ((X x)^2/a) ∂ν) ≤ 2/q := by
    change (∫ x, Real.exp ((X x)^2/a) ∂((μ K)⁻¹ • μ.restrict K)) ≤ _
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    change q⁻¹ * (∫ x in K, Real.exp ((X x)^2/a) ∂μ) ≤ _
    calc
      _ ≤ q⁻¹ * (∫ x, Real.exp ((X x)^2/a) ∂μ) :=
        mul_le_mul_of_nonneg_left
          (integral_mono_measure Measure.restrict_le_self
            (ae_of_all μ fun x => (Real.exp_pos _).le) hExp) (inv_nonneg.mpr hq.le)
      _ ≤ q⁻¹ * 2 := mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr hq.le)
      _ = _ := by ring
  have hPow : Integrable (fun x => (Real.exp ((X x)^2/a)) ^ θ) ν := by
    simpa only [← Real.exp_mul] using hsmall
  have hJ := (Real.concaveOn_rpow hθ0 hθ1).le_map_integral
    (Real.continuous_rpow_const hθ0).continuousOn isClosed_Ici
    (ae_of_all ν fun x => (Real.exp_pos ((X x)^2/a)).le) hExpν hPow
  have h2q : 0 < 2/q := div_pos (by norm_num) hq
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlog2q : Real.log (2/q) ≤ ℓ := by
    rw [Real.log_div (by norm_num : (2:ℝ)≠0) hq.ne', hℓ]
    linarith
  have hpower : (2/q)^θ ≤ Real.exp (1/2) := by
    rw [Real.rpow_def_of_pos h2q]
    apply Real.exp_le_exp.mpr
    dsimp [θ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*ℓ)).2
    nlinarith
  calc
    (∫ x, Real.exp ((X x)^2/a * θ) ∂ν) =
        ∫ x, (Real.exp ((X x)^2/a))^θ ∂ν := by simp only [Real.exp_mul]
    _ ≤ (∫ x, Real.exp ((X x)^2/a) ∂ν)^θ := hJ
    _ ≤ (2/q)^θ := Real.rpow_le_rpow (integral_nonneg fun x => (Real.exp_pos _).le) hRaw hθ0
    _ ≤ Real.exp (1/2) := hpower
    _ ≤ 2 := by
      have h := Real.exp_bound_div_one_sub_of_interval (x := (1/2:ℝ)) (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h

end LOOConcentration.Revision
