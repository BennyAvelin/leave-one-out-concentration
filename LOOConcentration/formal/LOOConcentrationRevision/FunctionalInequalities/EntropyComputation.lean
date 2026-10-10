import LOOConcentrationRevision.FunctionalInequalities.SquareEntropy
import LOOConcentrationRevision.FunctionalInequalities.LogSobolevConstant
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.EReal.Operations

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem squareEntropy_eq_of_integrable_density (f : Lp ℝ 2 μ)
    (hf : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ) :
    squareEntropy μ f = ENNReal.ofReal
      ((∫ x, (f x)^2 * Real.log ((f x)^2) ∂μ) -
        (∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ)) := by
  have hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.2).ne
  have hn := (squareEntropy_negative_part_lt_top f).ne
  dsimp only [squareEntropy]
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, ← EReal.coe_sub,
    ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  rfl

theorem mean_sq_mul_log_le_integral_density (f : Lp ℝ 2 μ)
    (hf : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ) :
    (∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ) ≤
      ∫ x, (f x)^2 * Real.log ((f x)^2) ∂μ := by
  exact Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici (Eventually.of_forall fun x => sq_nonneg (f x)) (integrable_sq f) hf

/-- Finite positive density integral suffices since the negative part is uniformly bounded. -/
theorem integrable_density_of_positive_part_ne_top (f : Lp ℝ 2 μ)
    (hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) ≠ ⊤) :
    Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ := by
  have hm : AEStronglyMeasurable (fun x => (f x)^2 * Real.log ((f x)^2)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable (integrable_sq f).aestronglyMeasurable
  have hip : Integrable (fun x => max ((f x)^2 * Real.log ((f x)^2)) 0) μ := by
    simpa only [ENNReal.toReal_ofReal'] using
      integrable_toReal_of_lintegral_ne_top hm.aemeasurable.ennreal_ofReal hp
  apply (hip.add (integrable_const (Real.exp (-1)))).mono' hm
  apply Eventually.of_forall
  intro x
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := neg_mul_log_le_exp_neg_one (sq_nonneg (f x))
    have hmax : 0 ≤ max ((f x)^2 * Real.log ((f x)^2)) 0 := le_max_right _ _
    linarith only [h, hmax]
  · have h := le_max_left ((f x)^2 * Real.log ((f x)^2)) 0
    have hpos := (Real.exp_pos (-1)).le
    linarith only [h, hpos]

/-- Infinite positive entropy density retains its literal extended value. -/
theorem squareEntropy_eq_top_of_positive_part_eq_top (f : Lp ℝ 2 μ)
    (hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) = ⊤) :
    squareEntropy μ f = ⊤ := by
  dsimp only [squareEntropy]
  rw [hp, EReal.coe_ennreal_top,
    EReal.top_sub (by simpa only [ne_eq, EReal.coe_ennreal_eq_top_iff] using
      (squareEntropy_negative_part_lt_top f).ne),
    EReal.top_sub_coe, EReal.toENNReal_top]

theorem squareEntropy_lt_top_iff_integrable_density (f : Lp ℝ 2 μ) :
    squareEntropy μ f < ⊤ ↔ Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ := by
  constructor
  · intro h
    apply integrable_density_of_positive_part_ne_top f
    intro hp
    exact h.ne (squareEntropy_eq_top_of_positive_part_eq_top f hp)
  · intro hf
    rw [squareEntropy_eq_of_integrable_density f hf]
    exact ENNReal.ofReal_lt_top

/-- Jensen's inequality prevents the ENNReal conversion from discarding a negative entropy. -/
theorem squareEntropy_expression_nonneg (f : Lp ℝ 2 μ) :
    0 ≤ ((∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-((f x)^2 * Real.log ((f x)^2))) ∂μ : ℝ≥0∞) : EReal) -
      (((∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ) : ℝ) : EReal) := by
  by_cases hf : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ
  · have hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) ≠ ⊤ :=
      ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.2).ne
    have hn := (squareEntropy_negative_part_lt_top f).ne
    rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_sub, ← EReal.coe_sub,
      ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    exact EReal.coe_nonneg.mpr (sub_nonneg.mpr (mean_sq_mul_log_le_integral_density f hf))
  · have hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) = ⊤ := by
      by_contra h
      exact hf (integrable_density_of_positive_part_ne_top f h)
    rw [hp, EReal.coe_ennreal_top,
      EReal.top_sub (by simpa only [ne_eq, EReal.coe_ennreal_eq_top_iff] using
        (squareEntropy_negative_part_lt_top f).ne), EReal.top_sub_coe]
    exact le_top

/-- The frozen extended entropy equals the literal, nonnegative source expression. -/
theorem coe_squareEntropy_eq_expression (f : Lp ℝ 2 μ) :
    (squareEntropy μ f : EReal) =
      ((∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-((f x)^2 * Real.log ((f x)^2))) ∂μ : ℝ≥0∞) : EReal) -
      (((∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ) : ℝ) : EReal) := by
  exact EReal.coe_toENNReal (squareEntropy_expression_nonneg f)

/-- Literal entropy density becomes integrable in the actual positive-energy LSI consumer. -/
theorem integrable_density_of_energy_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure ν]
    (hfinite : logSobolevConstant ν < ⊤) (u : SobolevPair ν)
    (henergy : 0 < sobolevEnergy ν u) :
    Integrable (fun x => (((WithLp.ofLp u.val).1 : Lp ℝ 2 ν) x)^2 *
      Real.log ((((WithLp.ofLp u.val).1 : Lp ℝ 2 ν) x)^2)) ν :=
  (squareEntropy_lt_top_iff_integrable_density (WithLp.ofLp u.val).1).mp
    (squareEntropy_lt_top_of_energy_pos hfinite u henergy)

end LOOConcentration.Revision
