import LOOConcentrationRevision.Probability.IndicatorVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

/-- The source's normalized restriction of a probability law to a positive-mass set. -/
noncomputable def normalizedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : Set α) : Measure α := (μ K)⁻¹ • μ.restrict K

/-- A measurable restriction of positive mass, with its source normalization, is a probability. -/
theorem normalizedRestriction_isProbability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Set α)
    (hq : 0 < μ.real K) : IsProbabilityMeasure (normalizedRestriction μ K) := by
  have hK0 : μ K ≠ 0 := by
    intro h
    have hz : μ.real K = 0 := by simp [Measure.real, h]
    exact (ne_of_gt hq) hz
  refine ⟨?_⟩
  rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter]
  exact ENNReal.inv_mul_cancel hK0 (measure_ne_top μ K)

/-- Integrals under the normalized restriction are the restricted integrals divided by `μ K`. -/
theorem integral_normalizedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Set α)
    (hq : 0 < μ.real K) (F : α → ℝ) (hF : MemLp F 2 μ) :
    Integrable F (normalizedRestriction μ K) ∧
      ∫ x, F x ∂normalizedRestriction μ K =
        (μ.real K)⁻¹ * ∫ x in K, F x ∂μ := by
  have hK0 : μ K ≠ 0 := by
    intro h
    have hz : μ.real K = 0 := by simp [Measure.real, h]
    exact (ne_of_gt hq) hz
  have hFint : Integrable F (μ.restrict K) := by
    exact (hF.integrable (by norm_num)).restrict
  have hFinv : (μ K)⁻¹ ≠ (⊤ : ENNReal) := by
    exact ENNReal.inv_ne_top.mpr hK0
  have hFcond : Integrable F (normalizedRestriction μ K) := by
    exact hFint.smul_measure hFinv
  refine ⟨hFcond, ?_⟩
  rw [normalizedRestriction, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  rw [show (μ K).toReal = μ.real K by rfl]

/-- Cauchy--Schwarz for two actual real `L²` functions, with coefficient one. -/
theorem integral_mul_abs_le_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hfa : MemLp (fun x => |f x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    convert (show MemLp (fun x => |f x|) 2 μ from by
      simpa only [Real.norm_eq_abs] using hf.norm) using 1; norm_num
  have hga : MemLp (fun x => |g x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    convert (show MemLp (fun x => |g x|) 2 μ from by
      simpa only [Real.norm_eq_abs] using hg.norm) using 1; norm_num
  have hprod : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ fun _ => abs_nonneg _) hfa hga
  have hpowf : ∫ x, |f x| ^ (2 : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    calc
      _ = ∫ x, |f x| ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => Real.rpow_two _
      _ = ∫ x, f x ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => sq_abs _
  have hpowg : ∫ x, |g x| ^ (2 : ℝ) ∂μ = ∫ x, g x ^ 2 ∂μ := by
    calc
      _ = ∫ x, |g x| ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => Real.rpow_two _
      _ = ∫ x, g x ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => sq_abs _
  calc
    |∫ x, f x * g x ∂μ| = ‖∫ x, f x * g x ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, |f x| * |g x| ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [Real.norm_eq_abs]
    _ ≤ (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2) *
        (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / 2) := hholder
    _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
      rw [hpowf, hpowg, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- Exact conditional-mean shift on an arbitrary probability space, using its actual variance. -/
theorem conditional_mean_shift_of_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Set α) (hK : MeasurableSet K)
    (F : α → ℝ) (hF : MemLp F 2 μ) (hq : 0 < μ.real K) :
    |∫ x, F x ∂normalizedRestriction μ K - ∫ x, F x ∂μ| ≤
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        (Real.sqrt (μ.real Kᶜ * (1 - μ.real Kᶜ)) / (1 - μ.real Kᶜ)) := by
  let m : ℝ := ∫ x, F x ∂μ
  let q : ℝ := μ.real K
  let I : α → ℝ := K.indicator (fun _ => (1 : ℝ))
  let Fc : α → ℝ := fun x => F x - m
  let Ic : α → ℝ := fun x => I x - q
  have hFint : Integrable F μ := hF.integrable (by norm_num)
  have hMconst : Integrable (fun _ : α => m) μ := integrable_const _
  have hprobK : IsProbabilityMeasure (normalizedRestriction μ K) :=
    normalizedRestriction_isProbability μ K hq
  have hfiniteK : IsFiniteMeasure (normalizedRestriction μ K) := by
    refine ⟨?_⟩
    rw [hprobK.measure_univ]
    norm_num
  have hFc : MemLp Fc 2 μ := by
    exact hF.sub (memLp_const m)
  have hIc : MemLp Ic 2 μ := by
    have hI : MemLp I 2 μ := by
      dsimp [I]
      exact (memLp_const (1 : ℝ)).indicator hK
    exact hI.sub (memLp_const q)
  have hFcInt : Integrable Fc μ := hFc.integrable (by norm_num)
  have hFcMean : ∫ x, Fc x ∂μ = 0 := by
    dsimp [Fc, m]
    rw [integral_sub hFint hMconst, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  have hFcMeanK := integral_normalizedRestriction μ K hq Fc hFc
  have hFcond := (integral_normalizedRestriction μ K hq F hF).1
  have hMcond : Integrable (fun _ : α => m) (normalizedRestriction μ K) :=
    (integrable_const_iff).2 (Or.inr hfiniteK)
  have hCondCenter : ∫ x, Fc x ∂normalizedRestriction μ K =
      ∫ x, F x ∂normalizedRestriction μ K - m := by
    change ∫ x, (F x - m) ∂normalizedRestriction μ K = _
    rw [integral_sub hFcond hMcond, integral_const]
    simp only [Measure.real, hprobK.measure_univ, ENNReal.toReal_one, one_smul]
  have hVarI := centered_indicator_variance μ K hK
  have hI : MemLp I 2 μ := by
    dsimp [I]
    exact (memLp_const (1 : ℝ)).indicator hK
  have hCovSet : ∫ x, Fc x * Ic x ∂μ = ∫ x in K, Fc x ∂μ := by
    have hprodI : Integrable (fun x => Fc x * I x) μ := hFc.integrable_mul hI
    have hprodq : Integrable (fun x => q * Fc x) μ := hFcInt.const_mul q
    have hFcI : ∫ x, Fc x * I x ∂μ = ∫ x in K, Fc x ∂μ := by
      calc
        _ = ∫ x, K.indicator Fc x ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by by_cases hx : x ∈ K <;> simp [I, hx]
        _ = ∫ x in K, Fc x ∂μ := integral_indicator hK
    calc
      ∫ x, Fc x * Ic x ∂μ = ∫ x, Fc x * I x - q * Fc x ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp [Ic]; ring
      _ = (∫ x, Fc x * I x ∂μ) - ∫ x, q * Fc x ∂μ := integral_sub hprodI hprodq
      _ = (∫ x in K, Fc x ∂μ) - q * ∫ x, Fc x ∂μ := by
        rw [hFcI, integral_const_mul]
      _ = ∫ x in K, Fc x ∂μ := by rw [hFcMean]; ring
  have hCovIdentity :
      ∫ x, F x ∂normalizedRestriction μ K - m =
        q⁻¹ * ∫ x, Fc x * Ic x ∂μ := by
    rw [← hCondCenter, hFcMeanK.2, hCovSet]
  have hCS := integral_mul_abs_le_sqrt μ Fc Ic hFc hIc
  have hratio : 0 < q := by simpa [q] using hq
  have hshift :
      |∫ x, F x ∂normalizedRestriction μ K - m| ≤
        Real.sqrt (∫ x, Fc x ^ 2 ∂μ) * (Real.sqrt (μ.real Kᶜ * (1 - μ.real Kᶜ)) / q) := by
    rw [hCovIdentity, abs_mul, abs_of_pos (inv_pos.mpr hratio)]
    calc
      q⁻¹ * |∫ x, Fc x * Ic x ∂μ| ≤
          q⁻¹ * (Real.sqrt (∫ x, Fc x ^ 2 ∂μ) * Real.sqrt (∫ x, Ic x ^ 2 ∂μ)) :=
            mul_le_mul_of_nonneg_left hCS (inv_nonneg.mpr hratio.le)
      _ = Real.sqrt (∫ x, Fc x ^ 2 ∂μ) *
          (Real.sqrt (μ.real Kᶜ * (1 - μ.real Kᶜ)) / q) := by
        rw [show (∫ x, Ic x ^ 2 ∂μ) = μ.real Kᶜ * (1 - μ.real Kᶜ) by
          simpa [Ic, I, q] using hVarI]
        ring
  have hqeq : μ.real K = 1 - μ.real Kᶜ := by
    linarith [probReal_add_probReal_compl (μ := μ) hK]
  simpa [m, Fc, q, hqeq] using hshift

#print axioms LOOConcentration.Revision.centered_indicator_variance
#print axioms LOOConcentration.Revision.integral_mul_abs_le_sqrt
#print axioms LOOConcentration.Revision.conditional_mean_shift_of_memLp

end LOOConcentration.Revision
