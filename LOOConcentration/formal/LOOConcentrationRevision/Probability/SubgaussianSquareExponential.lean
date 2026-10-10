import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal NNReal

private theorem auxiliary_gaussian_square_lintegral_le_two
    (c : ℝ) (hc : 0 < c) :
    ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (c * y ^ 2 / 2)) ∂
      ProbabilityTheory.gaussianReal 0 (⟨1 / (4 * c), by positivity⟩ : ℝ≥0) ≤ 2 := by
  let v : ℝ≥0 := ⟨1 / (4 * c), by positivity⟩
  have hv : (v : ℝ) = 1 / (4 * c) := rfl
  have hvne : v ≠ 0 := by
    intro h
    have h' : (v : ℝ) = 0 := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [hv] at h'
    have : 0 < 1 / (4 * c) := by positivity
    linarith
  have hdecay : 0 < 3 * c / 2 := by positivity
  have hform : (fun y : ℝ => ProbabilityTheory.gaussianPDFReal 0 v y *
      Real.exp (c * y ^ 2 / 2)) = fun y =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(3 * c / 2) * y ^ 2) := by
    funext y
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [sub_zero]
    calc
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-y ^ 2 / (2 * (v : ℝ))) * Real.exp (c * y ^ 2 / 2) =
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          (Real.exp (-y ^ 2 / (2 * (v : ℝ))) * Real.exp (c * y ^ 2 / 2)) := by ring
      _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-y ^ 2 / (2 * (v : ℝ)) + c * y ^ 2 / 2) := by rw [← Real.exp_add]
      _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-(3 * c / 2) * y ^ 2) := by
            congr 2
            rw [hv]
            field_simp
            ring
  have hweight : Integrable
      (fun y : ℝ => ProbabilityTheory.gaussianPDFReal 0 v y *
        Real.exp (c * y ^ 2 / 2)) volume := by
    rw [hform]
    exact (integrable_exp_neg_mul_sq hdecay).const_mul _
  have hformula : ∀ y : ℝ,
      ProbabilityTheory.gaussianPDF 0 v y *
        ENNReal.ofReal (Real.exp (c * y ^ 2 / 2)) =
      ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal 0 v y *
        Real.exp (c * y ^ 2 / 2)) := by
    intro y
    rw [ProbabilityTheory.gaussianPDF]
    rw [← ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg 0 v y)]
  have hgaussInt :
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (c * y ^ 2 / 2)) ∂
        ProbabilityTheory.gaussianReal 0 v) =
      ENNReal.ofReal (Real.sqrt (4 / 3)) := by
    calc
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (c * y ^ 2 / 2)) ∂
          ProbabilityTheory.gaussianReal 0 v)
          = ∫⁻ y : ℝ, ProbabilityTheory.gaussianPDF 0 v y *
              ENNReal.ofReal (Real.exp (c * y ^ 2 / 2)) := by
            rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hvne,
              lintegral_withDensity_eq_lintegral_mul volume
                (ProbabilityTheory.measurable_gaussianPDF 0 v)
                (by fun_prop)]
            rfl
      _ = ∫⁻ y : ℝ, ENNReal.ofReal
            (ProbabilityTheory.gaussianPDFReal 0 v y *
              Real.exp (c * y ^ 2 / 2)) := by
            apply lintegral_congr
            exact hformula
      _ = ENNReal.ofReal (∫ y : ℝ,
            ProbabilityTheory.gaussianPDFReal 0 v y *
              Real.exp (c * y ^ 2 / 2)) :=
            (ofReal_integral_eq_lintegral_ofReal hweight
              (ae_of_all _ fun y => mul_nonneg
                (ProbabilityTheory.gaussianPDFReal_nonneg 0 v y)
                (Real.exp_pos _).le)).symm
      _ = ENNReal.ofReal (Real.sqrt (4 / 3)) := by
            congr 2
            rw [hform]
            rw [integral_const_mul, integral_gaussian]
            rw [hv]
            have hconst :
                (Real.sqrt (2 * Real.pi * (1 / (4 * c))))⁻¹ *
                    Real.sqrt (Real.pi / (3 * c / 2)) = Real.sqrt (4 / 3) := by
              have h1 : 0 < 2 * Real.pi * (1 / (4 * c)) := by positivity
              have h2 : 0 < Real.pi / (3 * c / 2) := by positivity
              have h3 : (0 : ℝ) < 4 / 3 := by norm_num
              apply (sq_eq_sq₀ (by positivity) (by positivity)).1
              rw [mul_pow, inv_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le,
                Real.sq_sqrt h3.le]
              field_simp
            exact hconst
  have hroot : Real.sqrt (4 / 3) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  rw [hgaussInt]
  simpa using ENNReal.ofReal_le_ofReal hroot

/-- A sub-Gaussian MGF controls the actual exponential square integral at
the stated scale. The auxiliary Gaussian is used only to represent the
pointwise exponential square through its MGF. -/
theorem subgaussian_square_exponential_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hSG : ProbabilityTheory.HasSubgaussianMGF X c μ) :
    Integrable (fun x => Real.exp ((X x) ^ 2 / (8 * (c : ℝ)))) μ ∧
      (∫ x, Real.exp ((X x) ^ 2 / (8 * (c : ℝ))) ∂μ) ≤ 2 := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  let v : ℝ≥0 := ⟨1 / (4 * (c : ℝ)), by positivity⟩
  let γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 v
  have hv : (v : ℝ) = 1 / (4 * (c : ℝ)) := rfl
  have hvne : v ≠ 0 := by
    intro h
    have h' : (v : ℝ) = 0 := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [hv] at h'
    have hp : 0 < 1 / (4 * (c : ℝ)) := by positivity
    linarith
  let F : α → ℝ := fun x => Real.exp ((X x) ^ 2 / (8 * (c : ℝ)))
  let K : α → ℝ → ℝ≥0∞ := fun x y => ENNReal.ofReal (Real.exp (y * X x))
  have hpoint (x : α) :
      ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (y * X x)) ∂γ =
        ENNReal.ofReal (F x) := by
    have hInt : Integrable (fun y : ℝ => Real.exp (y * X x)) γ := by
      convert ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := v) (X x) using 1
      funext y
      congr 1
      ring
    have hmgf := congrFun
      (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := v)) (X x)
    have hmgf' :
        ∫ y : ℝ, Real.exp (y * X x) ∂γ =
          Real.exp ((v : ℝ) * (X x) ^ 2 / 2) := by
      calc
        (∫ y : ℝ, Real.exp (y * X x) ∂γ) =
            ∫ y : ℝ, Real.exp ((X x) * y) ∂γ := by
              apply integral_congr_ae
              filter_upwards [Filter.Eventually.of_forall (fun _ : ℝ => True.intro)] with y _
              rw [mul_comm]
        _ = Real.exp ((v : ℝ) * (X x) ^ 2 / 2) := by
              change ProbabilityTheory.mgf id γ (X x) = _ at hmgf
              simpa [ProbabilityTheory.mgf, γ] using hmgf
    calc
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (y * X x)) ∂γ) =
          ENNReal.ofReal (∫ y : ℝ, Real.exp (y * X x) ∂γ) := by
            symm
            apply ofReal_integral_eq_lintegral_ofReal hInt
            exact ae_of_all _ fun y => (Real.exp_pos _).le
      _ = ENNReal.ofReal (F x) := by
            apply congrArg ENNReal.ofReal
            rw [hmgf']
            apply congrArg Real.exp
            rw [hv]
            field_simp [ne_of_gt hcR]
            ring
  have hKmeas : AEMeasurable (Function.uncurry K) (μ.prod γ) := by
    have hXfst : AEMeasurable (fun p : α × ℝ => X p.1) (μ.prod γ) :=
      hSG.aemeasurable.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := γ))
    dsimp [Function.uncurry, K]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable
        (measurable_snd.aemeasurable.mul hXfst))
  have hswap :
      (∫⁻ x, ∫⁻ y, K x y ∂γ ∂μ) =
        ∫⁻ y, ∫⁻ x, K x y ∂μ ∂γ :=
    lintegral_lintegral_swap (μ := μ) (ν := γ) hKmeas
  have hinner (y : ℝ) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (y * X x)) ∂μ) ≤
        ENNReal.ofReal (Real.exp ((c : ℝ) * y ^ 2 / 2)) := by
    calc
      (∫⁻ x, ENNReal.ofReal (Real.exp (y * X x)) ∂μ) =
          ENNReal.ofReal (ProbabilityTheory.mgf X μ y) := by
            symm
            rw [← ofReal_integral_eq_lintegral_ofReal (hSG.integrable_exp_mul y)
              (ae_of_all _ fun x => (Real.exp_pos _).le)]
            rfl
      _ ≤ ENNReal.ofReal (Real.exp ((c : ℝ) * y ^ 2 / 2)) :=
        ENNReal.ofReal_le_ofReal (hSG.mgf_le y)
  have hlin :
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ 2 := by
    calc
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) =
          ∫⁻ x, ∫⁻ y, K x y ∂γ ∂μ := by
            apply lintegral_congr
            intro x
            simpa [K, F] using (hpoint x).symm
      _ = ∫⁻ y, ∫⁻ x, K x y ∂μ ∂γ := hswap
      _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp ((c : ℝ) * y ^ 2 / 2)) ∂γ := by
            apply lintegral_mono
            intro y
            exact hinner y
      _ ≤ 2 := by
            simpa [γ, v] using auxiliary_gaussian_square_lintegral_le_two
              (c : ℝ) hcR
  have hFmeas : AEStronglyMeasurable F μ := by
    have hmeas : Measurable (fun z : ℝ => Real.exp (z ^ 2 / (8 * (c : ℝ)))) := by
      fun_prop
    exact (hmeas.comp_aemeasurable hSG.aemeasurable).aestronglyMeasurable
  have hFnonneg : 0 ≤ᵐ[μ] F := ae_of_all _ fun x => (Real.exp_pos _).le
  have hfinite : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hlin (by norm_num : (2 : ℝ≥0∞) < ∞)
  have hIntF : Integrable F μ :=
    (lintegral_ofReal_ne_top_iff_integrable hFmeas hFnonneg).mp hfinite
  have hEq := ofReal_integral_eq_lintegral_ofReal hIntF hFnonneg
  have hbound : (∫ x, F x ∂μ) ≤ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp
    calc
      ENNReal.ofReal (∫ x, F x ∂μ) = ∫⁻ x, ENNReal.ofReal (F x) ∂μ := hEq
      _ ≤ ENNReal.ofReal 2 := by simpa using hlin
  exact ⟨by simpa [F] using hIntF, by simpa [F] using hbound⟩

example {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hSG : ProbabilityTheory.HasSubgaussianMGF X c μ) :
    Integrable (fun x => Real.exp ((X x) ^ 2 / (8 * (c : ℝ)))) μ ∧
      (∫ x, Real.exp ((X x) ^ 2 / (8 * (c : ℝ))) ∂μ) ≤ 2 := by
  exact subgaussian_square_exponential_bound μ X c hc hSG

private theorem zero_proxy_exp_square_integrable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ)
    (hSG : ProbabilityTheory.HasSubgaussianMGF X 0 μ) :
    Integrable (fun x => Real.exp ((X x) ^ 2)) μ ∧
      (∫ x, Real.exp ((X x) ^ 2) ∂μ) = 1 := by
  have hzero := hSG.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hEq : (fun x => Real.exp ((X x) ^ 2)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hzero] with x hx
    rw [hx]
    simp
  refine ⟨(integrable_const (1 : ℝ)).congr hEq.symm, ?_⟩
  calc
    (∫ x, Real.exp ((X x) ^ 2) ∂μ) = ∫ x, (1 : ℝ) ∂μ := integral_congr_ae hEq
    _ = 1 := by simp

#print axioms subgaussian_square_exponential_bound
#print axioms zero_proxy_exp_square_integrable

end LOOConcentration.Revision
