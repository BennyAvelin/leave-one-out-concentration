import LOOConcentrationRevision.Concentration.SourceProductMgfAllSizes
import LOOConcentrationRevision.Concentration.Chernoff
import LOOConcentrationRevision.Concentration.CertifiedGaussianChernoff
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal

/-- The source quadratic-gradient corollary for the actual centered function
on the Euclidean product law. The positive-growth branch is the literal
Theta rate; zero growth keeps the sharp Gaussian coefficient, and zero LSI
uses the internally proved zero-proxy endpoint. -/
theorem source_product_theta_tails
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (hr : 1 ≤ r)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hLCfin : logSobolevConstant μ ≠ ⊤)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin r × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ a + b * ‖x‖)
    (t : ℝ) (ht : 0 < t) :
    let ν := euclideanProductLaw (κ := Fin r) μ
    let C := (logSobolevConstant μ).toReal
    let M₂ := ∫ x, ‖x‖ ^ 2 ∂μ
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg (fun x => sq_nonneg (‖x‖ : ℝ))) r hr t ht a b ha hb
    let gaussian := if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))
    ν.real {x | F x - ∫ y, F y ∂ν > t} ≤ (if b = 0 then gaussian else θ) ∧
    ν.real {x | ∫ y, F y ∂ν - F x > t} ≤ (if b = 0 then gaussian else θ) := by
  dsimp only
  let ν := euclideanProductLaw (κ := Fin r) μ
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact euclideanProductLaw_isProbabilityMeasure μ
  let C : ℝ := (logSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ x, ‖x‖ ^ 2 ∂μ
  let aN : NNReal := ⟨a, ha⟩
  let bN : NNReal := ⟨b, hb⟩
  have hcoeA : (aN : ℝ) = a := rfl
  have hcoeB : (bN : ℝ) = b := rfl
  let X : EuclideanSpace ℝ (Fin r × ι) → ℝ := fun x => F x - ∫ y, F y ∂ν
  let θ := thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg (fun x => sq_nonneg (‖x‖ : ℝ))) r hr t ht a b ha hb
  let gaussian := if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal C := by
    dsimp [C]
    rw [ENNReal.ofReal_toReal hLCfin]
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg (fun x => sq_nonneg (‖x‖ : ℝ))
  have hgradN : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (aN : ℝ) + (bN : ℝ) * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    simpa only [hcoeA, hcoeB] using hx
  by_cases hC0 : C = 0
  · have hLC0 : logSobolevConstant μ = 0 := by
      have hle : logSobolevConstant μ ≤ 0 := by simpa [C, hC0] using hLC
      exact le_antisymm hle bot_le
    have hmgf (s : ℝ) :
        Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂ν))) ν ∧
          (∫ x, Real.exp (s * (F x - ∫ y, F y ∂ν)) ∂ν) = 1 := by
      cases r with
      | zero => omega
      | succ n =>
        have h := source_product_centered_mgf_zero_constant_via_truncation
          n μ hLC0 hM2 F s
        exact ⟨h.2.1, h.2.2.1⟩
    have hzero : ProbabilityTheory.HasSubgaussianMGF X 0 ν := by
      constructor
      · intro s
        simpa [X, ν] using (hmgf s).1
      · intro s
        have hs := (hmgf s).2
        simpa [ProbabilityTheory.mgf, X, ν] using hs.le
    have htails := strict_tails_le_of_subgaussianMGF_via_certified_chernoff ν X 0 hzero t ht
    constructor
    · simpa [gaussian, θ, C, M₂, hC0, X, ν, thetaRate] using htails.1
    · simpa [gaussian, θ, C, M₂, hC0, X, ν, thetaRate] using htails.2
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hgaussian : b = 0 → ∀ s : ℝ,
        Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂ν))) ν ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
          Real.exp ((C * a ^ 2 / 2) * s ^ 2) := by
      intro hb0 s
      have hgrad0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (aN : ℝ) := by
        filter_upwards [hgrad] with x hx
        simpa only [hcoeA, hcoeB, hb0, zero_mul, add_zero] using hx
      have hmgf := source_product_centered_mgf_bounded_gradient_all_sizes
        r μ C hC hLC hM2 F hloc aN hgrad0 s
      refine ⟨?_, ?_⟩
      · simpa [X, ν] using hmgf.2.1
      · have hs := hmgf.2.2.1
        simpa only [hcoeA] using hs
    have hcutoff : 0 < b → ∀ s : ℝ, |s| ≤ 1 / (4 * C * b) →
        Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂ν))) ν ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
          Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2) := by
      intro hbpos s hs
      have hbN : 0 < (bN : ℝ) := by rw [hcoeB]; exact hbpos
      have hmgf := source_product_centered_mgf_positive_growth_all_sizes
        r μ C hC hLC hM2 F hloc aN bN hbN hgradN s hs
      refine ⟨?_, ?_⟩
      · simpa [ν] using hmgf.2.1
      · have hbound := hmgf.2.2.1
        simpa only [hcoeA, hcoeB, M₂] using hbound
    have htails := chernoff_revision_thetaRate_of_quadraticMGF
      ν F C M₂ hCpos hM₂ r hr t ht a b ha hb hgaussian hcutoff
    by_cases hb0 : b = 0
    · have hgrad0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (aN : ℝ) := by
        filter_upwards [hgrad] with x hx
        simpa only [hcoeA, hcoeB, hb0, zero_mul, add_zero] using hx
      have hmgf := source_product_centered_mgf_bounded_gradient_all_sizes
        r μ C hC hLC hM2 F hloc aN hgrad0
      let proxy : NNReal := ⟨C * a ^ 2, mul_nonneg hC (sq_nonneg a)⟩
      have hproxyVal : (proxy : ℝ) = C * a ^ 2 := rfl
      have hproxy : ProbabilityTheory.HasSubgaussianMGF X proxy ν := by
        constructor
        · intro s
          simpa [X, ν] using (hmgf s).2.1
        · intro s
          have hs := (hmgf s).2.2.1
          have hbound :
              (∫ x, Real.exp (s * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
                Real.exp (((proxy : ℝ) * s ^ 2) / 2) := by
            calc
              _ ≤ Real.exp ((C * (aN : ℝ) ^ 2 / 2) * s ^ 2) := hs
              _ = Real.exp (((proxy : ℝ) * s ^ 2) / 2) := by
                congr 1
                rw [hcoeA, hproxyVal]
                ring
          simpa [ProbabilityTheory.mgf, X, ν] using hbound
      have hproxyZero : proxy = 0 ↔ a = 0 := by
        constructor
        · intro hp
          have hp' : (proxy : ℝ) = 0 := congrArg (fun q : NNReal => (q : ℝ)) hp
          rw [hproxyVal] at hp'
          rcases mul_eq_zero.mp hp' with hCzero | haSq
          · exact (hCpos.ne' hCzero).elim
          · exact sq_eq_zero_iff.mp haSq
        · intro ha0
          apply Subtype.ext
          simp [proxy, ha0]
      have hrate :
          (if proxy = 0 then 0 else Real.exp (-(t ^ 2 / (2 * (proxy : ℝ))))) = gaussian := by
        by_cases ha0 : a = 0
        · simp [hproxyZero, ha0, gaussian, C]
        · have hCaa : C * a ^ 2 ≠ 0 := mul_ne_zero hCpos.ne' (pow_ne_zero 2 ha0)
          simp only [hproxyZero, if_neg ha0, gaussian, if_neg hCaa]
          congr 1
          congr 1
          rw [hproxyVal]
          ring
      have hgaussianOut :
          gaussian =
            (if C = 0 ∨ a = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) := by
        by_cases ha0 : a = 0
        · simp [gaussian, ha0]
        · have hCaa : C * a ^ 2 ≠ 0 := mul_ne_zero hCpos.ne' (pow_ne_zero 2 ha0)
          simp [gaussian, hC0, ha0, hCaa]
      have hsharp := strict_tails_le_of_subgaussianMGF_via_certified_chernoff ν X proxy hproxy t ht
      constructor
      · simpa [hb0, θ, C, M₂, X, ν, hrate, hgaussianOut] using hsharp.1
      · simpa [hb0, θ, C, M₂, X, ν, hrate, hgaussianOut] using hsharp.2
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      constructor
      · simpa [hb0, θ, gaussian, C, M₂, ν] using htails.1
      · simpa [hb0, θ, gaussian, C, M₂, ν] using htails.2

end LOOConcentration.Revision
