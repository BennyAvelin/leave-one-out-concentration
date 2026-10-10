import LOOConcentrationRevision.Concentration.LipschitzHerbst

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The whole integrable Lipschitz class has the same standard MGF interface. -/
theorem lipschitz_hasSubgaussianMGF_of_constant_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal)
    (hLip : LipschitzWith L F) (hF : Integrable F μ) :
    ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ)
      (NNReal.mk (C * (L : ℝ)^2) (mul_nonneg hC (sq_nonneg _))) μ := by
  constructor
  · intro t
    exact (lipschitz_centered_exp_integrable_and_mgf_le μ C hC hLC F L hLip hF t).1
  · intro t
    have h := (lipschitz_centered_exp_integrable_and_mgf_le μ C hC hLC F L hLip hF t).2
    change (∫ x, Real.exp (t * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
      Real.exp ((C * (L : ℝ)^2) * t^2 / 2)
    exact h.trans_eq (congrArg Real.exp (by ring))

private theorem strict_tail_le_of_hasSubgaussianMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (c : NNReal) (h : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (t : ℝ) (ht : 0 < t) :
    μ.real {x | X x > t} ≤ if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ)))) := by
  by_cases hc : c = 0
  · subst c
    rw [if_pos rfl]
    have hae := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hz : μ {x | X x > t} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with x hx
      change ¬ t < X x
      change X x = 0 at hx
      rw [hx]
      exact not_lt_of_ge ht.le
    simp only [measureReal_def, hz, ENNReal.toReal_zero, le_refl]
  · rw [if_neg hc]
    exact (measureReal_mono (μ := μ) (s₁ := {x | X x > t}) (s₂ := {x | X x ≥ t}) (fun _ hx => le_of_lt (show t < X _ from hx))).trans (by
      simpa only [neg_div] using h.measure_ge_le ht.le)

/-- Chernoff gives both strict tails, with the genuine zero-proxy endpoint. -/
theorem strict_tails_le_of_hasSubgaussianMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (c : NNReal) (h : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (t : ℝ) (ht : 0 < t) :
    (μ.real {x | X x > t} ≤ if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) ∧
    (μ.real {x | -X x > t} ≤ if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) :=
  ⟨strict_tail_le_of_hasSubgaussianMGF μ X c h t ht,
    strict_tail_le_of_hasSubgaussianMGF μ (-X) c h.neg t ht⟩

/-- The actual integrable Lipschitz observable has both centered strict tails. -/
theorem lipschitz_centered_strict_tails_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal)
    (hLip : LipschitzWith L F) (hF : Integrable F μ)
    (t : ℝ) (ht : 0 < t) :
    let c : NNReal := ⟨C * (L : ℝ)^2, mul_nonneg hC (sq_nonneg _)⟩
    (μ.real {x | F x - ∫ y, F y ∂μ > t} ≤
      if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) ∧
    (μ.real {x | -(F x - ∫ y, F y ∂μ) > t} ≤
      if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) := by
  exact strict_tails_le_of_hasSubgaussianMGF μ _ _
    (lipschitz_hasSubgaussianMGF_of_constant_bound μ C hC hLC F L hLip hF) t ht

/-- The literal whole-class infimum of finite variance proxies is bounded by
 the intrinsic LSI constant; no alternative source constant is introduced. -/
theorem sInf_integrable_lipschitz_subgaussian_proxies_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ ≠ ⊤) :
    sInf {c : ENNReal | ∃ c₀ : NNReal, c = (c₀ : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c₀ μ} ≤
      logSobolevConstant μ := by
  let c₀ : NNReal := (logSobolevConstant μ).toNNReal
  have hc : (c₀ : ENNReal) = logSobolevConstant μ := ENNReal.coe_toNNReal hfinite
  rw [← hc]
  apply sInf_le
  refine ⟨c₀, rfl, ?_⟩
  intro F hF hLip
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal (c₀ : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, hc]
  have h := lipschitz_hasSubgaussianMGF_of_constant_bound μ (c₀ : ℝ) c₀.property hLC F 1 hLip hF
  have hp : NNReal.mk ((c₀ : ℝ) * ((1 : NNReal) : ℝ)^2)
      (mul_nonneg c₀.property (sq_nonneg _)) = c₀ := by
    apply Subtype.ext
    simp
  rw [hp] at h
  exact h

/-- A global actual gradient bound supplies the Lipschitz premise internally. -/
theorem differentiable_centered_strict_tails_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal)
    (hF : Differentiable ℝ F) (hGrad : ∀ x, ‖gradient F x‖ ≤ (L : ℝ))
    (hInt : Integrable F μ) (t : ℝ) (ht : 0 < t) :
    let c : NNReal := ⟨C * (L : ℝ)^2, mul_nonneg hC (sq_nonneg _)⟩
    (μ.real {x | F x - ∫ y, F y ∂μ > t} ≤
      if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) ∧
    (μ.real {x | -(F x - ∫ y, F y ∂μ) > t} ≤
      if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c : ℝ))))) := by
  have hLip : LipschitzWith L F := lipschitzWith_of_nnnorm_fderiv_le hF (fun x => by
    change ‖fderiv ℝ F x‖ ≤ (L : ℝ)
    have heq : ‖gradient F x‖ = ‖fderiv ℝ F x‖ :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map _
    rw [← heq]
    exact hGrad x)
  exact lipschitz_centered_strict_tails_le μ C hC hLC F L hLip hInt t ht

end LOOConcentration.Revision
