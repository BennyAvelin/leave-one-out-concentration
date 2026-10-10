import LOOConcentrationManuscript.Internal.GenericScaledThetaUpperBounds
import LOOConcentrationRevision.Frozen.Results.MainConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual uniform main bound gives exponential concentration for the
source rates, bounded expected-loss growth coefficients, and an arbitrary
source bias tending to zero. Nonzero growth coefficients remain allowed. -/
theorem generic_uniform_main_source_exponential
    (σ M₂ A B D : NNReal) (ε : ℝ) (hε : 0 < ε) :
    ∃ cε : ℝ, 0 < cε ∧
      ∀ (k m : ℕ) (μ : Measure (LOOConcentration.Observation k m)) [IsProbabilityMeasure μ]
      (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
      (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
      (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ) (δ₃ c d : ℕ → ℝ)
      (_hσIdentity : (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal = (σ : ℝ))
      (_hM₂Identity : (∫ z, LOOConcentration.observationNormSq z ∂μ) = (M₂ : ℝ))
      (hStanding : ∀ n, LOOConcentration.Revision.StandingAssumption
        (n := n) μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1)))
      (_hRates : ∀ n, ∀ᵐ z ∂μ,
        (δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) ∧
         δ₂ (n + 1) z ≤ (A : ℝ) / (n + 1 : ℝ)) ∧
        (δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ) ∧
         δ₂ (n + 2) z ≤ (A : ℝ) / (n + 2 : ℝ)))
      (_hcBound : ∀ n, c (n + 1) ≤ (B : ℝ))
      (_hdBound : ∀ n, d (n + 1) ≤ (D : ℝ)),
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        let ν := Measure.pi fun _ : Fin (n + 2) => μ
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
            ((hStanding n).stable.integrable_full n)) D -
            LOOConcentration.looEstimate (T n) L D
        ν.real {D | H D > ε} ≤ 3 * Real.exp (-cε * (n + 2 : ℝ)) ∧
        ν.real {D | -H D > ε} ≤ 3 * Real.exp (-cε * (n + 2 : ℝ)) := by
  have hσ : 0 ≤ (σ : ℝ) := σ.coe_nonneg
  have hM₂ : 0 ≤ (M₂ : ℝ) := M₂.coe_nonneg
  have hτ : 0 < ε / 6 := by positivity
  obtain ⟨c₁, hc₁, h₁⟩ := thetaRate_of_uniform_scaled_upper_bounds
    σ M₂ A A (ε / 6) hσ hM₂ A.coe_nonneg A.coe_nonneg hτ
  obtain ⟨c₂, hc₂, h₂⟩ := thetaRate_of_uniform_scaled_upper_bounds
    σ M₂ B D (ε / 6) hσ hM₂ B.coe_nonneg D.coe_nonneg hτ
  let cε := min c₁ c₂ / 2
  have hcε : 0 < cε := by dsimp [cε]; positivity
  refine ⟨cε, hcε, ?_⟩
  intro k m μ hμ T L δ₁ δ₂ δ₃ c d hσIdentity hM₂Identity hStanding hRates hcBound hdBound
  have hδevent : ∀ᶠ n : ℕ in atTop, δ₃ (n + 2) < ε / 6 :=
    (hStanding 0).stable.delta₃_tendsto.eventually (Iio_mem_nhds hτ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hδevent
  refine ⟨n₀, ?_⟩
  intro n hn
  have hsmall := hn₀ n hn
  have hmainε : 3 * δ₃ (n + 2) < ε := by linarith
  have ht₁ : ε / 6 ≤ ε / 3 := by linarith
  have ht₃ : ε / 6 ≤ ε / 3 - δ₃ (n + 2) := by linarith
  let a : NNReal := ⟨(A : ℝ) / Real.sqrt (n + 1 : ℝ), by positivity⟩
  let b : NNReal := ⟨(A : ℝ) / (n + 1 : ℝ), by positivity⟩
  have hbound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ) :=
    (hRates n).mono fun _ hz => hz.1
  have hm := (LOOConcentration.Revision.mainConcentration
    μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1)) (hStanding n) ε hmainε).2 a b hbound
  simp only [hσIdentity, hM₂Identity] at hm
  have hmean₁ : (∫ z, δ₁ (n + 2) z ∂μ) ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
    calc
      _ ≤ ∫ _z : LOOConcentration.Observation k m,
          (A : ℝ) / Real.sqrt (n + 2 : ℝ) ∂μ :=
        integral_mono_ae (hStanding n).delta₁_full_integrable (integrable_const _)
          ((hRates n).mono fun _ hz => hz.2.1)
      _ = _ := by simp
  have hmean₂ : (∫ z, δ₂ (n + 2) z ∂μ) ≤ (A : ℝ) / (n + 2 : ℝ) := by
    calc
      _ ≤ ∫ _z : LOOConcentration.Observation k m,
          (A : ℝ) / (n + 2 : ℝ) ∂μ :=
        integral_mono_ae (hStanding n).delta₂_full_integrable (integrable_const _)
          ((hRates n).mono fun _ hz => hz.2.2)
      _ = _ := by simp
  have hθ₁ := h₁ (n + 1) (by omega) (ε / 3) ht₁ a b a.coe_nonneg b.coe_nonneg
    (by
      change (A : ℝ) / Real.sqrt (n + 1 : ℝ) ≤ (A : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)
      rw [Nat.cast_add, Nat.cast_one])
    (by
      change (A : ℝ) / (n + 1 : ℝ) ≤ (A : ℝ) / ((n + 1 : ℕ) : ℝ)
      rw [Nat.cast_add, Nat.cast_one])
  have hθ₂ := h₂ (n + 2) (by omega) (ε / 3) ht₁
    (c (n + 1) / Real.sqrt (n + 2 : ℝ)) (d (n + 1) / (n + 2 : ℝ))
    (div_nonneg (hStanding n).c_nonneg (Real.sqrt_nonneg _))
    (div_nonneg (hStanding n).d_nonneg (by positivity))
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (div_le_div_of_nonneg_right (hcBound n) (Real.sqrt_nonneg (n + 2 : ℝ))))
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (div_le_div_of_nonneg_right (hdBound n) (show 0 ≤ (n + 2 : ℝ) by positivity)))
  have hθ₃ := h₁ (n + 2) (by omega) (ε / 3 - δ₃ (n + 2)) ht₃
    (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
    (integral_nonneg ((hStanding n).stable.delta₁_nonneg (n + 1)))
    (integral_nonneg ((hStanding n).stable.delta₂_nonneg (n + 1))) (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hmean₁)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hmean₂)
  have hexp (j : ℕ) (cj : ℝ) (_hcj : 0 ≤ cj)
      (hsize : (n + 2 : ℝ) ≤ 2 * (j : ℝ)) (hcjBound : min c₁ c₂ ≤ cj) :
      Real.exp (-cj * (j : ℝ)) ≤ Real.exp (-cε * (n + 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h₀ : cε * (n + 2 : ℝ) ≤ cj * (j : ℝ) := by
      calc
        _ ≤ cε * (2 * (j : ℝ)) := mul_le_mul_of_nonneg_left hsize hcε.le
        _ = min c₁ c₂ * (j : ℝ) := by dsimp [cε]; ring
        _ ≤ cj * (j : ℝ) := mul_le_mul_of_nonneg_right hcjBound (by positivity)
    linarith only [h₀]
  have he₁ := hexp (n + 1) c₁ hc₁.le (by exact_mod_cast (show n + 2 ≤ 2 * (n + 1) by omega)) (min_le_left _ _)
  have he₂ := hexp (n + 2) c₂ hc₂.le (by exact_mod_cast (show n + 2 ≤ 2 * (n + 2) by omega)) (min_le_right _ _)
  have he₃ := hexp (n + 2) c₁ hc₁.le (by exact_mod_cast (show n + 2 ≤ 2 * (n + 2) by omega)) (min_le_left _ _)
  have hsum := add_le_add (add_le_add (hθ₁.trans he₁) (hθ₂.trans he₂)) (hθ₃.trans he₃)
  have heq : Real.exp (-cε * (n + 2 : ℝ)) + Real.exp (-cε * (n + 2 : ℝ)) +
      Real.exp (-cε * (n + 2 : ℝ)) = 3 * Real.exp (-cε * (n + 2 : ℝ)) := by ring
  rw [heq] at hsum
  exact ⟨hm.1.trans hsum, hm.2.trans hsum⟩

end LOOConcentration.Manuscript.Internal
