import LOOConcentration.Frozen.Stability.Stable
import LOOConcentration.Probability.FittedConditionalRisk
import LOOConcentration.Frozen.Foundations.LooEstimate

/-!
# Consequences of the frozen stability definition

These access lemmas make the source's measurable fitted losses and finite
expectations available to the independent-test conditional-risk theorem.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory

theorem stable_measurable_fittedLoss {k m : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ}
    (h : Stable μ T L δ₁ δ₂ δ₃) (r : ℕ) :
    Measurable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (r + 1) ×
        Observation (k + 1) (m + 1) => fittedLoss (T r) L p.1 p.2) :=
  h.1 r

theorem stable_integrable_fittedLoss {k m : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ}
    (h : Stable μ T L δ₁ δ₂ δ₃) (n : ℕ) :
    Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) =>
        fittedLoss (T (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hbias⟩
  exact (hbias n 0).2.1

theorem stable_integrable_looEstimate {k m : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ}
    (h : Stable μ T L δ₁ δ₂ δ₃) (n : ℕ) :
    Integrable (looEstimate (T n) L)
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hbias⟩
  have hsum : Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        ∑ i : Fin (n + 2), fittedLoss (T n) L (deleteAt D i) (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => (hbias n i).1)
  change Integrable
    (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
      (∑ i : Fin (n + 2), fittedLoss (T n) L (deleteAt D i) (D i)) / (n + 2))
    (Measure.pi fun _ : Fin (n + 2) => μ)
  exact hsum.div_const (n + 2 : ℝ)

theorem stable_condExp_fittedLoss_eq_integral_test {k m : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ)
    (h : Stable μ T L δ₁ δ₂ δ₃) (n : ℕ) :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) =>
        fittedLoss (T (n + 1)) L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => ∫ z, fittedLoss (T (n + 1)) L p.1 z ∂μ := by
  exact condExp_fittedLoss_eq_integral_test μ (T (n + 1)) L
    (stable_integrable_fittedLoss h n)
    (stable_measurable_fittedLoss h (n + 1))

theorem stable_expected_loo_bias {k m : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ)
    (h : Stable μ T L δ₁ δ₂ δ₃) (n : ℕ) :
    |(∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
        looEstimate (T n) L D ∂Measure.pi fun _ : Fin (n + 2) => μ) -
      (∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1),
        fittedLoss (T (n + 1)) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2) := by
  rcases h with ⟨_, _, _, _, hδ₃, _, _, _, hbias⟩
  let R : ℝ := ∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
      Observation (k + 1) (m + 1),
      fittedLoss (T (n + 1)) L p.1 p.2
        ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)
  let a (i : Fin (n + 2)) : ℝ :=
    ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      fittedLoss (T n) L (deleteAt D i) (D i)
        ∂Measure.pi fun _ : Fin (n + 2) => μ
  have hmean :
      (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
        looEstimate (T n) L D ∂Measure.pi fun _ : Fin (n + 2) => μ) =
      (∑ i : Fin (n + 2), a i) / (n + 2) := by
    change (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      (∑ i : Fin (n + 2), fittedLoss (T n) L (deleteAt D i) (D i)) / (n + 2)
        ∂Measure.pi fun _ : Fin (n + 2) => μ) = _
    rw [integral_div]
    rw [integral_finsetSum Finset.univ (fun i _ => (hbias n i).1)]
  change |(∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
    looEstimate (T n) L D ∂Measure.pi fun _ : Fin (n + 2) => μ) - R| ≤ δ₃ (n + 2)
  rw [hmean]
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hsum : |∑ i : Fin (n + 2), (a i - R)| ≤
      ∑ _i : Fin (n + 2), δ₃ (n + 2) := by
    calc
      |∑ i : Fin (n + 2), (a i - R)| ≤
          ∑ i : Fin (n + 2), |a i - R| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + 2), δ₃ (n + 2) :=
        Finset.sum_le_sum (fun i _ => (hbias n i).2.2)
  have hrewrite :
      (∑ i : Fin (n + 2), a i) / (n + 2 : ℝ) - R =
        (∑ i : Fin (n + 2), (a i - R)) / (n + 2 : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).2
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, mul_comm] using hsum

end LOOConcentration
