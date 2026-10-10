import LOOConcentration.Frozen.Stability.StandingAssumption
import LOOConcentration.Geometry.EuclideanNormFacts
import LOOConcentration.Stability.Basic

set_option autoImplicit false
namespace LOOConcentration
open MeasureTheory

theorem standing_integrable_full_fittedLoss {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss (T (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) :=
  stable_integrable_fittedLoss h.2.2.1 n

theorem standing_lsi_pos {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) : 0 < C := h.1.1

theorem standing_moment_nonneg {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (_h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    0 ≤ ∫ z, observationNormSq z ∂μ :=
  integral_nonneg (fun z => observationNormSq_nonneg z)

theorem standing_delta_nonneg {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) (r : ℕ)
    (z : Observation (k + 1) (m + 1)) :
    0 ≤ δ₁ (r + 1) z ∧ 0 ≤ δ₂ (r + 1) z := by
  rcases h.2.2.1 with ⟨_, _, hδ, _, _, _, _, _, _⟩
  exact hδ r z

theorem standing_mean_delta_nonneg {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) (r : ℕ) :
    (0 ≤ ∫ z, δ₁ (r + 1) z ∂μ) ∧
    (0 ≤ ∫ z, δ₂ (r + 1) z ∂μ) := by
  constructor
  · exact integral_nonneg (fun z => (standing_delta_nonneg h r z).1)
  · exact integral_nonneg (fun z => (standing_delta_nonneg h r z).2)

theorem standing_c_nonneg {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    0 ≤ c ∧ 0 ≤ d := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hc, hd, _⟩
  exact ⟨hc, hd⟩


theorem standing_uniform_bounds_nonneg {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d a b : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (hbound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a ∧ δ₂ (n + 1) z ≤ b) :
    0 ≤ a ∧ 0 ≤ b := by
  have hboth : ∀ᵐ z ∂μ,
      (0 ≤ δ₁ (n + 1) z ∧ 0 ≤ δ₂ (n + 1) z) ∧
      (δ₁ (n + 1) z ≤ a ∧ δ₂ (n + 1) z ≤ b) :=
    (Filter.Eventually.of_forall (standing_delta_nonneg h n)).and hbound
  obtain ⟨z, hz⟩ := hboth.exists
  exact ⟨le_trans hz.1.1 hz.2.1, le_trans hz.1.2 hz.2.2⟩

theorem standing_mean_integrable {k m n : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C : ℝ} {T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1)}
    {L : Responses (m + 1) → Responses (m + 1) → ℝ}
    {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (z : Observation (k + 1) (m + 1)) :
    Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨hbar, _⟩⟩
  exact hbar z

end LOOConcentration
