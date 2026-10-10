import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

/-- The centered indicator of a measurable event has variance `p * (1-p)`. -/
theorem centered_indicator_variance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Set α) (hK : MeasurableSet K) :
    ∫ x, (K.indicator (fun _ : α => (1 : ℝ)) x - μ.real K) ^ 2 ∂μ =
      μ.real Kᶜ * (1 - μ.real Kᶜ) := by
  let q : ℝ := μ.real K
  have hprob : μ.real K + μ.real Kᶜ = 1 := probReal_add_probReal_compl hK
  have hsplit : ∀ x,
      (K.indicator (fun _ : α => (1 : ℝ)) x - q) ^ 2 =
        K.indicator (fun _ => (1 - q) ^ 2) x + Kᶜ.indicator (fun _ => q ^ 2) x := by
    intro x
    by_cases hx : x ∈ K
    · simp [hx, q]
    · simp [hx, q]
  have hKint : Integrable (K.indicator (fun _ : α => (1 - q) ^ 2)) μ :=
    (integrable_const _).indicator hK
  have hKcint : Integrable (Kᶜ.indicator (fun _ : α => q ^ 2)) μ :=
    (integrable_const _).indicator hK.compl
  have hformula :
      ∫ x, (K.indicator (fun _ : α => (1 : ℝ)) x - q) ^ 2 ∂μ =
        μ.real K * (1 - q) ^ 2 + μ.real Kᶜ * q ^ 2 := by
    calc
      _ = ∫ x, (K.indicator (fun _ : α => (1 - q) ^ 2) x +
          Kᶜ.indicator (fun _ : α => q ^ 2) x) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ hsplit
      _ = (∫ x, K.indicator (fun _ : α => (1 - q) ^ 2) x ∂μ) +
          ∫ x, Kᶜ.indicator (fun _ : α => q ^ 2) x ∂μ := integral_add hKint hKcint
      _ = μ.real K * (1 - q) ^ 2 + μ.real Kᶜ * q ^ 2 := by
        rw [integral_indicator_const (e := (1 - q) ^ 2) hK,
          integral_indicator_const (e := q ^ 2) hK.compl, smul_eq_mul, smul_eq_mul]
  have hq : q = 1 - μ.real Kᶜ := by
    dsimp [q]
    linarith [hprob]
  rw [show μ.real K = q by rfl, hformula]
  rw [show μ.real K = q by rfl]
  rw [hq]
  ring

end LOOConcentration.Revision
