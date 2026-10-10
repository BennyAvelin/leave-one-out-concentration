import MomentFinishSupport
import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.Tactic

set_option autoImplicit false
namespace LOOConcentration.Revision.Support

open MeasureTheory
open scoped ENNReal

/-- Nonnegativity of the exact six-term scale in the frozen LOO-moment root. -/
theorem standing_MomentScale_nonneg
    {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (hp : 2 ≤ p) :
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
    let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
    let B := Real.sqrt (C * (p - 1)) *
      ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
       (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull)
    0 ≤ B := by
  dsimp only
  have hC : 0 ≤ (observationLogSobolevConstant μ).toReal := ENNReal.toReal_nonneg
  have hM₂ : 0 ≤ ∫ z, observationNormSq z ∂μ :=
    integral_nonneg (fun z => observationNormSq_nonneg z)
  have hδ₁ : 0 ≤ ∫ z, δ₁ (n + 2) z ∂μ :=
    integral_nonneg (fun z => hSt.stable.delta₁_nonneg (n + 1) z)
  have hδ₂ : 0 ≤ ∫ z, δ₂ (n + 2) z ∂μ :=
    integral_nonneg (fun z => hSt.stable.delta₂_nonneg (n + 1) z)
  have hLp₁ : 0 ≤ (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal :=
    ENNReal.toReal_nonneg
  have hLp₂ : 0 ≤ (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal :=
    ENNReal.toReal_nonneg
  have hc : 0 ≤ c := hSt.c_nonneg
  have hd : 0 ≤ d := hSt.d_nonneg
  have hp₁ : 0 ≤ p - 1 := by linarith
  have hp₂ : 0 ≤ p - 2 := by linarith
  positivity

/-- Conditional assembly of the exact uncentered and square clauses of the
frozen moment statement. The exact centered first clause remains a parent
condition and is not proved here. -/
theorem standing_actual_exact_scale_finish
    {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (hp : 2 ≤ p) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
    let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
    let B := Real.sqrt (C * (p - 1)) *
      ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
       (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull)
    let H := fun D => (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
      looEstimate (T n) L D
    eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B →
    eLpNorm H (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (δ₃ (n + 2) + B) ∧
    (p = 2 → (∫ D, (H D - ∫ E, H E ∂ν) ^ 2 ∂ν) ≤ B ^ 2) := by
  dsimp only
  intro hcenter
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
      looEstimate (T n) L D
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
  let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
  let B := Real.sqrt (C * (p - 1)) *
    ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
     Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
     c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
     (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull)
  have hB : 0 ≤ B := standing_MomentScale_nonneg μ T L δ₁ δ₂ δ₃ c d hSt p hp
  have hp0 : 0 ≤ p := by linarith
  have hpENN : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    calc
      (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal p :=
        (ENNReal.ofReal_le_ofReal_iff hp0).2 hp
  have hcenter' :
      eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B := by
    simpa [B, Qdeleted, Qfull, C, M₂, H, ν] using hcenter
  have hshift := standing_actual_centered_moment_finish
    μ T L δ₁ δ₂ δ₃ c d hSt (ENNReal.ofReal p) hpENN B hB hcenter'
  constructor
  · simpa [B, Qdeleted, Qfull, C, M₂, H, ν] using hshift
  · intro hp2
    subst p
    have hcenter2 :
        eLpNorm (fun D => H D - ∫ E, H E ∂ν) 2 ν ≤ ENNReal.ofReal B := by
      simpa [B, Qdeleted, Qfull, C, M₂, H, ν] using hcenter
    exact standing_actual_centered_square_finish μ T L δ₁ δ₂ δ₃ c d hSt B hB
      hcenter2

end LOOConcentration.Revision.Support

#print axioms LOOConcentration.Revision.Support.standing_MomentScale_nonneg
#print axioms LOOConcentration.Revision.Support.standing_actual_exact_scale_finish
