import StandingI1ActualMomentSource
import LOOConcentrationRevision.Results.StandingI2I3MomentSourceImporting
import LOOConcentration.Revision.Support.MomentExactScaleSupport

/-! QUARANTINED source assembly candidate. Author scope ruling and whole bounded-smooth extension remain open; no certification or source closure inferred. -/
set_option autoImplicit false
namespace LOOConcentration.Revision.Providers
open MeasureTheory
open scoped ENNReal

theorem looMoments {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (_hp : 2 ≤ p)
    (_hδ₁ : MemLp (δ₁ (n + 1)) (ENNReal.ofReal p) μ)
    (_hδ₂ : MemLp (δ₂ (n + 1)) (ENNReal.ofReal p) μ) :
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
    let H := fun D => (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
      looEstimate (T n) L D
    eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B ∧
    eLpNorm H (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (δ₃ (n + 2) + B) ∧
    (p = 2 → (∫ D, (H D - ∫ E, H E ∂ν) ^ 2 ∂ν) ≤ B ^ 2) := by
  dsimp only
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
  let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
  let S := Real.sqrt (C * (p - 1))
  let A₁ := (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
    Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal
  let A₂ := c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull
  let A₃ := (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull
  let B := S * (A₁ + A₂ + A₃)
  let H := standingH μ T L δ₁ δ₂ δ₃ c d h
  let I₁ := standingI1 μ T L δ₁ δ₂ δ₃ c d h
  let I₂ := standingI2 μ T L δ₁ δ₂ δ₃ c d h
  let I₃ := standingI3 μ T L δ₁ δ₂ δ₃ c d h
  let b := standingB μ T L δ₁ δ₂ δ₃ c d h
  let J₂ := fun D => I₂ D - ∫ E, I₂ E ∂ν
  let J₃ := fun D => I₃ D - ∫ E, I₃ E ∂ν
  have hI₁ := standing_I1_actual_moment μ T L δ₁ δ₂ δ₃ c d h p _hp _hδ₁ _hδ₂
  have hI₂ := standingI2_original_centered_moment μ T L δ₁ δ₂ δ₃ c d h _hp
  have hI₃ := standingI3_original_centered_moment μ T L δ₁ δ₂ δ₃ c d h _hp
  have hm₁ : MemLp I₁ (ENNReal.ofReal p) ν := hI₁.1
  have hm₂ : MemLp J₂ (ENNReal.ofReal p) ν := hI₂.1
  have hm₃ : MemLp J₃ (ENNReal.ofReal p) ν := hI₃.1
  have hn₁ : eLpNorm I₁ (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (S * A₁) := hI₁.2.1
  have hn₂ : eLpNorm J₂ (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (S * A₂) := hI₂.2
  have hn₃ : eLpNorm J₃ (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (S * A₃) := hI₃.2
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d h
  have hi₁ : Integrable I₁ ν := hparts.2.1.sub hparts.2.2.1
  have hi₂ : Integrable I₂ ν := (integrable_const _).sub hparts.2.1
  have hi₃ : Integrable I₃ ν := hparts.1.sub (integrable_const _)
  have hsplit : H = fun D => I₁ D + I₂ D + I₃ D + b := by
    funext D
    exact standingLoss_decomposition μ T L δ₁ δ₂ δ₃ c d h D
  have hmean : (∫ D, H D ∂ν) = (∫ D, I₂ D ∂ν) + (∫ D, I₃ D ∂ν) + b := by
    rw [hsplit]
    rw [integral_add (f := fun D => I₁ D + I₂ D + I₃ D) (g := fun _ => b)
      ((hi₁.add hi₂).add hi₃) (integrable_const b)]
    rw [integral_add (f := fun D => I₁ D + I₂ D) (g := I₃) (hi₁.add hi₂) hi₃,
      integral_add (f := I₁) (g := I₂) hi₁ hi₂]
    have hz : (∫ D, I₁ D ∂ν) = 0 := hI₁.2.2
    simp only [hz, integral_const, probReal_univ, one_smul, zero_add]
  have hcenter_eq : (fun D => H D - ∫ E, H E ∂ν) = (I₁ + J₂) + J₃ := by
    funext D
    rw [hmean, hsplit]
    simp only [Pi.add_apply, J₂, J₃]
    ring
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith only [_hp])
  have ht₁ := eLpNorm_add_le hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable hp1
  have ht₂ := eLpNorm_add_le (hm₁.add hm₂).aestronglyMeasurable hm₃.aestronglyMeasurable hp1
  have ha₁ : 0 ≤ S * A₁ := by dsimp only [S, A₁]; positivity
  have ha₂ : 0 ≤ S * A₂ := by
    have hc := h.c_nonneg
    have hd := h.d_nonneg
    dsimp only [S, A₂]
    positivity
  have ha₃ : 0 ≤ S * A₃ := by
    have hd₁ : 0 ≤ ∫ z, δ₁ (n + 2) z ∂μ :=
      integral_nonneg (fun z => h.stable.delta₁_nonneg (n + 1) z)
    have hd₂ : 0 ≤ ∫ z, δ₂ (n + 2) z ∂μ :=
      integral_nonneg (fun z => h.stable.delta₂_nonneg (n + 1) z)
    dsimp only [S, A₃]
    positivity
  have hsum : ENNReal.ofReal (S * A₁) + ENNReal.ofReal (S * A₂) +
      ENNReal.ofReal (S * A₃) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_add ha₁ ha₂, ← ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃]
    congr 1
    dsimp only [B]
    ring
  have hcenter : eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal B := by
    rw [hcenter_eq]
    calc
      _ ≤ eLpNorm (I₁ + J₂) (ENNReal.ofReal p) ν + eLpNorm J₃ (ENNReal.ofReal p) ν := ht₂
      _ ≤ (eLpNorm I₁ (ENNReal.ofReal p) ν + eLpNorm J₂ (ENNReal.ofReal p) ν) +
          eLpNorm J₃ (ENNReal.ofReal p) ν := add_le_add ht₁ (le_refl _)
      _ ≤ ENNReal.ofReal (S * A₁) + ENNReal.ofReal (S * A₂) + ENNReal.ofReal (S * A₃) :=
        add_le_add (add_le_add hn₁ hn₂) hn₃
      _ = ENNReal.ofReal B := hsum
  have hB_exact : B = Real.sqrt (C * (p - 1)) *
      ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
       (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull) := by
    dsimp only [B, S, A₁, A₂, A₃]
    ring
  have hcenter_exact := hcenter
  rw [hB_exact] at hcenter_exact
  have hfinish := Support.standing_actual_exact_scale_finish μ T L δ₁ δ₂ δ₃ c d h p _hp
    hcenter_exact
  exact ⟨hcenter_exact, hfinish⟩

end LOOConcentration.Revision.Providers
