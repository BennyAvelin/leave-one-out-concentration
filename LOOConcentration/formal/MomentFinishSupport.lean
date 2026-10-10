import LOOConcentrationRevision.Results.StandingLossDecomposition

set_option autoImplicit false
namespace LOOConcentration.Revision.Support

open MeasureTheory
open scoped MeasureTheory ENNReal

/-- A finite conditional centered norm gives both membership and the shifted norm bound. -/
theorem centered_eLpNorm_finish
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (H : α → ℝ) (hHint : Integrable H ν)
    (p : ℝ≥0∞) (hp : (2 : ℝ≥0∞) ≤ p)
    (B : ℝ) (hB : 0 ≤ B)
    (hcenter : eLpNorm (fun x => H x - ∫ y, H y ∂ν) p ν ≤ ENNReal.ofReal B) :
    MemLp (fun x => H x - ∫ y, H y ∂ν) p ν ∧
      eLpNorm H p ν ≤ ENNReal.ofReal (|∫ y, H y ∂ν| + B) := by
  let m : ℝ := ∫ y, H y ∂ν
  let Hc : α → ℝ := fun x => H x - m
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_trans (by norm_num) hp
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hνne : ν ≠ 0 := by
    intro hz
    have hu : ν Set.univ = 1 := measure_univ
    rw [hz] at hu
    norm_num at hu
  have hHc_meas : AEStronglyMeasurable Hc ν := by
    exact hHint.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hHc_mem : MemLp Hc p ν := by
    refine ⟨hHc_meas, ?_⟩
    have hbound : eLpNorm Hc p ν ≤ ENNReal.ofReal B := by
      simpa [Hc, m] using hcenter
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hHc_mem' : MemLp (fun x => H x - ∫ y, H y ∂ν) p ν := by
    simpa [Hc, m] using hHc_mem
  have hconst : eLpNorm (fun _ : α => m) p ν = ENNReal.ofReal |m| := by
    calc
      eLpNorm (fun _ : α => m) p ν =
          ‖m‖ₑ * ν Set.univ ^ (1 / p.toReal) := eLpNorm_const (c := m) hp0 hνne
      _ = ‖m‖ₑ := by simp [measure_univ]
      _ = ENNReal.ofReal |m| := Real.enorm_eq_ofReal_abs m
  have hsplit : H = Hc + fun _ : α => m := by
    funext x
    simp [Hc, m]
  have htri := eLpNorm_add_le (f := Hc) (g := fun _ : α => m)
    hHc_meas aestronglyMeasurable_const hp1
  refine ⟨hHc_mem', ?_⟩
  calc
    eLpNorm H p ν = eLpNorm (Hc + fun _ : α => m) p ν := by rw [hsplit]
    _ ≤
        eLpNorm Hc p ν + eLpNorm (fun _ : α => m) p ν := htri
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal |m| := add_le_add hcenter (le_of_eq hconst)
    _ = ENNReal.ofReal (B + |m|) := by
      rw [← ENNReal.ofReal_add hB (abs_nonneg m)]
    _ = ENNReal.ofReal (|∫ y, H y ∂ν| + B) := by
      congr 1
      ring

/-- The raw centered square integral is bounded by the square of a centered `L²` bound. -/
theorem centered_square_integral_finish
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (H : α → ℝ) (hHint : Integrable H ν)
    (B : ℝ) (hB : 0 ≤ B)
    (hcenter : eLpNorm (fun x => H x - ∫ y, H y ∂ν) 2 ν ≤ ENNReal.ofReal B) :
    (∫ x, (H x - ∫ y, H y ∂ν) ^ 2 ∂ν) ≤ B ^ 2 := by
  let g : α → ℝ := fun x => H x - ∫ y, H y ∂ν
  have hmem := (centered_eLpNorm_finish ν H hHint 2 (by norm_num) B hB hcenter).1
  have hsq_nonneg : 0 ≤ ∫ x, g x ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (g x))
  have hformula := hmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hpow : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) = ∫ x, g x ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hformula2 : eLpNorm g 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, g x ^ 2 ∂ν)) := by
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at hformula
    rw [hpow] at hformula
    rw [hformula, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hroot : Real.sqrt (∫ x, g x ^ 2 ∂ν) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hB).mp
    rw [← hformula2]
    exact hcenter
  have hout : (∫ x, g x ^ 2 ∂ν) ≤ B ^ 2 := by
    have hroot_nonneg : 0 ≤ Real.sqrt (∫ x, g x ^ 2 ∂ν) := Real.sqrt_nonneg _
    have hsquare : Real.sqrt (∫ x, g x ^ 2 ∂ν) ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hroot_nonneg hB).2 hroot
    nlinarith [Real.sq_sqrt hsq_nonneg, hsquare]
  simpa [g] using hout

/-- Conditional consumer for the exact frozen standing risk error. The centered
bound remains an explicit parent obligation; this helper does not close a
source theorem. -/
theorem standing_actual_centered_moment_finish
    {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
        looEstimate (T n) L D
    ∀ (p : ℝ≥0∞), (2 : ℝ≥0∞) ≤ p → ∀ B : ℝ, 0 ≤ B →
      eLpNorm (fun D => H D - ∫ E, H E ∂ν) p ν ≤ ENNReal.ofReal B →
      eLpNorm H p ν ≤ ENNReal.ofReal (δ₃ (n + 2) + B) := by
  dsimp only
  intro p hp B hB hcenter
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
      looEstimate (T n) L D
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hRisk : Integrable (standingRisk μ T L δ₁ δ₂ δ₃ c d hSt) ν := hparts.1
  have hLoo : Integrable (looEstimate (T n) L) ν := hparts.2.2.1
  have hHint : Integrable H ν := by
    change Integrable (standingH μ T L δ₁ δ₂ δ₃ c d hSt) _
    exact hparts.2.2.2
  have hshort := standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  have hloo_joint := integral_looEstimate_eq_independent_test μ (T n) L hshort
  have hev_joint := standingEV_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt
  have hmean_eq : (∫ D, H D ∂ν) = standingB μ T L δ₁ δ₂ δ₃ c d hSt := by
    calc
      (∫ D, H D ∂ν) =
          (∫ D, standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D ∂ν) -
            (∫ D, looEstimate (T n) L D ∂ν) := by
              change (∫ D,
                standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D - looEstimate (T n) L D ∂ν) = _
              rw [integral_sub hRisk hLoo]
      _ = standingER μ T L δ₁ δ₂ δ₃ c d hSt -
          (∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
            fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) := by
              rw [← hloo_joint]
              rfl
      _ = standingER μ T L δ₁ δ₂ δ₃ c d hSt - standingEV μ T L δ₁ δ₂ δ₃ c d hSt := by
              rw [← hev_joint]
      _ = standingB μ T L δ₁ δ₂ δ₃ c d hSt := rfl
  have hmean : |∫ D, H D ∂ν| ≤ δ₃ (n + 2) := by
    rw [hmean_eq]
    exact standingB_abs_le μ T L δ₁ δ₂ δ₃ c d hSt
  have hδ : 0 ≤ δ₃ (n + 2) := hSt.stable.delta₃_nonneg n
  have hfinish := centered_eLpNorm_finish ν H hHint p hp B hB (by simpa [H] using hcenter)
  have htarget : 0 ≤ δ₃ (n + 2) + B := add_nonneg hδ hB
  have hreal : |∫ D, H D ∂ν| + B ≤ δ₃ (n + 2) + B := by
    nlinarith [hmean]
  exact hfinish.2.trans ((ENNReal.ofReal_le_ofReal_iff htarget).2 hreal)

/-- Conditional exact `p = 2` consumer for the same literal frozen error. -/
theorem standing_actual_centered_square_finish
    {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
        looEstimate (T n) L D
    ∀ B : ℝ, 0 ≤ B →
      eLpNorm (fun D => H D - ∫ E, H E ∂ν) 2 ν ≤ ENNReal.ofReal B →
      (∫ D, (H D - ∫ E, H E ∂ν) ^ 2 ∂ν) ≤ B ^ 2 := by
  dsimp only
  intro B hB hcenter
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)) D -
      looEstimate (T n) L D
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hHint : Integrable H ν := by
    change Integrable (standingH μ T L δ₁ δ₂ δ₃ c d hSt) _
    exact hparts.2.2.2
  exact centered_square_integral_finish ν H hHint B hB (by simpa [H] using hcenter)

end LOOConcentration.Revision.Support

#print axioms LOOConcentration.Revision.Support.centered_eLpNorm_finish
#print axioms LOOConcentration.Revision.Support.centered_square_integral_finish
#print axioms LOOConcentration.Revision.Support.standing_actual_centered_moment_finish
#print axioms LOOConcentration.Revision.Support.standing_actual_centered_square_finish
