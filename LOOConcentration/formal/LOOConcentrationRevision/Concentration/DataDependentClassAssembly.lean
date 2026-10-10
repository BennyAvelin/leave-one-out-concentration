import LOOConcentrationRevision.Concentration.DatasetConditionalClassTails
import LOOConcentrationRevision.Probability.ZeroEndpointTails
import LOOConcentrationRevision.Probability.DataDependentMean
import LOOConcentrationRevision.Probability.Unconditioning

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal

/-- Exact frozen data-dependent conclusion assembled from actual raw-law mean,
K-local conditional tails, and once-only unconditioning. Independent review and
all frozen graph prerequisite certification are required before sealing. -/
theorem dataDependentConcentration_class_assembly {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable observationNormSq μ)
    (H : Dataset (Observation k m) (n + 2) → ℝ) (hH : Measurable H)
    (B δ L_K : NNReal)
    (hL2 : eLpNorm H 2 (Measure.pi fun _ : Fin (n + 2) => μ) ≤ (B : ℝ≥0∞))
    (hbias : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ (δ : ℝ))
    (K : Set (Dataset (Observation k m) (n + 2))) (hK : MeasurableSet K)
    (hKpos : 0 < (Measure.pi fun _ : Fin (n + 2) => μ) K)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D - H E| ≤ (L_K : ℝ) * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let p := ν.real Kᶜ
    let C := (observationLogSobolevConstant μ).toReal
    let cBNT := 3 * (2 : ℝ) ^ 12 * Real.exp 2
    let C_K := cBNT * C * Real.log (Real.exp 1 / (1 - p))
    let η_K := (B : ℝ) * Real.sqrt (p / (1 - p))
    ∀ (ε : ℝ) (_hε : (δ : ℝ) + η_K < ε),
      let G := if C_K * (L_K : ℝ) ^ 2 = 0 then 0 else
        Real.exp (-((ε - (δ : ℝ) - η_K) ^ 2 / (2 * C_K * (L_K : ℝ) ^ 2)))
      ν.real {D | H D > ε} ≤ p + G ∧
      ν.real {D | -H D > ε} ≤ p + G ∧
      ν.real {D | |H D| > ε} ≤ p + 2 * G := by
  let P := Measure.pi fun _ : Fin (n+2) => μ
  let p := P.real Kᶜ
  let C := (observationLogSobolevConstant μ).toReal
  let cBNT := 3*(2:ℝ)^12*Real.exp 2
  let C_K := cBNT*C*Real.log (Real.exp 1/(1-p))
  let η_K := (B:ℝ)*Real.sqrt (p/(1-p))
  have hq : 0 < P.real K :=
    ENNReal.toReal_pos (ne_of_gt hKpos) (measure_ne_top P K)
  have hqeq : P.real K = 1-p := by
    have h := probReal_add_probReal_compl (μ := P) hK
    dsimp [p]
    linarith
  dsimp only
  intro ε hε
  let a := (δ:ℝ)+η_K
  let G := if C_K*(L_K:ℝ)^2 = 0 then 0 else
    Real.exp (-((ε-(δ:ℝ)-η_K)^2/(2*C_K*(L_K:ℝ)^2)))
  have ht : 0 < ε-a := by change (δ:ℝ)+η_K < ε at hε; dsimp [a]; linarith
  have hδeps : (δ:ℝ) < ε := by
    have hη : 0 ≤ η_K := mul_nonneg B.property (Real.sqrt_nonneg _)
    change (δ:ℝ)+η_K < ε at hε
    linarith
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    split_ifs <;> positivity
  by_cases hdim : k+m=0
  · obtain ⟨hk, hm⟩ := Nat.add_eq_zero_iff.mp hdim
    subst k
    subst m
    have hz := zeroDimensional_original_tails_eq_zero μ H hH δ hbias ε hδeps
    change P.real {D | H D > ε} = 0 ∧ P.real {D | -H D > ε} = 0 ∧
      P.real {D | |H D| > ε} = 0 at hz
    change P.real {D | H D > ε} ≤ p+G ∧ P.real {D | -H D > ε} ≤ p+G ∧
      P.real {D | |H D| > ε} ≤ p+2*G
    rw [hz.1, hz.2.1, hz.2.2]
    exact ⟨add_nonneg measureReal_nonneg hGnonneg,
      add_nonneg measureReal_nonneg hGnonneg,
      add_nonneg measureReal_nonneg (mul_nonneg (by norm_num) hGnonneg)⟩
  by_cases hzero : observationLogSobolevConstant μ=0
  · have hz := observation_zero_lsi_original_tails_eq_zero μ hzero H hH δ hbias ε hδeps
    change P.real {D | H D > ε} = 0 ∧ P.real {D | -H D > ε} = 0 ∧
      P.real {D | |H D| > ε} = 0 at hz
    change P.real {D | H D > ε} ≤ p+G ∧ P.real {D | -H D > ε} ≤ p+G ∧
      P.real {D | |H D| > ε} ≤ p+2*G
    rw [hz.1, hz.2.1, hz.2.2]
    exact ⟨add_nonneg measureReal_nonneg hGnonneg,
      add_nonneg measureReal_nonneg hGnonneg,
      add_nonneg measureReal_nonneg (mul_nonneg (by norm_num) hGnonneg)⟩
  have hMean := dataDependent_normalized_mean_abs_le μ H hH B δ hL2 hbias K hK hKpos
  have hTail := dataset_local_centered_normalizedRestriction_strict_tails_le_via_class_infimum_and_moment
    μ hfinite hM2 H K hK hq L_K hLip (ε-a) ht
  dsimp only at hTail
  rw [hqeq] at hTail
  change
    ((normalizedRestriction P K).real {D | H D-∫ E, H E ∂normalizedRestriction P K > ε-a} ≤
      if C_K*(L_K:ℝ)^2=0 then 0 else Real.exp (-((ε-a)^2/(2*(C_K*(L_K:ℝ)^2))))) ∧
    ((normalizedRestriction P K).real {D | -(H D-∫ E, H E ∂normalizedRestriction P K) > ε-a} ≤
      if C_K*(L_K:ℝ)^2=0 then 0 else Real.exp (-((ε-a)^2/(2*(C_K*(L_K:ℝ)^2))))) at hTail
  have hG : (if C_K*(L_K:ℝ)^2=0 then 0 else
      Real.exp (-((ε-a)^2/(2*(C_K*(L_K:ℝ)^2))))) = G := by
    dsimp [G]
    split_ifs
    · rfl
    · congr 1
      dsimp [a]
      ring
  rw [hG] at hTail
  exact unconditional_tails_of_conditional_centered_tails
    P K hK hq H a ε G hMean hTail.1 hTail.2

end LOOConcentration.Revision
