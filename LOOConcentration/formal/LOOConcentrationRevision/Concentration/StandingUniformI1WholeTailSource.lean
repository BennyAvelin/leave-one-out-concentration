import LOOConcentrationRevision.Concentration.StandingUniformI1AverageAssembly
import LOOConcentrationRevision.Concentration.Chernoff
import LOOConcentrationRevision.Concentration.CertifiedGaussianChernoff
import LOOConcentrationRevision.Concentration.StandingI1CorollaryRealConsumer
import Mathlib.Probability.Moments.SubGaussian
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

/-- Both strict source-I1 tails from the actual full-average MGF. The zero-LSI
endpoint consumes the independently certified actual-I1 zero-law producer;
the positive-LSI cases use the finite-cutoff Chernoff theorem. -/
theorem standing_revision_uniform_bounds_nonneg
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (a b : ℝ)
    (hbound : ∀ᵐ z ∂μ,
      δ₁ (n + 1) z ≤ a ∧ δ₂ (n + 1) z ≤ b) :
    0 ≤ a ∧ 0 ≤ b := by
  obtain ⟨z, hz⟩ := hbound.exists
  exact ⟨(hSt.stable.delta₁_nonneg n z).trans hz.1,
    (hSt.stable.delta₂_nonneg n z).trans hz.2⟩

theorem standing_I1_actual_uniform_average_theta_tails
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (a b t : ℝ) (ht : 0 < t)
    (hbound : ∀ᵐ z ∂μ,
      δ₁ (n + 1) z ≤ a ∧ δ₂ (n + 1) z ≤ b) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ :=
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ y, observationNormSq y ∂μ
    let hM₂ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
    let hBounds := standing_revision_uniform_bounds_nonneg μ T L δ₁ δ₂ δ₃ c d hSt a b hbound
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg hM₂
      (n + 1) (by omega) t ht a b hBounds.1 hBounds.2
    P.real {D | I₁ D > t} ≤ θ ∧ P.real {D | -I₁ D > t} ≤ θ := by
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ :=
    standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  have hM₂ : 0 ≤ M₂ := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
  have hBounds := standing_revision_uniform_bounds_nonneg μ T L δ₁ δ₂ δ₃ c d hSt a b hbound
  let θ := thetaRate C M₂ ENNReal.toReal_nonneg hM₂
    (n + 1) (by omega) t ht a b hBounds.1 hBounds.2
  change P.real {D | I₁ D > t} ≤ θ ∧ P.real {D | -I₁ D > t} ≤ θ
  have ha0 : 0 ≤ a := hBounds.1
  have hb0 : 0 ≤ b := hBounds.2
  have ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a := hbound.mono fun z hz => hz.1
  have hb : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b := hbound.mono fun z hz => hz.2
  have haverage := standing_I1_actual_uniform_average_mgf
    μ T L δ₁ δ₂ δ₃ c d a b hSt ha0 hb0 ha hb
  have hshort := standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hVInt : Integrable (standingV μ T L δ₁ δ₂ δ₃ c d hSt) P := hparts.2.1
  have hlooInt : Integrable (LOOConcentration.looEstimate (T n) L) P := hparts.2.2.1
  have hmeanZero : (∫ D, I₁ D ∂P) = 0 := by
    change (∫ D, standingV μ T L δ₁ δ₂ δ₃ c d hSt D -
      LOOConcentration.looEstimate (T n) L D ∂P) = 0
    rw [integral_sub hVInt hlooInt]
    change standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
      (∫ D, LOOConcentration.looEstimate (T n) L D ∂P) = 0
    rw [LOOConcentration.integral_looEstimate_eq_independent_test μ (T n) L hshort]
    rw [standingEV_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt]
    ring
  by_cases hCzero : observationLogSobolevConstant μ = 0
  · have hzero := standing_I1_zero_lsi_endpoint μ T L δ₁ δ₂ δ₃ c d hSt hCzero t ht
    constructor
    · simpa [P, I₁, C, M₂, θ, hCzero, thetaRate] using hzero.1.le
    · simpa [P, I₁, C, M₂, θ, hCzero, thetaRate] using hzero.2.le
  · have hCpos : 0 < C := by
      have hCnonneg : 0 ≤ C := ENNReal.toReal_nonneg
      by_contra hnot
      have hC0 : C = 0 := le_antisymm (le_of_not_gt hnot) hCnonneg
      have hLCzero : observationLogSobolevConstant μ = 0 ∨
          observationLogSobolevConstant μ = ⊤ :=
        (ENNReal.toReal_eq_zero_iff _).mp (by simpa [C] using hC0)
      rcases hLCzero with hz | hinf
      · exact (hCzero hz).elim
      · exact hSt.lsi.ne hinf
    by_cases hbzero : b = 0
    · let proxy : NNReal := ⟨4 * C * a ^ 2, by positivity⟩
      have hproxyVal : (proxy : ℝ) = 4 * C * a ^ 2 := rfl
      have hproxyZero : proxy = 0 ↔ a = 0 := by
        constructor
        · intro hp
          have hpc : (proxy : ℝ) = 0 := congrArg (fun x : NNReal => (x : ℝ)) hp
          rw [hproxyVal] at hpc
          have haSq : a ^ 2 = 0 := (mul_eq_zero.mp hpc).resolve_left (by positivity)
          exact sq_eq_zero_iff.mp haSq
        · intro haZ
          apply Subtype.ext
          simp [proxy, haZ]
      have hsub : ProbabilityTheory.HasSubgaussianMGF I₁ proxy P := by
        constructor
        · intro s
          have hs := haverage s (Or.inl hbzero)
          simpa [P, I₁] using hs.1
        · intro s
          have hs := haverage s (Or.inl hbzero)
          have hbound :
              (∫ D, Real.exp (s * I₁ D) ∂P) ≤
                Real.exp (((proxy : ℝ) * s ^ 2) / 2) := by
            calc
              _ ≤ Real.exp ((2 * C * a ^ 2) * s ^ 2) := by
                simpa [P, I₁, C, M₂, hbzero] using hs.2
              _ = Real.exp (((proxy : ℝ) * s ^ 2) / 2) := by
                congr 1
                rw [hproxyVal]
                ring
          simpa [ProbabilityTheory.mgf, I₁, P] using hbound
      have hsharp := strict_tails_le_of_subgaussianMGF_via_certified_chernoff
        P I₁ proxy hsub t ht
      by_cases haZ : a = 0
      · have hrate :
            (if proxy = 0 then (0 : ℝ) else
              Real.exp (-(t ^ 2 / (2 * (proxy : ℝ))))) = θ := by
          simp [hproxyZero, haZ, θ, thetaRate, C, hbzero]
        constructor
        · exact hsharp.1.trans_eq hrate
        · exact hsharp.2.trans_eq hrate
      · have hp : proxy ≠ 0 := fun hp => haZ (hproxyZero.mp hp)
        have hCne : C ≠ 0 := ne_of_gt hCpos
        have htheta : θ = Real.exp (-(t ^ 2 / (8 * C * a ^ 2))) := by
          simp [θ, thetaRate, hCne, hbzero, haZ]
        have hfrac : -(t ^ 2 / (2 * (proxy : ℝ))) =
            -(t ^ 2 / (8 * C * a ^ 2)) := by
          rw [hproxyVal]
          field_simp [ne_of_gt hCpos, pow_ne_zero 2 haZ]
          ring_nf
        have hrate :
            (if proxy = 0 then (0 : ℝ) else
              Real.exp (-(t ^ 2 / (2 * (proxy : ℝ))))) = θ := by
          calc
            _ = Real.exp (-(t ^ 2 / (8 * C * a ^ 2))) := by
              rw [if_neg hp, hfrac]
            _ = θ := htheta.symm
        constructor
        · exact hsharp.1.trans_eq hrate
        · exact hsharp.2.trans_eq hrate
    · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
      have hgaussian : b = 0 → ∀ s : ℝ,
          Integrable (fun D => Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P))) P ∧
          (∫ D, Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P)) ∂P) ≤
            Real.exp ((C * a ^ 2 / 2) * s ^ 2) := by
        intro hbEq
        exact (hbzero hbEq).elim
      have hcutoff : 0 < b → ∀ s : ℝ, |s| ≤ 1 / (4 * C * b) →
          Integrable (fun D => Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P))) P ∧
          (∫ D, Real.exp (s * (I₁ D - ∫ E, I₁ E ∂P)) ∂P) ≤
            Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * ((n + 1 : ℕ) : ℝ) * M₂)) * s ^ 2) := by
        intro _ s hs
        have hm := haverage s (Or.inr (by simpa [C] using hs))
        constructor
        · simpa [P, I₁, hmeanZero] using hm.1
        · simpa [P, I₁, hmeanZero, C, M₂] using hm.2
      have htails := chernoff_revision_thetaRate_of_quadraticMGF
        P I₁ C M₂ hCpos hM₂ (n + 1) (by omega) t ht a b ha0 hb0
        hgaussian hcutoff
      simpa [P, I₁, θ, C, M₂, hmeanZero] using htails

end LOOConcentration.Revision
