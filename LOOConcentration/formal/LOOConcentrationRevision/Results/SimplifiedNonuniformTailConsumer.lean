import LOOConcentrationRevision.Concentration.CertifiedGaussianChernoff
import LOOConcentrationRevision.Concentration.StandingI1MixtureTail
import LOOConcentrationRevision.Concentration.StandingRiskSubGaussian
import LOOConcentrationRevision.Concentration.StandingValidationSubGaussian
import LOOConcentrationRevision.Results.StandingLossDecomposition
import Mathlib.Tactic

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

private theorem nnreal_mk_eq_zero_iff {q : ℝ} (hq : 0 ≤ q) :
    (NNReal.mk q hq : NNReal) = 0 ↔ q = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun x : NNReal => (x : ℝ)) h
    simpa using hv
  · intro h
    apply Subtype.ext
    simpa using h

private theorem strict_gaussian_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (C s t : ℝ) (hC : 0 ≤ C) (ht : 0 < t)
    (hX : ProbabilityTheory.HasSubgaussianMGF X
      (NNReal.mk (C*s^2) (mul_nonneg hC (sq_nonneg s))) ν) :
    ν.real {x | X x > t} ≤
      (if C*s^2 = 0 then 0 else Real.exp (-(t^2/(2*C*s^2)))) := by
  have htails := strict_tails_le_of_subgaussianMGF_via_certified_chernoff
    ν X (NNReal.mk (C*s^2) (mul_nonneg hC (sq_nonneg s))) hX t ht
  have hval : (((NNReal.mk (C*s^2) (mul_nonneg hC (sq_nonneg s)) : NNReal) : ℝ)) = C*s^2 := rfl
  have hzero := nnreal_mk_eq_zero_iff (mul_nonneg hC (sq_nonneg s))
  simpa only [hzero, hval, mul_assoc] using htails.1

/-- Actual simplified first-clause upper-tail consumer with the nonuniform
source mixture rates for the three fluctuation terms. -/
theorem simplified_nonuniform_tail
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzero : ∀ z, δ₂ (n+1) z = 0 ∧ δ₂ (n+2) z = 0)
    (hLip : ∀ z w,
      |meanFittedLoss μ (T n) L z (hSt.mean_integrable z) -
        meanFittedLoss μ (T n) L w (hSt.mean_integrable w)| ≤
          c * observationNorm (z-w))
    (ε : ℝ) (hε : 3*δ₃ (n+2) < ε) :
    let C := (observationLogSobolevConstant μ).toReal
    let ν := Measure.pi fun _ : Fin (n+2) => μ
    let H := fun D =>
      (looRiskL1 μ (T (n+1)) L (hSt.stable.integrable_full n)) D - looEstimate (T n) L D
    let t := (ε-δ₃ (n+2))/3
    let G := fun s : ℝ => if C*s^2 = 0 then 0 else Real.exp (-(t^2/(2*C*s^2)))
    let rhs := (n+2:ℝ) * (∫ z, G (δ₁ (n+1) z) ∂μ) +
      G (c/Real.sqrt (n+2:ℝ)) + G (∫ z, δ₁ (n+2) z ∂μ)
    ν.real {D | H D > ε} ≤ rhs := by
  dsimp only
  let N : ℝ := (n+2:ℝ)
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let ν : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let H : Dataset (Observation k m) (n+2) → ℝ :=
    fun D => (looRiskL1 μ (T (n+1)) L (hSt.stable.integrable_full n)) D - looEstimate (T n) L D
  let I1 := standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
  let I2 := standingI2 μ T L δ₁ δ₂ δ₃ c d hSt
  let I3 := standingI3 μ T L δ₁ δ₂ δ₃ c d hSt
  let B := standingB μ T L δ₁ δ₂ δ₃ c d hSt
  let t : ℝ := (ε-δ₃ (n+2))/3
  let sV : ℝ := c / Real.sqrt N
  let sR : ℝ := ∫ z, δ₁ (n+2) z ∂μ
  let G : ℝ → ℝ := fun s => if C*s^2 = 0 then 0 else Real.exp (-(t^2/(2*C*s^2)))
  let A1 : Set (Dataset (Observation k m) (n+2)) := {D | I1 D > t}
  let A2 : Set (Dataset (Observation k m) (n+2)) := {D | I2 D > t}
  let A3 : Set (Dataset (Observation k m) (n+2)) := {D | I3 D > t}
  let U : Set (Dataset (Observation k m) (n+2)) := (A1 ∪ A2) ∪ A3
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hN : 0 < N := by dsimp [N]; positivity
  have hδ3 : 0 ≤ δ₃ (n+2) := hSt.stable.delta₃_nonneg n
  have ht : 0 < t := by dsimp [t]; linarith
  have hI1pair := standing_I1_mixture_tail μ T L δ₁ δ₂ δ₃ c d hSt
    (fun z => (hzero z).1) t ht
  have hI1tail : ν.real A1 ≤ N * ∫ z, G (δ₁ (n+1) z) ∂μ := by
    simpa [ν, N, C, G, A1, I1, standingI1, standingV] using hI1pair.1
  let V : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
      (hSt.mean_integrable (D i))) / (n+2:ℝ)
  have hVraw := validationAverage_hasSubgaussianMGF_of_revisedStanding
    μ T L δ₁ δ₂ δ₃ c d hSt hLip
  have hVproxyNonneg : 0 ≤ C*c^2/N := by
    exact div_nonneg (mul_nonneg hC (sq_nonneg c)) (le_of_lt hN)
  have hV : ProbabilityTheory.HasSubgaussianMGF
      (fun D => V D - ∫ E, V E ∂ν)
      (NNReal.mk (C*c^2/N) hVproxyNonneg) ν := by
    simpa [V, ν, C, N] using hVraw
  have hVparam :
      (NNReal.mk (C*c^2/N) hVproxyNonneg : NNReal) =
        NNReal.mk (C*sV^2) (mul_nonneg hC (sq_nonneg sV)) := by
    apply Subtype.ext
    have hsqrt : Real.sqrt N * Real.sqrt N = N := by
      nlinarith [Real.sq_sqrt (show 0 ≤ N by linarith)]
    change C*c^2/N = C*(c/Real.sqrt N)^2
    rw [div_pow, Real.sq_sqrt (show 0 ≤ N by linarith)]
    ring
  have hVneg := hV.neg
  rw [hVparam] at hVneg
  have hI2mgf : ProbabilityTheory.HasSubgaussianMGF I2
      (NNReal.mk (C*sV^2) (mul_nonneg hC (sq_nonneg sV))) ν := by
    apply hVneg.congr
    filter_upwards [] with D
    change -(V D - ∫ E, V E ∂ν) = standingEV μ T L δ₁ δ₂ δ₃ c d hSt - V D
    rw [neg_sub]
    congr 1
  have hRiskraw := standing_risk_hasSubgaussianMGF μ T L δ₁ δ₂ δ₃ c d hSt
    (fun z => (hzero z).2)
  have hI3mgf : ProbabilityTheory.HasSubgaussianMGF I3
      (NNReal.mk (C*sR^2) (mul_nonneg hC (sq_nonneg sR))) ν := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun D => standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D -
        standingER μ T L δ₁ δ₂ δ₃ c d hSt)
      (NNReal.mk (C*sR^2) (mul_nonneg hC (sq_nonneg sR))) ν
    simpa [standingRisk, standingER, sR, C, ν] using hRiskraw
  have hI2tail := strict_gaussian_upper_tail ν I2 C sV t hC ht hI2mgf
  have hI3tail := strict_gaussian_upper_tail ν I3 C sR t hC ht hI3mgf
  have hBabs := standingB_abs_le μ T L δ₁ δ₂ δ₃ c d hSt
  have hBupper : B ≤ δ₃ (n+2) := (le_abs_self B).trans hBabs
  have hdecomp (D : Dataset (Observation k m) (n+2)) :
      H D = I1 D + I2 D + I3 D + B := by
    change standingH μ T L δ₁ δ₂ δ₃ c d hSt D =
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt D + standingI2 μ T L δ₁ δ₂ δ₃ c d hSt D +
        standingI3 μ T L δ₁ δ₂ δ₃ c d hSt D + standingB μ T L δ₁ δ₂ δ₃ c d hSt
    exact standingLoss_decomposition μ T L δ₁ δ₂ δ₃ c d hSt D
  have hsubset : {D | H D > ε} ⊆ U := by
    intro D hD
    by_contra hn
    have hbounds : I1 D ≤ t ∧ I2 D ≤ t ∧ I3 D ≤ t := by
      dsimp [U, A1, A2, A3] at hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hn
      rcases hn with ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    have hHD : H D > ε := hD
    rw [hdecomp D] at hHD
    have htidentity : 3*t + δ₃ (n+2) = ε := by dsimp [t]; ring
    nlinarith [htidentity]
  have hUnion : ν.real U ≤ ν.real A1 + ν.real A2 + ν.real A3 := by
    dsimp [U]
    calc
      ν.real ((A1 ∪ A2) ∪ A3) ≤ ν.real (A1 ∪ A2) + ν.real A3 :=
        measureReal_union_le _ _
      _ ≤ ν.real A1 + ν.real A2 + ν.real A3 := by
        exact add_le_add (measureReal_union_le _ _) le_rfl
  change ν.real {D | H D > ε} ≤
    N * ∫ z, G (δ₁ (n+1) z) ∂μ + G sV + G sR
  calc
    ν.real {D | H D > ε} ≤ ν.real U := measureReal_mono hsubset
    _ ≤ ν.real A1 + ν.real A2 + ν.real A3 := hUnion
    _ ≤ N * ∫ z, G (δ₁ (n+1) z) ∂μ + G sV + G sR := by
      exact add_le_add (add_le_add hI1tail hI2tail) hI3tail

end LOOConcentration.Revision
