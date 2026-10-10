import LOOConcentrationManuscript.Internal.GaussianKernelApprovedStanding
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedKernelEstimator
import LOOConcentrationRevision.Frozen.Results.MainConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

theorem gaussianKernel_approved_estimator_uniform_main_tails
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    let K : {K : ℝ → ℝ // Continuous K ∧ ∀ x, 0 ≤ K x} :=
      ⟨gaussianPDFReal 0 1, gaussianKernel_normalization_and_bounds.1.continuous,
        gaussianPDFReal_nonneg 0 1⟩
    let T := stabilizedKernelEstimator K ⟨h, hh⟩ ⟨δ, hδ⟩
    let L := fun u v : LOOConcentration.Responses 1 => |u 0 - v 0|
    let σ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, LOOConcentration.observationNormSq z ∂μ
    let Θ := fun (r : ℕ) (t a b : ℝ) =>
      if σ = 0 then 0 else
      if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
        if b = 0 then 0 else Real.exp (-(t / (8 * σ * b)))
      else if b = 0 then
        Real.exp (-(t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
      else Real.exp (-(min
        (t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
        (t / (8 * σ * b))))
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N _ => C / Real.sqrt (N : ℝ)) (fun N _ => C / (N : ℝ))
        (fun N => B / (N : ℝ)) M 0,
      ∀ ε : ℝ, 3 * (B / (n + 2 : ℝ)) < ε →
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
            (hStanding.stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
        let rhs := Θ (n + 1) (ε / 3)
            (C / Real.sqrt (n + 1 : ℝ)) (C / (n + 1 : ℝ)) +
          Θ (n + 2) (ε / 3) (M / Real.sqrt (n + 2 : ℝ)) 0 +
          Θ (n + 2) (ε / 3 - B / (n + 2 : ℝ))
            (C / Real.sqrt (n + 2 : ℝ)) (C / (n + 2 : ℝ))
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤ rhs ∧
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤ rhs := by
  intro K T L σ M₂ Θ
  obtain ⟨C,hC,B,hB,M,hM,hAll⟩ :=
    gaussianKernel_approved_estimator_complete_standing μ hSecond hLSI h δ hh hδ
  refine ⟨C,hC,B,hB,M,hM,?_⟩
  intro n
  refine ⟨hAll n,?_⟩
  intro ε hε
  have hε' : 3 * (B / ((n + 2 : ℕ) : ℝ)) < ε := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hε
  have hMain := (LOOConcentration.Revision.mainConcentration μ T L
    (fun N _ => C / Real.sqrt (N : ℝ)) (fun N _ => C / (N : ℝ))
    (fun N => B / (N : ℝ)) M 0 (hAll n) ε hε').2
  let a : NNReal := ⟨C / Real.sqrt (n + 1 : ℝ), by positivity⟩
  let b : NNReal := ⟨C / (n + 1 : ℝ), by positivity⟩
  have hBound : ∀ᵐ z ∂μ, C / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (a : ℝ) ∧
      C / ((n + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact Eventually.of_forall fun _ => by
      change C / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ C / Real.sqrt (n + 1 : ℝ) ∧
        C / ((n + 1 : ℕ) : ℝ) ≤ C / (n + 1 : ℝ)
      simp only [Nat.cast_add,Nat.cast_one,le_refl,and_self]
  have hTails := hMain a b hBound
  have ha : (a : ℝ) = C / Real.sqrt (n + 1 : ℝ) := rfl
  have hb : (b : ℝ) = C / (n + 1 : ℝ) := rfl
  dsimp only [σ,M₂,Θ]
  simpa only [ha,hb,LOOConcentration.Revision.thetaRate,
    integral_const,probReal_univ,one_smul,zero_div,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat] using hTails

end LOOConcentration.Manuscript.Internal
