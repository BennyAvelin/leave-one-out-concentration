import LOOConcentrationRevision.Frozen.Results.MainConcentration
import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import LOOConcentrationManuscript.Internal.MeanQuadraticMainDependencies

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_quadratic_scalar_main_application
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) :
    let e := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map e) :=
      μ.isProbabilityMeasure_map
        (((PiLp.continuous_toLp (p := (2 : ENNReal))
          (β := fun _ : Fin 1 => ℝ)).comp
          (continuous_pi fun _ : Fin 1 => continuous_id)).measurable.aemeasurable)
    ∀ (_hFinite : Revision.logSobolevConstant (μ.map e) < ⊤) (n : ℕ),
    let C := (Revision.logSobolevConstant (μ.map e)).toReal
    let M₂ := ∫ x : ℝ, x ^ 2 ∂μ
    let m := ∫ x : ℝ, x ∂μ
    let v := variance (id : ℝ → ℝ) μ
    let bias := v / ((n + 2 : ℝ) * (n + 1 : ℝ))
    let H := fun D : Fin (n + 2) → ℝ =>
      (∫ z : ℝ, (empiricalMean (n + 1) (WithLp.toLp 2 D) - z) ^ 2 ∂μ) -
      (n + 2 : ℝ)⁻¹ * ∑ i : Fin (n + 2),
        (empiricalMean n (WithLp.toLp 2 (fun j : Fin (n + 1) => D (i.succAbove j))) - D i) ^ 2
    ∀ (ε : ℝ), 3 * bias < ε →
    let Θ := fun (r : ℕ) (t a b : ℝ) =>
      if C = 0 then 0 else
      if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
        if b = 0 then 0 else Real.exp (-(t / (8 * C * b)))
      else if b = 0 then
        Real.exp (-(t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
      else Real.exp (-(min
        (t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
        (t / (8 * C * b))))
    let rhs := (n + 2 : ℝ) *
        (∫ z : ℝ, Θ (n + 1) (ε / 3)
          (2 * |z| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ)) ∂μ) +
      Θ (n + 2) (ε / 3)
        (2 * |m| / Real.sqrt (n + 2 : ℝ)) (2 / (n + 2 : ℝ)) +
      Θ (n + 2) (ε / 3 - bias)
        (2 * (∫ z : ℝ, |z| ∂μ) / Real.sqrt (n + 2 : ℝ)) (2 / (n + 2 : ℝ))
    (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤ rhs ∧
    (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤ rhs

:= by
  classical
  intro e hFinite n C M₂ m v bias H ε hε Θ rhs
  let φ : ℝ → LOOConcentration.Observation 1 1 := fun x =>
    (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
  let ν := μ.map φ
  let hνprob : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
    ContinuousMap.const (LOOConcentration.Features 1)
      (fun _ : Fin 1 => empiricalMean r (WithLp.toLp 2 (fun i => (D i).2 0)))
  let L := fun y y' : LOOConcentration.Responses 1 => (y 0 - y' 0) ^ 2
  let δ₁ := fun N : ℕ => fun z : LOOConcentration.Observation 1 1 =>
    2 * |z.2 0| / Real.sqrt (N : ℝ)
  let δ₂ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 =>
    (2 : ℝ) / (N : ℝ)
  let δ₃ := fun N : ℕ => variance (id : ℝ → ℝ) μ /
    ((N : ℝ) * ((N : ℝ) - 1))
  let c := 2 * |∫ x : ℝ, x ∂μ|
  let d := (2 : ℝ)
  have hFiniteScalar :
      let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤ := by
    simpa [e] using hFinite
  have hStanding :=
    LOOConcentration.Manuscript.Internal.empiricalMean_quadraticStanding_of_scalarLaw
      μ hSecond hFiniteScalar n
  have hN : (n : ℝ) + 2 - 1 = (n : ℝ) + 1 := by ring
  have hεMain : 3 * δ₃ (n + 2) < ε := by
    dsimp [δ₃]
    push_cast
    rw [hN]
    simpa [v, bias] using hε
  have hMain := @LOOConcentration.Revision.mainConcentration 1 1 n
    ν hνprob T L δ₁ δ₂ δ₃ c d hStanding ε hεMain
  have hTransport :=
    LOOConcentration.Manuscript.Internal.empiricalMean_quadratic_scalar_observation_H_tail_transport
      μ hSecond n
  obtain ⟨_hFull, hTransport⟩ := hTransport
  have hCompare :=
    LOOConcentration.Manuscript.Internal.empiricalMean_quadratic_main_rhs_le_scalar_source
      μ hSecond hFiniteScalar n ε (by simpa [v, bias] using hε)
  have hTails := hTransport.2 ε
  refine ⟨?_, ?_⟩
  · calc
      (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} =
          (Measure.pi fun _ : Fin (n + 2) => ν).real
            {D | (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
              (_hFull)) D - LOOConcentration.looEstimate (T n) L D > ε} := by
              exact (hTails.1).symm
      _ ≤ _ := hMain.1.1
      _ ≤ rhs := by
        convert hCompare using 1 <;>
          simp [Θ, LOOConcentration.Revision.thetaRate, δ₁, δ₂, δ₃, c, d,
            ν, φ, C, M₂, m, v, bias, e, hN, rhs]
  · calc
      (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} =
          (Measure.pi fun _ : Fin (n + 2) => ν).real
            {D | -((LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
              (_hFull)) D - LOOConcentration.looEstimate (T n) L D) > ε} := by
              exact (hTails.2).symm
      _ ≤ _ := hMain.1.2
      _ ≤ rhs := by
        convert hCompare using 1 <;>
          simp [Θ, LOOConcentration.Revision.thetaRate, δ₁, δ₂, δ₃, c, d,
            ν, φ, C, M₂, m, v, bias, e, hN, rhs]

end LOOConcentration.Manuscript
