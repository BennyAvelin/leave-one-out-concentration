import LOOConcentrationManuscript.Internal.KernelDensityExactSupremumStanding
import LOOConcentrationManuscript.Internal.StandingMeanLossLipschitz
import LOOConcentrationRevision.Frozen.Results.SimplifiedConcentration
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Topology ENNReal

theorem kde_actual_exact_supremum_simplified_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    let M := sSup (Set.range (fun t : ℝ => |deriv K.val t|))
    0 ≤ M ∧ ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) ν T L
        (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
        (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) 0,
      ∀ ε : ℝ, 0 < ε →
        let H := fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
          (hStanding.stable.integrable_full n)) D - LOOConcentration.looEstimate (T n) L D
        let σ := (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal
        let s := M / (h.val ^ 2 * Real.sqrt (n + 1 : ℝ)) +
          2 * (M / (h.val ^ 2 * Real.sqrt (n + 2 : ℝ)))
        let G := if σ * s ^ 2 = 0 then 0 else Real.exp (-(ε ^ 2 / (2 * σ * s ^ 2)))
        (Measure.pi fun _ : Fin (n + 2) => ν).real {D | |H D| > ε} ≤ 2 * G ∧
        (Measure.pi fun _ : Fin (n + 2) => ν).real {D | H D > ε} ≤ G ∧
        (Measure.pi fun _ : Fin (n + 2) => ν).real {D | -H D > ε} ≤ G := by
  intro φ ν T L M
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨hM,hAll⟩ := kde_actual_exact_supremum_standing μ hSecond hLSI K h
  refine ⟨hM,?_⟩
  intro n
  refine ⟨hAll n,?_⟩
  intro ε hε
  have hLip := standing_zero_d_mean_loss_lipschitz ν T L
    (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
    (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) (hAll n)
  have hSimple := (LOOConcentration.Revision.simplifiedConcentration.1
    1 1 n ν T L (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
    (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) 0 (hAll n)
    (fun _ => ⟨rfl,rfl⟩) hLip).2
  let a : NNReal := ⟨M / (h.val ^ 2 * Real.sqrt (n + 1 : ℝ)), by positivity⟩
  have ha : (a : ℝ) = M / (h.val ^ 2 * Real.sqrt (n + 1 : ℝ)) := rfl
  have hBound : ∀ᵐ z ∂ν,
      M / (h.val ^ 2 * Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤ (a : ℝ) :=
    Eventually.of_forall fun _ => by simp only [ha,Nat.cast_add,Nat.cast_one,le_refl]
  have hTail := hSimple a hBound ε hε
  dsimp only
  convert hTail using 1 <;>
    simp only [ha, integral_const, probReal_univ, one_smul, Nat.cast_add,
      Nat.cast_ofNat, zero_add] <;>
      ring

end LOOConcentration.Manuscript.Internal
