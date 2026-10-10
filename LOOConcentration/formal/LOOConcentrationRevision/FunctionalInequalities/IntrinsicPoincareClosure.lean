import LOOConcentrationRevision.FunctionalInequalities.IntrinsicPoincare
import LOOConcentrationRevision.FunctionalInequalities.PoincareClosure
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter

/-- The actual intrinsic LSI supplies Poincaré on every literal completed pair. -/
theorem all_pairs_poincare_of_logSobolevConstant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (u : SobolevPair μ) :
    (∫ x, ((WithLp.ofLp u.val).1 x - ∫ y, (WithLp.ofLp u.val).1 y ∂μ)^2 ∂μ) ≤
      C * (sobolevEnergy μ u).toReal := by
  apply completed_pair_poincare_of_generator_bound μ C _ u
  intro p hp
  obtain ⟨F, hF, ⟨B, hB, hbound⟩, hf, hg, rfl⟩ := hp
  change (∫ x, (hf.toLp F x - ∫ y, hf.toLp F y ∂μ)^2 ∂μ) ≤
    C * ‖hg.toLp (gradient F)‖^2
  have hMean : (∫ y, hf.toLp F y ∂μ) = ∫ y, F y ∂μ := integral_congr_ae hf.coeFn_toLp
  have hVar : (∫ x, (hf.toLp F x - ∫ y, hf.toLp F y ∂μ)^2 ∂μ) =
      ∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, hMean]
  have hEnergy : (∫ x, ‖gradient F x‖^2 ∂μ) = ‖hg.toLp (gradient F)‖^2 := by
    calc
      _ = ∫ x, ‖hg.toLp (gradient F) x‖^2 ∂μ :=
        integral_congr_ae (hg.coeFn_toLp.symm.mono fun x hx => by
          simpa only using congrArg (fun y => ‖y‖^2) hx)
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
  rw [hVar, ← hEnergy]
  exact (bounded_smooth_intrinsic_poincare μ C hC hLC F hF B hB hbound).2

/-- Every actual completed pair on a positive finite product keeps the same
base optimal constant in its variance/retained-energy inequality. -/
theorem all_pairs_poincare_euclideanProductLaw
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (u : let ν := euclideanProductLaw (κ := Fin (r+1)) μ
      let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
      SobolevPair ν) :
    let ν := euclideanProductLaw (κ := Fin (r+1)) μ
    let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    (∫ x, ((WithLp.ofLp u.val).1 x - ∫ y, (WithLp.ofLp u.val).1 y ∂ν)^2 ∂ν) ≤
      (logSobolevConstant μ).toReal * (sobolevEnergy ν u).toReal := by
  let ν := euclideanProductLaw (κ := Fin (r+1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal (logSobolevConstant μ).toReal := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    exact logSobolevConstant_euclideanProductLaw_le r μ hfinite
  exact all_pairs_poincare_of_logSobolevConstant_le ν _ ENNReal.toReal_nonneg hLC u

/-- The actual ordered dataset pair has variance bounded by the observation
constant times its own retained gradient energy. -/
theorem all_pairs_poincare_datasetLaw
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (u : let ν := datasetLawOfObservation (r := n+2) μ
      let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
      SobolevPair ν) :
    let ν := datasetLawOfObservation (r := n+2) μ
    let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
    (∫ x, ((WithLp.ofLp u.val).1 x - ∫ y, (WithLp.ofLp u.val).1 y ∂ν)^2 ∂ν) ≤
      (observationLogSobolevConstant μ).toReal * (sobolevEnergy ν u).toReal := by
  let ν := datasetLawOfObservation (r := n+2) μ
  let : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal (observationLogSobolevConstant μ).toReal := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    exact logSobolevConstant_datasetLaw_le μ hfinite
  exact all_pairs_poincare_of_logSobolevConstant_le ν _ ENNReal.toReal_nonneg hLC u

end LOOConcentration.Revision
