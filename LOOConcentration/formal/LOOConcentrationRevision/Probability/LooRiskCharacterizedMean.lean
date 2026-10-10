import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
/-- The mean of the approved risk object obtained from its conditional characterization. -/
theorem looRiskL1_mean_eq_joint_of_characterization {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 2)) (L : Responses m → Responses m → ℝ)
    (hf : Integrable (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss T L p.1 p.2) ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    (∫ D, (looRiskL1 μ T L hf) D ∂Measure.pi fun _ : Fin (n + 2) => μ) =
      ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss T L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  have hchar := looRiskL1_characterization μ T L hf
  have he := integral_congr_ae hchar
  have hm : MeasurableSpace.comap
      (Prod.fst : Dataset (Observation k m) (n + 2) × Observation k m →
        Dataset (Observation k m) (n + 2)) inferInstance ≤
      (inferInstance : MeasurableSpace (Dataset (Observation k m) (n + 2) × Observation k m)) :=
    measurable_fst.comap_le
  calc
    (∫ D, (looRiskL1 μ T L hf) D ∂ν) =
        ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (looRiskL1 μ T L hf) p.1 ∂(ν.prod μ) := by
      simp only [integral_fun_fst, probReal_univ, one_smul]
    _ = ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (ν.prod μ)[(fun q : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss T L q.1 q.2) | MeasurableSpace.comap Prod.fst inferInstance] p
          ∂(ν.prod μ) := he.symm
    _ = ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          fittedLoss T L p.1 p.2 ∂(ν.prod μ) := integral_condExp hm
end LOOConcentration.Revision
