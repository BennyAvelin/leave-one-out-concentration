import LOOConcentrationRevision.Probability.ObservationZeroLsi
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory LOOConcentration

/-- At native zero LSI, the original observation law is a point mass. The
actual signed mean-validation and delete-one averages therefore coincide almost
everywhere, without any growth, regularity, or component integrability premise.
All signed query means are finite on this same law. -/
theorem modelSelection_actual_signed_I1_zero_lsi {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hzero : Revision.observationLogSobolevConstant μ = 0)
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let f : Observation k m → ℝ := fun z =>
      ∫ D, (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
    (∀ z, Integrable (fun D => fittedLoss (T₀ n) L D z -
        fittedLoss (T₁ n) L D z) Q) ∧
      I₁ =ᵐ[P] (fun _ => 0) ∧
      P.real {D | I₁ D > t} = 0 ∧ P.real {D | -I₁ D > t} = 0 := by
  obtain ⟨a, ha⟩ := Revision.exists_dirac_of_observationLogSobolevConstant_eq_zero μ hzero
  subst μ
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => Measure.dirac a
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => Measure.dirac a
  let f : Observation k m → ℝ := fun z =>
    ∫ D, (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
      (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
  have hQ : Q = Measure.dirac (fun _ : Fin (n + 1) => a) :=
    Revision.measure_pi_dirac a
  have hP : P = Measure.dirac (fun _ : Fin (n + 2) => a) :=
    Revision.measure_pi_dirac a
  have hf (z : Observation k m) : f z =
      fittedLoss (T₀ n) L (fun _ => a) z - fittedLoss (T₁ n) L (fun _ => a) z := by
    dsimp only [f]
    rw [hQ, integral_dirac]
  have hdelete (i : Fin (n + 2)) :
      deleteAt (fun _ : Fin (n + 2) => a) i = (fun _ : Fin (n + 1) => a) := rfl
  have hI : I₁ (fun _ => a) = 0 := by
    simp only [I₁, hf, looEstimate, hdelete, fittedLoss, Finset.sum_sub_distrib, sub_div,
      sub_self]
  have hAE : I₁ =ᵐ[P] (fun _ => 0) := by
    rw [hP, ae_dirac_eq]
    exact hI
  have hPlus : P {D | I₁ D > t} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hAE] with D hD
    rw [hD]
    exact not_lt_of_ge ht.le
  have hMinus : P {D | -I₁ D > t} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hAE] with D hD
    rw [hD, neg_zero]
    exact not_lt_of_ge ht.le
  refine ⟨?_, hAE, ?_, ?_⟩
  · intro z
    change Integrable (fun D => fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) Q
    rw [hQ]
    exact integrable_dirac (by finiteness)
  · change (P {D | I₁ D > t}).toReal = 0
    rw [hPlus, ENNReal.toReal_zero]
  · change (P {D | -I₁ D > t}).toReal = 0
    rw [hMinus, ENNReal.toReal_zero]

end LOOConcentration.Manuscript.Internal
