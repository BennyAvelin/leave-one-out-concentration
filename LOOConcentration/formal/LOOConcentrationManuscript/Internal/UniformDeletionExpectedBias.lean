import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.DeleteAt
import LOOConcentration.Probability.DeletedTransport
import LOOConcentration.Probability.SampleTestLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory

/-- A same-test-point uniform deletion envelope gives the source expected-bias
bound. The true-L¹ integrability of the deleted fit is derived from the full
fit and the envelope, then transported through the actual deletion laws. -/
theorem uniform_deletion_expected_bias
    {k m : ℕ}
    (μ : Measure (LOOConcentration.Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ,
      LOOConcentration.Estimator (k + 1) (m + 1) (r + 1))
    (L : LOOConcentration.Responses (m + 1) →
      LOOConcentration.Responses (m + 1) → ℝ)
    (β : ℕ → ℝ)
    (hJointMeas : ∀ r,
      Measurable
        (fun p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (r + 1) ×
            LOOConcentration.Observation (k + 1) (m + 1) =>
          LOOConcentration.fittedLoss (T r) L p.1 p.2))
    (hFullL1 : ∀ n,
      Integrable
        (fun p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1) =>
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2)
        ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hUniform : ∀ n (i : Fin (n + 2))
      (D : LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2))
      (z : LOOConcentration.Observation (k + 1) (m + 1)),
        |LOOConcentration.fittedLoss (T (n + 1)) L D z -
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) z| ≤ β (n + 2)) :
    ∀ n (i : Fin (n + 2)),
      Integrable
        (fun D : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) =>
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
      |(∫ D : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2),
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1),
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
            ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ β (n + 2) := by
  intro n i
  let P : Measure
      (LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Pshort : Measure
      (LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let Q : Measure
      (LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
          LOOConcentration.Observation (k + 1) (m + 1)) := P.prod μ
  let Qshort : Measure
      (LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1) ×
          LOOConcentration.Observation (k + 1) (m + 1)) := Pshort.prod μ
  let Φ :
      (LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
        LOOConcentration.Observation (k + 1) (m + 1)) →
      (LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1) ×
        LOOConcentration.Observation (k + 1) (m + 1)) :=
    fun p => (LOOConcentration.deleteAt p.1 i, p.2)
  let shortFresh := fun p :
      LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1) ×
        LOOConcentration.Observation (k + 1) (m + 1) =>
    LOOConcentration.fittedLoss (T n) L p.1 p.2
  let shortOnFull := fun p :
      LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
        LOOConcentration.Observation (k + 1) (m + 1) =>
    shortFresh (Φ p)
  let fullFresh := fun p :
      LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
        LOOConcentration.Observation (k + 1) (m + 1) =>
    LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
  have hFull : Integrable fullFresh Q := hFullL1 n
  have hHeldMap :=
    LOOConcentration.deleted_sample_and_heldout_measurePreserving
      (μ := μ) (n := n) i
  have hDeleteSample : MeasurePreserving
      (fun D : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) =>
        LOOConcentration.deleteAt D i) P Pshort := by
    exact (measurePreserving_fst (μ := Pshort) (ν := μ)).comp hHeldMap
  have hDeleteFreshMap : MeasurePreserving Φ Q Qshort := by
    have h := hDeleteSample.prod (MeasurePreserving.id μ)
    change MeasurePreserving
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
          LOOConcentration.Observation (k + 1) (m + 1) =>
        (LOOConcentration.deleteAt p.1 i, p.2)) (P.prod μ) (Pshort.prod μ) at h
    exact h
  have hShortMeas : Measurable shortFresh := hJointMeas n
  have hShortOnFullMeas : Measurable shortOnFull := by
    exact hShortMeas.comp hDeleteFreshMap.measurable
  have hβ : 0 ≤ β (n + 2) := by
    have h := hUniform n 0 (fun _ => 0) 0
    exact (abs_nonneg _).trans h
  have hDiffPoint (p :
      LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
        LOOConcentration.Observation (k + 1) (m + 1)) :
      |shortOnFull p - fullFresh p| ≤ β (n + 2) := by
    change
      |LOOConcentration.fittedLoss (T n) L
          (LOOConcentration.deleteAt p.1 i) p.2 -
        LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2| ≤ β (n + 2)
    rw [show
      LOOConcentration.fittedLoss (T n) L
          (LOOConcentration.deleteAt p.1 i) p.2 -
        LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2 =
          -(LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2 -
            LOOConcentration.fittedLoss (T n) L
              (LOOConcentration.deleteAt p.1 i) p.2) by ring,
      abs_neg]
    exact hUniform n i p.1 p.2
  have hMajor : Integrable (fun p => ‖fullFresh p‖ + β (n + 2)) Q := by
    exact hFull.norm.add (integrable_const (β (n + 2)))
  have hShortOnFull : Integrable shortOnFull Q := by
    apply hMajor.mono' hShortOnFullMeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |shortOnFull p| = |(shortOnFull p - fullFresh p) - -fullFresh p| := by
        congr 1
        ring
      _ ≤ |shortOnFull p - fullFresh p| + |-fullFresh p| := abs_sub _ _
      _ ≤ β (n + 2) + |fullFresh p| := by
        calc
          _ ≤ β (n + 2) + |-fullFresh p| := add_le_add (hDiffPoint p) le_rfl
          _ = β (n + 2) + |fullFresh p| := by simp
      _ = |fullFresh p| + β (n + 2) := by ring
  have hShortFresh : Integrable shortFresh Qshort := by
    exact (hDeleteFreshMap.integrable_comp
      hShortMeas.aestronglyMeasurable).mp hShortOnFull
  have hHeld : Integrable
      (fun D : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) =>
        LOOConcentration.fittedLoss (T n) L
          (LOOConcentration.deleteAt D i) (D i)) P := by
    exact hHeldMap.integrable_comp_of_integrable hShortFresh
  have hFreshIntegral :
      (∫ p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
          LOOConcentration.Observation (k + 1) (m + 1),
        shortOnFull p ∂Q) =
      ∫ p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1) ×
          LOOConcentration.Observation (k + 1) (m + 1),
        shortFresh p ∂Qshort := by
    have hMapMeas : AEStronglyMeasurable shortFresh (Measure.map Φ Q) := by
      rw [hDeleteFreshMap.map_eq]
      exact hShortMeas.aestronglyMeasurable
    have hIntegral :=
      integral_map hDeleteFreshMap.measurable.aemeasurable hMapMeas
    rw [hDeleteFreshMap.map_eq] at hIntegral
    exact hIntegral.symm
  have hHeldIntegral :
      (∫ D : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2),
        LOOConcentration.fittedLoss (T n) L
          (LOOConcentration.deleteAt D i) (D i) ∂P) =
      ∫ p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 1) ×
          LOOConcentration.Observation (k + 1) (m + 1),
        shortFresh p ∂Qshort := by
    exact LOOConcentration.deleted_section_integral μ i shortFresh hShortFresh
  have hDiffInt : Integrable (fun p => shortOnFull p - fullFresh p) Q :=
    hShortOnFull.sub hFull
  have hFreshBias :
      |(∫ p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
          LOOConcentration.Observation (k + 1) (m + 1),
        shortOnFull p ∂Q) -
        (∫ p : LOOConcentration.Dataset
            (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
            LOOConcentration.Observation (k + 1) (m + 1),
          fullFresh p ∂Q)| ≤ β (n + 2) := by
    calc
      _ = |∫ p, shortOnFull p - fullFresh p ∂Q| := by
        rw [integral_sub hShortOnFull hFull]
      _ ≤ ∫ p, |shortOnFull p - fullFresh p| ∂Q := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (fun p : LOOConcentration.Dataset
                (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
                LOOConcentration.Observation (k + 1) (m + 1) =>
              shortOnFull p - fullFresh p))
      _ ≤ ∫ _p, |β (n + 2)| ∂Q :=
        integral_mono hDiffInt.norm (integrable_const |β (n + 2)|)
          (fun p =>
            calc
              |shortOnFull p - fullFresh p| ≤ β (n + 2) := hDiffPoint p
              _ = |β (n + 2)| := (abs_of_nonneg hβ).symm)
      _ = β (n + 2) := by simp [abs_of_nonneg hβ]
  refine ⟨hHeld, ?_⟩
  calc
    _ = |(∫ p : LOOConcentration.Dataset
        (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
        LOOConcentration.Observation (k + 1) (m + 1),
        shortOnFull p ∂Q) -
        (∫ p : LOOConcentration.Dataset
          (LOOConcentration.Observation (k + 1) (m + 1)) (n + 2) ×
          LOOConcentration.Observation (k + 1) (m + 1),
          fullFresh p ∂Q)| := by
      rw [hHeldIntegral, ← hFreshIntegral]
    _ ≤ β (n + 2) := hFreshBias

end LOOConcentration.Manuscript.Internal
