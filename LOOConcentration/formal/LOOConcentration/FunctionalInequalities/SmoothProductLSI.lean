import LOOConcentration.Analysis.DatasetMeasureTransport
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.FunctionalInequalities.CoordinatePoincare
import LOOConcentration.FunctionalInequalities.EntropyCoordinateTransport
import LOOConcentration.FunctionalInequalities.FiniteEntropySubadditivity
import LOOConcentration.FunctionalInequalities.EntropyMixture
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.Geometry.SmoothCoordinateSections
import LOOConcentration.Geometry.SmoothLocalSlope
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Bounded-positive smooth product LSI assembly

The actual one-observation log-Sobolev inequality applies to each reviewed
coordinate-section witness. Finite bounded-positive entropy subadditivity and
the smooth collective coordinate-energy identity/admission are consumed from
their independently reviewed producers.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- Normalization bridge between the frozen LSI entropy and the concentration
entropy. The two definitions have the same formula. -/
theorem looconcentrationEntropy_eq_entropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) :
    looconcentrationEntropy μ g = entropy μ g := rfl

/-- Apply the original frozen one-space LSI to the actual section witness
constructed by `CoordinatePoincare`. No product inequality is assumed. -/
theorem coordinate_section_entropy_lsi
    {k m n : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C : ℝ}
    (hLSI : HasLogSobolev μ C)
    (F : LocallyLipschitzDataFunction k m n)
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (hEnergy : Integrable
      (fun z => observationLocalSlope (coordinateSectionWitness F i tail) z ^ 2) μ) :
    entropy μ (fun z => (coordinateSectionWitness F i tail).1 z ^ 2) ≤
      2 * C * ∫ z,
        observationLocalSlope (coordinateSectionWitness F i tail) z ^ 2 ∂μ := by
  have h := hLSI.2 (coordinateSectionWitness F i tail) hEnergy
  simpa [entropy] using h.2.2

private noncomputable def smoothProductSectionEnergy
    {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1)) :
    Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
  fun p =>
    (observationLocalSlope
      (coordinateSectionWitness (smoothDatasetPullback f hf) i p.2) p.1) ^ 2

private noncomputable def smoothProductSectionEnergyAt
    {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (D : DataCarrier k m n) : ℝ :=
  smoothProductSectionEnergy f hf i
    ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i) D)

/-- Same-constant product LSI for the actual smooth pullback in the
bounded-positive class. It consumes the audited finite entropy induction and
the audited smooth coordinate-section energy and collective identity. -/
theorem smooth_product_lsi_bounded_positive
    {k m n : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C : ℝ}
    (hLSI : HasLogSobolev μ C)
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (ε B : ℝ) (hε : 0 < ε)
    (hBounds : ∀ D : DataCarrier k m n,
      ε ≤ (smoothDatasetPullback f hf).1 D ∧
        (smoothDatasetPullback f hf).1 D ≤ B)
    (hFullEnergy : Integrable
      (fun D : DataCarrier k m n =>
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
        (fun D : DataCarrier k m n => (smoothDatasetPullback f hf).1 D ^ 2) ≤
      2 * C * ∫ D : DataCarrier k m n,
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2
          ∂Measure.pi fun _ : Fin (n + 1) => μ := by
  let u := smoothDatasetPullback f hf
  let fullν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let tailν : Measure (Fin n → Observation (k + 1) (m + 1)) :=
    Measure.pi fun _ : Fin n => μ
  have hUmeas : Measurable u.1 := by
    change Measurable (fun D : DataCarrier k m n =>
      f (datasetToEuclidean D))
    exact hf.continuous.measurable.comp measurable_datasetToEuclidean
  have hεsqpos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hBsqnonneg : 0 ≤ B ^ 2 := sq_nonneg B
  have hSquareBounds (D : DataCarrier k m n) :
      ε ^ 2 ≤ u.1 D ^ 2 ∧ u.1 D ^ 2 ≤ B ^ 2 := by
    have hD := hBounds D
    constructor <;> nlinarith [sq_nonneg (u.1 D - ε), sq_nonneg (B - u.1 D)]
  have hSquareMeas : Measurable (fun D : DataCarrier k m n => u.1 D ^ 2) :=
    hUmeas.pow_const 2
  have hFiniteEntropySubadditivity :=
    entropy_piFin_succ_subadditive_bounded_positive μ
      (fun D : DataCarrier k m n => u.1 D ^ 2) (ε ^ 2) (B ^ 2)
      hSquareMeas hεsqpos hSquareBounds
  have hJointEnergy (i : Fin (n + 1)) :
      Integrable (smoothProductSectionEnergy f hf i) (μ.prod tailν) := by
    change Integrable (smoothCoordinateSectionEnergy f hf i)
      (μ.prod (Measure.pi fun _ : Fin n => μ))
    exact integrable_smoothCoordinateSectionEnergy_of_fullEnergy f hf hFullEnergy i
  have hSectionEntropyIntegrable (i : Fin (n + 1)) :
      Integrable
        (fun tail : Fin n → Observation (k + 1) (m + 1) =>
          entropy μ (fun z => u.1
            ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm
                (z, tail)) ^ 2)) tailν := by
    let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
        Observation (k + 1) (m + 1) ×
          (Fin n → Observation (k + 1) (m + 1)) :=
      MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
    let G : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
      fun p => u.1 (e.symm p) ^ 2
    have hGmeas : Measurable G := hUmeas.comp e.symm.measurable |>.pow_const 2
    have hGnonneg (p : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1))) : 0 ≤ G p :=
      (le_of_lt hεsqpos).trans (hSquareBounds (e.symm p)).1
    have hGle (p : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1))) : G p ≤ B ^ 2 :=
      (hSquareBounds (e.symm p)).2
    change Integrable (fun tail => entropy μ (fun z => G (z, tail))) tailν
    exact entropy_section_integrable μ tailν G (B ^ 2) hBsqnonneg
      hGmeas hGnonneg hGle
  have hSectionEntropyBound (i : Fin (n + 1)) :
      ∫ tail : Fin n → Observation (k + 1) (m + 1),
        entropy μ (fun z => u.1
          ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm
              (z, tail)) ^ 2) ∂tailν ≤
        2 * C * ∫ tail : Fin n → Observation (k + 1) (m + 1),
          ∫ z, smoothProductSectionEnergy f hf i (z, tail) ∂μ ∂tailν := by
    let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
        Observation (k + 1) (m + 1) ×
          (Fin n → Observation (k + 1) (m + 1)) :=
      MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
    let energy : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
      smoothProductSectionEnergy f hf i
    have hEnergyAE : ∀ᵐ tail ∂tailν,
        Integrable (fun z => energy (z, tail)) μ :=
      (hJointEnergy i).prod_left_ae
    have hLSIAE : ∀ᵐ tail ∂tailν,
        entropy μ (fun z => u.1 (e.symm (z, tail)) ^ 2) ≤
          2 * C * ∫ z, energy (z, tail) ∂μ := by
      filter_upwards [hEnergyAE] with tail hE
      have hApplied := coordinate_section_entropy_lsi hLSI u i tail hE
      simpa [energy, e, coordinateSectionWitness, smoothProductSectionEnergy,
        entropy] using hApplied
    have hRightInt : Integrable
        (fun tail => 2 * C * ∫ z, energy (z, tail) ∂μ) tailν :=
      ((hJointEnergy i).integral_prod_right).const_mul (2 * C)
    have hIntegralMono := integral_mono_ae (hSectionEntropyIntegrable i)
      hRightInt hLSIAE
    have hEnergyEq :
        (∫ tail, ∫ z, energy (z, tail) ∂μ ∂tailν) =
          ∫ tail, ∫ z,
            smoothProductSectionEnergy f hf i (z, tail) ∂μ ∂tailν := rfl
    calc
      _ ≤ ∫ tail, 2 * C * ∫ z, energy (z, tail) ∂μ ∂tailν := hIntegralMono
      _ = 2 * C * ∫ tail, ∫ z, energy (z, tail) ∂μ ∂tailν := by
        rw [integral_const_mul]
      _ = 2 * C * ∫ tail, ∫ z,
          smoothProductSectionEnergy f hf i (z, tail) ∂μ ∂tailν := by
        rw [hEnergyEq]
  have hEnergyAtIntegrable (i : Fin (n + 1)) :
      Integrable (fun D : DataCarrier k m n =>
        smoothProductSectionEnergyAt f hf i D) fullν := by
    let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
        Observation (k + 1) (m + 1) ×
          (Fin n → Observation (k + 1) (m + 1)) :=
      MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
    have hMP : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i)
        fullν (μ.prod tailν) := by
      simpa [fullν, tailν] using
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) i)
    change Integrable (fun D => smoothProductSectionEnergy f hf i
      ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i) D)) fullν
    exact hMP.integrable_comp_of_integrable (hJointEnergy i)
  have hIntegratedSectionIdentity :
      (∑ i : Fin (n + 1),
        ∫ tail : Fin n → Observation (k + 1) (m + 1),
          ∫ z, smoothProductSectionEnergy f hf i (z, tail) ∂μ ∂tailν) =
        ∫ D : DataCarrier k m n,
          (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2 ∂fullν := by
    calc
      _ = ∑ i : Fin (n + 1),
          ∫ D : DataCarrier k m n,
            smoothProductSectionEnergyAt f hf i D ∂fullν := by
        apply Finset.sum_congr rfl
        intro i hi
        let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
            Observation (k + 1) (m + 1) ×
              (Fin n → Observation (k + 1) (m + 1)) :=
          MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
        have hMP : MeasurePreserving
            (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i)
            fullν (μ.prod tailν) := by
          simpa [fullν, tailν] using
            (measurePreserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => μ) i)
        calc
          _ = ∫ p : Observation (k + 1) (m + 1) ×
              (Fin n → Observation (k + 1) (m + 1)),
                smoothProductSectionEnergy f hf i p ∂(μ.prod tailν) :=
            (integral_prod_symm _ (hJointEnergy i)).symm
          _ = ∫ D : DataCarrier k m n,
              smoothProductSectionEnergy f hf i (e D) ∂fullν :=
            (hMP.integral_comp' (smoothProductSectionEnergy f hf i)).symm
          _ = _ := rfl
      _ = ∫ D : DataCarrier k m n,
          (∑ i : Fin (n + 1),
            smoothProductSectionEnergyAt f hf i D) ∂fullν := by
        symm
        exact integral_finsetSum Finset.univ (fun i hi => hEnergyAtIntegrable i)
      _ = ∫ D : DataCarrier k m n,
          (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2 ∂fullν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun D => by
          have hsum := sum_smoothCoordinateSection_slope_sq f hf D
          simpa [smoothProductSectionEnergyAt, smoothProductSectionEnergy,
            smoothCoordinateSectionEnergy, smoothCoordinateSectionTail] using hsum
  calc
    looconcentrationEntropy fullν (fun D : DataCarrier k m n => u.1 D ^ 2) =
        entropy fullν (fun D : DataCarrier k m n => u.1 D ^ 2) := rfl
    _ ≤ ∑ i : Fin (n + 1),
        ∫ tail : Fin n → Observation (k + 1) (m + 1),
          entropy μ (fun z => u.1
            ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm
                (z, tail)) ^ 2) ∂tailν := by
      simpa [u, fullν, tailν] using hFiniteEntropySubadditivity
    _ ≤ ∑ i : Fin (n + 1),
        2 * C * ∫ tail : Fin n → Observation (k + 1) (m + 1),
          ∫ z, smoothProductSectionEnergy f hf i (z, tail) ∂μ ∂tailν :=
      Finset.sum_le_sum fun i hi => hSectionEntropyBound i
    _ = 2 * C * ∫ D : DataCarrier k m n,
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2 ∂fullν := by
      rw [← Finset.mul_sum, hIntegratedSectionIdentity]
    _ = 2 * C * ∫ D : DataCarrier k m n,
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2
          ∂Measure.pi fun _ : Fin (n + 1) => μ := by
      rfl

#print axioms looconcentrationEntropy_eq_entropy
#print axioms coordinate_section_entropy_lsi
#print axioms smooth_product_lsi_bounded_positive

end LOOConcentration
