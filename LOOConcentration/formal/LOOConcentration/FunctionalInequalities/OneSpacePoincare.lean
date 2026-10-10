import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# One-space perturbation input for Poincaré

The bounded perturbation `1 + εg` remains in the finite-energy test class of
the frozen one-observation logarithmic Sobolev inequality.  This file records
that admissibility input and the resulting entropy bound.  The entropy
second-order limit is a separate obligation.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- The perturbation `1 + εg`, equipped with its local Lipschitz proof. -/
def oneObservationPerturbation {k m : ℕ}
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (ε : ℝ) :
    {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)} :=
  ⟨fun z => 1 + ε * g.1 z, by
    intro z
    obtain ⟨U, hU, K, hK, hLip⟩ := g.2 z
    refine ⟨U, hU, |ε| * K, mul_nonneg (abs_nonneg ε) hK, ?_⟩
    intro w hw v hv
    calc
      |(1 + ε * g.1 w) - (1 + ε * g.1 v)| =
          |ε| * |g.1 w - g.1 v| := by
            rw [show (1 + ε * g.1 w) - (1 + ε * g.1 v) =
              ε * (g.1 w - g.1 v) by ring, abs_mul]
      _ ≤ |ε| * (K * observationNorm (w - v)) :=
          mul_le_mul_of_nonneg_left (hLip w hw v hv) (abs_nonneg ε)
      _ = (|ε| * K) * observationNorm (w - v) := by ring⟩

private theorem oneObservationPerturbation_quotient_eq {k m : ℕ}
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (ε : ℝ) (z w : Observation (k + 1) (m + 1)) :
    |(oneObservationPerturbation g ε).1 w -
        (oneObservationPerturbation g ε).1 z| / observationNorm (w - z) =
      |ε| * (|g.1 w - g.1 z| / observationNorm (w - z)) := by
  by_cases hw : w = z
  · subst w
    simp
  · have hden : observationNorm (w - z) ≠ 0 :=
      (observationNorm_sub_pos hw).ne'
    have hdiff : (oneObservationPerturbation g ε).1 w -
        (oneObservationPerturbation g ε).1 z = ε * (g.1 w - g.1 z) := by
      simp only [oneObservationPerturbation]
      ring
    rw [hdiff, abs_mul]
    field_simp [hden]

theorem observationLocalSlope_oneObservationPerturbation_le {k m : ℕ}
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (ε : ℝ) (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope (oneObservationPerturbation g ε) z ≤
      |ε| * observationLocalSlope g z := by
  rw [observationLocalSlope]
  change limsup
      (fun w => |(oneObservationPerturbation g ε).1 w -
        (oneObservationPerturbation g ε).1 z| / observationNorm (w - z))
      (𝓝[≠] z) ≤ |ε| * limsup
        (fun w => |g.1 w - g.1 z| / observationNorm (w - z)) (𝓝[≠] z)
  have hquot := oneObservationPerturbation_quotient_eq g ε z
  simp_rw [hquot]
  have hmul := limsup_mul_le
      (f := 𝓝[≠] z)
      (u := fun _ : Observation (k + 1) (m + 1) => |ε|)
      (v := fun w => |g.1 w - g.1 z| / observationNorm (w - z))
      (Filter.Frequently.of_forall fun _ => abs_nonneg ε)
      Filter.isBoundedUnder_const
      (Filter.Eventually.of_forall fun w =>
        div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (observationSlope_bounded g z)
  have hpoint :
      (fun w : Observation (k + 1) (m + 1) =>
        |ε| * (|g.1 w - g.1 z| / observationNorm (w - z))) =
      (fun _ : Observation (k + 1) (m + 1) => |ε|) *
        (fun w => |g.1 w - g.1 z| / observationNorm (w - z)) := by
    funext w
    rfl
  rw [hpoint]
  simpa only [limsup_const] using hmul

theorem observationLocalSlope_oneObservationPerturbation_eq {k m : ℕ}
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (ε : ℝ) (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope (oneObservationPerturbation g ε) z =
      |ε| * observationLocalSlope g z := by
  have hupper := observationLocalSlope_oneObservationPerturbation_le g ε z
  by_cases hε : ε = 0
  · subst ε
    have hnonneg := observationLocalSlope_nonneg (oneObservationPerturbation g 0) z
    simp only [abs_zero, zero_mul] at hupper ⊢
    exact le_antisymm hupper hnonneg
  · have hεpos : 0 < |ε| := abs_pos.mpr hε
    have hquot :
        (fun w : Observation (k + 1) (m + 1) =>
          |g.1 w - g.1 z| / observationNorm (w - z)) =
        (fun w => |ε|⁻¹ *
          (|(oneObservationPerturbation g ε).1 w -
            (oneObservationPerturbation g ε).1 z| / observationNorm (w - z))) := by
      funext w
      rw [oneObservationPerturbation_quotient_eq]
      field_simp [ne_of_gt hεpos]
    have hmul := limsup_mul_le
        (f := 𝓝[≠] z)
        (u := fun _ : Observation (k + 1) (m + 1) => |ε|⁻¹)
        (v := fun w =>
          |(oneObservationPerturbation g ε).1 w -
            (oneObservationPerturbation g ε).1 z| / observationNorm (w - z))
        (Filter.Frequently.of_forall fun _ => (inv_nonneg.mpr (le_of_lt hεpos)))
        Filter.isBoundedUnder_const
        (Filter.Eventually.of_forall fun w =>
          div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        (observationSlope_bounded (oneObservationPerturbation g ε) z)
    have hreverse : observationLocalSlope g z ≤
        |ε|⁻¹ * observationLocalSlope (oneObservationPerturbation g ε) z := by
      change limsup
          (fun w => |g.1 w - g.1 z| / observationNorm (w - z)) (𝓝[≠] z) ≤
        |ε|⁻¹ * limsup
          (fun w => |(oneObservationPerturbation g ε).1 w -
            (oneObservationPerturbation g ε).1 z| / observationNorm (w - z)) (𝓝[≠] z)
      rw [hquot]
      have hpoint :
          (fun w : Observation (k + 1) (m + 1) =>
            |ε|⁻¹ * (|(oneObservationPerturbation g ε).1 w -
              (oneObservationPerturbation g ε).1 z| / observationNorm (w - z))) =
          (fun _ : Observation (k + 1) (m + 1) => |ε|⁻¹) *
            (fun w => |(oneObservationPerturbation g ε).1 w -
              (oneObservationPerturbation g ε).1 z| / observationNorm (w - z)) := by
        funext w
        rfl
      rw [hpoint]
      simpa only [limsup_const] using hmul
    have hscale : |ε| * observationLocalSlope g z ≤
        observationLocalSlope (oneObservationPerturbation g ε) z := by
      calc
        |ε| * observationLocalSlope g z ≤
            |ε| * (|ε|⁻¹ * observationLocalSlope (oneObservationPerturbation g ε) z) :=
              mul_le_mul_of_nonneg_left hreverse (le_of_lt hεpos)
        _ = observationLocalSlope (oneObservationPerturbation g ε) z := by
          field_simp [ne_of_gt hεpos]
    exact le_antisymm hupper hscale

theorem integrable_observationLocalSlope_sq_oneObservationPerturbation
    {k m : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    (ε : ℝ)
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ) :
    Integrable (fun z => observationLocalSlope (oneObservationPerturbation g ε) z ^ 2) μ := by
  simpa only [observationLocalSlope_oneObservationPerturbation_eq, mul_pow, sq_abs,
    mul_comm] using hgEnergy.const_mul (ε ^ 2)

theorem oneObservationPerturbation_lsi_bound {k m : ℕ}
    {μ : Measure (Observation (k + 1) (m + 1))} [IsProbabilityMeasure μ]
    {C ε : ℝ}
    (hLSI : HasLogSobolev μ C)
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    (hgEnergy : Integrable (fun z => observationLocalSlope g z ^ 2) μ) :
    Integrable (fun z => (oneObservationPerturbation g ε).1 z ^ 2) μ ∧
    Integrable (fun z => (oneObservationPerturbation g ε).1 z ^ 2 *
      Real.log ((oneObservationPerturbation g ε).1 z ^ 2)) μ ∧
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 *
        Real.log ((oneObservationPerturbation g ε).1 z ^ 2) ∂μ) -
    (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) *
        Real.log (∫ z, (oneObservationPerturbation g ε).1 z ^ 2 ∂μ) ≤
      2 * C * (ε ^ 2 * (∫ z, observationLocalSlope g z ^ 2 ∂μ)) := by
  have hSlopeIntegral :
      (∫ z, observationLocalSlope (oneObservationPerturbation g ε) z ^ 2 ∂μ) =
        ε ^ 2 * (∫ z, observationLocalSlope g z ^ 2 ∂μ) := by
    calc
      (∫ z, observationLocalSlope (oneObservationPerturbation g ε) z ^ 2 ∂μ) =
          ∫ z, ε ^ 2 * observationLocalSlope g z ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [observationLocalSlope_oneObservationPerturbation_eq]
        ring_nf
        rw [sq_abs]
        ring
      _ = ε ^ 2 * (∫ z, observationLocalSlope g z ^ 2 ∂μ) :=
          integral_const_mul _ _
  obtain ⟨hSq, hEntropy, hBound⟩ := hLSI.2
    (oneObservationPerturbation g ε)
    (integrable_observationLocalSlope_sq_oneObservationPerturbation ε g hgEnergy)
  refine ⟨hSq, hEntropy, ?_⟩
  simpa only [hSlopeIntegral] using hBound

theorem oneObservationPerturbation_pos_of_bounded {k m : ℕ}
    (g : {f : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |f w - f v| ≤ K * observationNorm (w - v)})
    {B ε : ℝ}
    (hbounded : ∀ z, |g.1 z| ≤ B)
    (hsmall : |ε| * (B + 1) < 1)
    (z : Observation (k + 1) (m + 1)) :
    0 < (oneObservationPerturbation g ε).1 z := by
  have hεg : |ε * g.1 z| < 1 := by
    calc
      |ε * g.1 z| = |ε| * |g.1 z| := abs_mul _ _
      _ ≤ |ε| * B := mul_le_mul_of_nonneg_left (hbounded z) (abs_nonneg ε)
      _ ≤ |ε| * (B + 1) := by gcongr; linarith
      _ < 1 := hsmall
  have hlower : -|ε * g.1 z| ≤ ε * g.1 z := neg_abs_le _
  unfold oneObservationPerturbation
  dsimp
  linarith

end LOOConcentration
