import LOOConcentration.Concentration.ThetaRateFacts
import LOOConcentration.Results.StandingFacts
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of the deleted conditional concentration rate

The standing assumption supplies integrability of the two rate coefficients
at the deleted training size. Measurable representatives of those
coefficients give an almost-everywhere measurable representative of the
literal frozen rate, including its zero-denominator branches.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

private theorem thetaRate_proof_irrel
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha ha' : 0 ≤ a) (hb hb' : 0 ≤ b) :
    thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
      thetaRate C M₂ hC hM₂ r hr t ht a b ha' hb' := by
  rfl

private theorem thetaRate_congr_coefficients
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a a' b b' : ℝ) (haa : a = a') (hbb : b = b')
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
    thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
      thetaRate C M₂ hC hM₂ r hr t ht a' b' ha' hb' := by
  subst a'
  subst b'
  exact thetaRate_proof_irrel C M₂ hC hM₂ r hr t ht a b ha ha' hb hb'

/-- The literal frozen rate is AE strongly measurable when its nonnegative
coefficients are integrable. The proof constructs measurable nonnegative
representatives, then transfers measurability across their AE equality. -/
theorem aestronglyMeasurable_thetaRate_of_integrable_coefficients
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    AEStronglyMeasurable
      (fun x => thetaRate C M₂ hC hM₂ r hr t ht
        (a x) (b x) (ha0 x) (hb0 x)) μ := by
  let aRep : α → ℝ := fun x => max (ha.aestronglyMeasurable.mk a x) 0
  let bRep : α → ℝ := fun x => max (hb.aestronglyMeasurable.mk b x) 0
  have haRep_meas : Measurable aRep := by
    dsimp [aRep]
    exact ha.aestronglyMeasurable.measurable_mk.max measurable_const
  have hbRep_meas : Measurable bRep := by
    dsimp [bRep]
    exact hb.aestronglyMeasurable.measurable_mk.max measurable_const
  have haRep_nonneg : ∀ x, 0 ≤ aRep x := by
    intro x
    exact le_max_right _ _
  have hbRep_nonneg : ∀ x, 0 ≤ bRep x := by
    intro x
    exact le_max_right _ _
  have ha_eq : a =ᵐ[μ] aRep := by
    filter_upwards [ha.aestronglyMeasurable.ae_eq_mk] with x hx
    change a x = max (ha.aestronglyMeasurable.mk a x) 0
    rw [← hx]
    exact (max_eq_left (ha0 x)).symm
  have hb_eq : b =ᵐ[μ] bRep := by
    filter_upwards [hb.aestronglyMeasurable.ae_eq_mk] with x hx
    change b x = max (hb.aestronglyMeasurable.mk b x) 0
    rw [← hx]
    exact (max_eq_left (hb0 x)).symm
  let θRep : α → ℝ := fun x =>
    thetaRate C M₂ hC hM₂ r hr t ht
      (aRep x) (bRep x) (haRep_nonneg x) (hbRep_nonneg x)
  have hθRep_meas : Measurable θRep := by
    dsimp [θRep]
    exact measurable_thetaRate haRep_meas hbRep_meas C M₂ hC hM₂ r hr t ht
      haRep_nonneg hbRep_nonneg
  have hθ_eq :
      (fun x => thetaRate C M₂ hC hM₂ r hr t ht
        (a x) (b x) (ha0 x) (hb0 x)) =ᵐ[μ] θRep := by
    filter_upwards [ha_eq, hb_eq] with x hax hbx
    dsimp [θRep]
    exact thetaRate_congr_coefficients C M₂ hC hM₂ r hr t ht
      (a x) (aRep x) (b x) (bRep x) hax hbx
      (ha0 x) (hb0 x) (haRep_nonneg x) (hbRep_nonneg x)
  exact hθRep_meas.aestronglyMeasurable.congr hθ_eq.symm

/-- An integrable pair of nonnegative coefficients yields an integrable
frozen rate on any finite measure space. -/
theorem integrable_thetaRate_of_integrable_coefficients
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {a b : α → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    Integrable
      (fun x => thetaRate C M₂ hC hM₂ r hr t ht
        (a x) (b x) (ha0 x) (hb0 x)) μ := by
  have hθmeas := aestronglyMeasurable_thetaRate_of_integrable_coefficients
    ha hb C M₂ hC hM₂ r hr t ht ha0 hb0
  apply Integrable.of_mem_Icc 0 1 hθmeas.aemeasurable
  filter_upwards [] with x
  exact thetaRate_mem_Icc C M₂ hC hM₂ r hr t ht
    (a x) (b x) (ha0 x) (hb0 x)

/-- The standing-data rate at the deleted training size is pointwise in
`[0,1]`, with the frozen zero-denominator conventions. -/
theorem standing_deletedThetaRate_mem_Icc {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d t : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (ht : 0 < t) (z : Observation (k + 1) (m + 1)) :
    thetaRate C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
      (standing_moment_nonneg h) (n + 1) (by omega) t ht
      (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (standing_delta_nonneg h n z).1 (standing_delta_nonneg h n z).2 ∈
        Set.Icc 0 1 := by
  exact thetaRate_mem_Icc C (∫ z, observationNormSq z ∂μ)
    (standing_lsi_pos h) (standing_moment_nonneg h) (n + 1) (by omega)
    t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
    (standing_delta_nonneg h n z).1 (standing_delta_nonneg h n z).2

/-- The actual frozen conditional deleted rate is AE strongly measurable
from only the original standing integrability of `δ₁` and `δ₂`. -/
theorem standing_deletedThetaRate_aestronglyMeasurable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d t : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (ht : 0 < t) :
    AEStronglyMeasurable
      (fun z : Observation (k + 1) (m + 1) =>
        thetaRate C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
          (standing_moment_nonneg h) (n + 1) (by omega) t ht
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (standing_delta_nonneg h n z).1 (standing_delta_nonneg h n z).2) μ := by
  have hδ₁ : Integrable (δ₁ (n + 1)) μ := h.2.2.2.1
  have hδ₂ : Integrable (δ₂ (n + 1)) μ := h.2.2.2.2.1
  exact aestronglyMeasurable_thetaRate_of_integrable_coefficients
    hδ₁ hδ₂ C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
    (standing_moment_nonneg h) (n + 1) (by omega) t ht
    (fun z => (standing_delta_nonneg h n z).1)
    (fun z => (standing_delta_nonneg h n z).2)

/-- The actual frozen conditional deleted rate is integrable under the
standing assumption, with no pointwise measurability premise on its rates. -/
theorem standing_deletedThetaRate_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d t : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (ht : 0 < t) :
    Integrable
      (fun z : Observation (k + 1) (m + 1) =>
        thetaRate C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
          (standing_moment_nonneg h) (n + 1) (by omega) t ht
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (standing_delta_nonneg h n z).1 (standing_delta_nonneg h n z).2) μ := by
  have hδ₁ : Integrable (δ₁ (n + 1)) μ := h.2.2.2.1
  have hδ₂ : Integrable (δ₂ (n + 1)) μ := h.2.2.2.2.1
  exact integrable_thetaRate_of_integrable_coefficients
    hδ₁ hδ₂ C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
    (standing_moment_nonneg h) (n + 1) (by omega) t ht
    (fun z => (standing_delta_nonneg h n z).1)
    (fun z => (standing_delta_nonneg h n z).2)

#print axioms LOOConcentration.aestronglyMeasurable_thetaRate_of_integrable_coefficients
#print axioms LOOConcentration.integrable_thetaRate_of_integrable_coefficients
#print axioms LOOConcentration.standing_deletedThetaRate_mem_Icc
#print axioms LOOConcentration.standing_deletedThetaRate_aestronglyMeasurable
#print axioms LOOConcentration.standing_deletedThetaRate_integrable

end LOOConcentration
