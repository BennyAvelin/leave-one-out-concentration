import LOOConcentration.FunctionalInequalities.FiniteEfronStein
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinate-energy Poincaré bound

This module applies the one-observation Poincaré inequality to actual
coordinate sections and combines the resulting bounds with finite
Efron–Stein. Joint integrability of the coordinate-energy kernels remains an
explicit finite-energy input.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private abbrev DatasetLocallyLip {k m n : ℕ} :=
  {F : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
    ∀ D, ∃ U ∈ 𝓝 D, ∃ K : ℝ, 0 ≤ K ∧
      ∀ D' ∈ U, ∀ D'' ∈ U,
        |F D' - F D''| ≤ K * datasetNorm (D' - D'')}

private theorem datasetNorm_piFinSuccAbove_symm_sub
    {k m n : ℕ} (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (z z' : Observation (k + 1) (m + 1)) :
    datasetNorm
      ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail) -
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm (z', tail)) =
      observationNorm (z - z') := by
  let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
      Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
  let delta : Fin (n + 1) → Observation (k + 1) (m + 1) :=
    e.symm (z, tail) - e.symm (z', tail)
  have hdelta (q : Fin (n + 1)) : delta q = if q = i then z - z' else 0 := by
    by_cases hqi : q = i
    · subst q
      simp [delta, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
    · simp [delta, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, hqi]
  have hdelta_i : delta i = z - z' := by rw [hdelta]; simp
  have hdelta_tail (q : Fin n) : delta (i.succAbove q) = 0 := by
    rw [hdelta]
    simp [Fin.succAbove_ne]
  have hnormSq : datasetNormSq delta = observationNormSq (z - z') := by
    rw [datasetNormSq,
      Fin.sum_univ_succAbove (fun q : Fin (n + 1) => observationNormSq (delta q)) i,
      hdelta_i]
    have hsum :
        (∑ q : Fin n, observationNormSq (delta (i.succAbove q))) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      rw [hdelta_tail]
      simp [observationNormSq]
    rw [hsum]
    simp [observationNormSq]
  unfold datasetNorm observationNorm
  rw [hnormSq]

/-- Restrict a full-dataset locally Lipschitz witness to the actual section
obtained by inserting one observation at coordinate `i`. The section value is
definitionally the full witness evaluated on that insertion. -/
def coordinateSectionWitness {k m n : ℕ}
    (F : {G : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ K : ℝ, 0 ≤ K ∧
        ∀ D' ∈ U, ∀ D'' ∈ U,
          |G D' - G D''| ≤ K * datasetNorm (D' - D'')})
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1)) :
    {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
        ∀ z' ∈ U, ∀ z'' ∈ U,
          |g z' - g z''| ≤ K * observationNorm (z' - z'')} := by
  classical
  let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
      Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i
  let insert : Observation (k + 1) (m + 1) →
      Dataset (Observation (k + 1) (m + 1)) (n + 1) := fun z => e.symm (z, tail)
  refine ⟨fun z => F.1 (insert z), ?_⟩
  intro z
  obtain ⟨U, hU, K, hK, hLip⟩ := F.2 (insert z)
  have hinsertContinuous : Continuous insert := by
    apply continuous_pi
    intro q
    by_cases hqi : q = i
    · subst q
      have heval : (fun z : Observation (k + 1) (m + 1) => insert z i) = id := by
        funext z'
        simp [insert, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
      rw [heval]
      exact continuous_id
    · rcases Fin.eq_self_or_eq_succAbove i q with hq | ⟨j, hq⟩
      · exact (hqi hq).elim
      · subst q
        have hconst : (fun z : Observation (k + 1) (m + 1) => insert z (i.succAbove j)) =
            fun _ => insert (0 : Observation (k + 1) (m + 1)) (i.succAbove j) := by
          funext z'
          simp [insert, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        simpa only [hconst] using
          (continuous_const : Continuous
            (fun _ : Observation (k + 1) (m + 1) => insert 0 (i.succAbove j)))
  have hpreimage : insert ⁻¹' U ∈ 𝓝 z :=
    hinsertContinuous.continuousAt.preimage_mem_nhds hU
  refine ⟨insert ⁻¹' U, hpreimage, K, hK, ?_⟩
  intro z' hz' z'' hz''
  calc
    |F.1 (insert z') - F.1 (insert z'')| ≤
        K * datasetNorm (insert z' - insert z'') := hLip _ hz' _ hz''
    _ = K * observationNorm (z' - z'') := by
      rw [datasetNorm_piFinSuccAbove_symm_sub]

private theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

private theorem square_norm_bound {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    ‖x ^ 2‖ ≤ B ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ B ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hB (abs_nonneg x))
      nlinarith [hprod]

private theorem integralVariance_section_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    Integrable (fun y => integralVariance μ (fun x => F (x, y))) ν := by
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let second : β → ℝ := fun y => ∫ x, F (x, y) ^ 2 ∂μ
  let variance : β → ℝ := fun y => integralVariance μ (fun x => F (x, y))
  have hF2 : Measurable (fun p : α × β => F p ^ 2) := hF.pow_const 2
  have hmeanStrong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hsecondStrong : StronglyMeasurable second := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ^ 2 ∂μ)
    exact hF2.stronglyMeasurable.integral_prod_left'
  have hmeanMeas : Measurable mean := hmeanStrong.measurable
  have hsecondMeas : Measurable second := hsecondStrong.measurable
  have hvarMeas : Measurable variance := by
    change Measurable (fun y => second y - mean y ^ 2)
    exact hsecondMeas.sub (hmeanMeas.pow_const 2)
  have hmeanBound (y : β) : |mean y| ≤ B := by
    have hsectionMeas : Measurable (fun x : α => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    have hsectionInt : Integrable (fun x : α => F (x, y)) μ :=
      bounded_measurable_integrable hsectionMeas B fun x => by
        simpa only [Real.norm_eq_abs] using hFbound (x, y)
    calc
      |mean y| ≤ ∫ x, |F (x, y)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : α, B ∂μ :=
        integral_mono hsectionInt.abs (integrable_const B) fun x => hFbound (x, y)
      _ = B := by simp
  have hsecondSectionInt (y : β) : Integrable (fun x : α => F (x, y) ^ 2) μ := by
    have hsqMeas : Measurable (fun x : α => F (x, y) ^ 2) :=
      hF2.comp (measurable_prodMk_right (y := y))
    exact bounded_measurable_integrable hsqMeas (B ^ 2) fun x => by
      exact square_norm_bound hB (hFbound (x, y))
  have hsecondNonneg (y : β) : 0 ≤ second y := by
    calc
      0 = ∫ _ : α, (0 : ℝ) ∂μ := by simp
      _ ≤ ∫ x, F (x, y) ^ 2 ∂μ :=
        integral_mono (by simp) (hsecondSectionInt y) fun x => sq_nonneg _
  have hsecondUpper (y : β) : second y ≤ B ^ 2 := by
    calc
      second y ≤ ∫ _ : α, B ^ 2 ∂μ :=
        integral_mono (hsecondSectionInt y) (integrable_const _) fun x => by
          have hprod := mul_nonneg
            (sub_nonneg.mpr (hFbound (x, y)))
            (add_nonneg hB (abs_nonneg (F (x, y))))
          nlinarith [hprod, sq_abs (F (x, y))]
      _ = B ^ 2 := by simp
  have hsecondBound (y : β) : |second y| ≤ B ^ 2 := by
    rw [abs_of_nonneg (hsecondNonneg y)]
    exact hsecondUpper y
  have hvariance_eq (y : β) : variance y = second y - mean y ^ 2 := by
    simp [variance, integralVariance, mean, second]
  have hvarianceBound (y : β) : ‖variance y‖ ≤ 2 * B ^ 2 := by
    rw [Real.norm_eq_abs, hvariance_eq]
    calc
      |second y - mean y ^ 2| ≤ |second y| + |mean y ^ 2| := abs_sub _ _
      _ ≤ B ^ 2 + B ^ 2 := add_le_add (hsecondBound y) (by
        rw [abs_of_nonneg (sq_nonneg (mean y))]
        have hprod := mul_nonneg
          (sub_nonneg.mpr (hmeanBound y))
          (add_nonneg hB (abs_nonneg (mean y)))
        nlinarith [hprod, sq_abs (mean y)])
      _ = 2 * B ^ 2 := by ring
  exact bounded_measurable_integrable hvarMeas (2 * B ^ 2) hvarianceBound

/-- Coordinate-energy Poincaré bound for a bounded measurable function having
a full dataset locally Lipschitz witness. The only additional predecessor is
joint integrability of the actual coordinate slope-square kernels. -/
theorem integralVariance_piFin_coordinate_poincare
    {k m n : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B : ℝ}
    (hLSI : HasLogSobolev μ C)
    (F : DatasetLocallyLip)
    (hFmeas : Measurable F.1)
    (hFbound : ∀ D, |F.1 D| ≤ B)
    (hfiniteEnergy : ∀ i : Fin (n + 1),
      Integrable
        (fun p : Observation (k + 1) (m + 1) ×
            (Fin n → Observation (k + 1) (m + 1)) =>
          observationLocalSlope (coordinateSectionWitness F i p.2) p.1 ^ 2)
        (μ.prod (Measure.pi fun _ : Fin n => μ))) :
    integralVariance (Measure.pi fun _ : Fin (n + 1) => μ) F.1 ≤
      C * ∑ i : Fin (n + 1),
        ∫ tail : Fin n → Observation (k + 1) (m + 1),
          ∫ z, observationLocalSlope (coordinateSectionWitness F i tail) z ^ 2 ∂μ
            ∂Measure.pi (fun _ : Fin n => μ) := by
  let ν : Measure (Fin n → Observation (k + 1) (m + 1)) :=
    Measure.pi fun _ : Fin n => μ
  let fullν : Measure (Fin (n + 1) → Observation (k + 1) (m + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let energyKernel (i : Fin (n + 1)) :
      Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
    fun p => observationLocalSlope (coordinateSectionWitness F i p.2) p.1 ^ 2
  let varianceKernel (i : Fin (n + 1)) :
      (Fin n → Observation (k + 1) (m + 1)) → ℝ := fun tail =>
    integralVariance μ
      (fun z => F.1 ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail)))
  have hB : 0 ≤ B := (abs_nonneg (F.1 0)).trans (hFbound 0)
  have hvarianceKernelInt (i : Fin (n + 1)) :
      Integrable (varianceKernel i) ν := by
    let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
        Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) =>
        Observation (k + 1) (m + 1)) i
    let G : Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
      fun p => F.1 (e.symm p)
    have hG : Measurable G := hFmeas.comp e.symm.measurable
    have hGbound (p : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1))) : |G p| ≤ B := hFbound (e.symm p)
    change Integrable (fun tail => integralVariance μ (fun z => G (z, tail))) ν
    exact integralVariance_section_integrable μ ν G B hB hG hGbound
  have hcoordinateEnergyInt (i : Fin (n + 1)) :
      Integrable (fun tail => ∫ z, energyKernel i (z, tail) ∂μ) ν := by
    exact (hfiniteEnergy i).integral_prod_right
  have hcoordinateBound (i : Fin (n + 1)) :
      (∫ tail, varianceKernel i tail ∂ν) ≤
        C * ∫ tail, ∫ z, energyKernel i (z, tail) ∂μ ∂ν := by
    let e : (Fin (n + 1) → Observation (k + 1) (m + 1)) ≃ᵐ
        Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) =>
        Observation (k + 1) (m + 1)) i
    let G : Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
      fun p => F.1 (e.symm p)
    have hG : Measurable G := hFmeas.comp e.symm.measurable
    have hGbound (p : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1))) : |G p| ≤ B := hFbound (e.symm p)
    have hsectionEnergyAE : ∀ᵐ tail ∂ν,
        Integrable (fun z => energyKernel i (z, tail)) μ :=
      (hfiniteEnergy i).prod_left_ae
    have hsectionPoincare : ∀ᵐ tail ∂ν,
        integralVariance μ (fun z => G (z, tail)) ≤
          C * ∫ z, energyKernel i (z, tail) ∂μ := by
      filter_upwards [hsectionEnergyAE] with tail henergy
      have hsectionBound (z : Observation (k + 1) (m + 1)) :
          |(coordinateSectionWitness F i tail).1 z| ≤ B := by
        exact hFbound (e.symm (z, tail))
      exact oneObservation_poincare_variance_from_logSobolev hLSI
        (coordinateSectionWitness F i tail) henergy hsectionBound
    have hrightInt : Integrable
        (fun tail => C * ∫ z, energyKernel i (z, tail) ∂μ) ν :=
      (hcoordinateEnergyInt i).const_mul C
    have hintegralBound := integral_mono_ae (hvarianceKernelInt i) hrightInt ?_
    · simpa only [integral_const_mul] using hintegralBound
    · filter_upwards [hsectionPoincare] with tail htail
      simpa only [varianceKernel, energyKernel, G, e, ν] using htail
  have hEfronStein := integralVariance_piFin_succ_efronStein
    μ n F.1 B hB hFmeas hFbound
  calc
    integralVariance fullν F.1 ≤
        ∑ i : Fin (n + 1), ∫ tail,
          integralVariance μ (fun z => F.1 ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail))) ∂ν := by
      simpa [fullν, ν] using hEfronStein
    _ ≤ ∑ i : Fin (n + 1),
        C * ∫ tail, ∫ z, energyKernel i (z, tail) ∂μ ∂ν :=
      Finset.sum_le_sum fun i _ => by
        simpa [varianceKernel, energyKernel] using hcoordinateBound i
    _ = C * ∑ i : Fin (n + 1),
        ∫ tail, ∫ z, energyKernel i (z, tail) ∂μ ∂ν := by
      rw [← Finset.mul_sum]
    _ = C * ∑ i : Fin (n + 1),
        ∫ tail, ∫ z,
          observationLocalSlope (coordinateSectionWitness F i tail) z ^ 2 ∂μ ∂ν := by
      rfl

#print axioms LOOConcentration.integralVariance_piFin_coordinate_poincare

end LOOConcentration
