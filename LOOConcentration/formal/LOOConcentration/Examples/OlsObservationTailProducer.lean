import LOOConcentration.Frozen.Results.DataDependentConcentration
import LOOConcentration.Examples.OlsObservationGoodSet
import LOOConcentration.Examples.OlsGoodSetPenalty
import LOOConcentration.Examples.OlsObservationMoments
import LOOConcentration.Examples.OlsNoiseRiskL1Bridge
import LOOConcentration.Examples.OlsResponseTailTransport
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open Topology
open scoped ENNReal

local instance : IsProbabilityMeasure gaussianObservationLaw :=
  gaussianObservationLaw_isProbability

private noncomputable def olsObservationBiasEnvelope (n : ℕ) : ℝ :=
  Real.sqrt (1 / ((n + 3 : ℕ) : ℝ) +
    (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) +
  Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
    (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3))

private theorem olsObservationSampleLaw_eq_pair_map (N : ℕ) :
    gaussianObservationSampleLaw N =
      Measure.map (gaussianObservationSampleMap N) (olsPairGaussianLaw N) := by
  rw [← gaussianObservationSampleLaw_eq_map N]
  congr 1

private theorem olsObservationTestError_pairMap {n : ℕ}
    (G : Fin (n + 3) → ℝ × ℝ) :
    olsObservationTestError (gaussianObservationSampleMap (n + 3) G) =
      olsTestError (n := n + 1) G := by
  change olsTestError
      (olsObservationToPairSample (olsPairToObservationSample G)) = olsTestError G
  rw [olsObservationToPairSample_pairToObservationSample]

/-- The actual OLS observation-error event is the same event probability as
the pair-coordinate noise error under the reviewed Gaussian transport. -/
private theorem olsObservationErrorTailProbability_eq_pair {n : ℕ}
    (eps : ℝ) :
    (gaussianObservationSampleLaw (n + 3)).real
        {D : Dataset (Observation 1 1) (n + 3) |
          |olsObservationTestError D| > eps} =
      (olsPairGaussianLaw (n + 3)).real
        {G : Fin (n + 3) → ℝ × ℝ |
          |olsTestError (n := n + 1) G| > eps} := by
  let Eobs : Set (Dataset (Observation 1 1) (n + 3)) :=
    {D | |olsObservationTestError D| > eps}
  let Epair : Set (Fin (n + 3) → ℝ × ℝ) :=
    {G | |olsTestError (n := n + 1) G| > eps}
  have hEobs : MeasurableSet Eobs := by
    exact measurableSet_lt measurable_const
      (measurable_abs.comp (measurable_olsObservationTestError (n := n)))
  have hpre : gaussianObservationSampleMap (n + 3) ⁻¹' Eobs = Epair := by
    ext G
    simp only [Set.mem_preimage, Eobs, Epair, Set.mem_ofPred_eq]
    rw [olsObservationTestError_pairMap]
  calc
    _ = (Measure.map (gaussianObservationSampleMap (n + 3))
        (olsPairGaussianLaw (n + 3))).real Eobs := by
      rw [olsObservationSampleLaw_eq_pair_map]
    _ = (olsPairGaussianLaw (n + 3)).real
        (gaussianObservationSampleMap (n + 3) ⁻¹' Eobs) :=
      map_measureReal_apply (gaussianObservationSampleMap_measurable (n + 3)) hEobs
    _ = (olsPairGaussianLaw (n + 3)).real Epair := by rw [hpre]

/-- Actual OLS observation-noise tails from the certified data-dependent
concentration theorem. The sole open analytic input is the standard Gaussian
log-Sobolev instance, retained explicitly as a conditional predecessor. -/
theorem olsObservationErrorTail_of_hasLogSobolev
    (hLSI : @HasLogSobolev 0 0 gaussianObservationLaw
      gaussianObservationLaw_isProbability 1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ Nε : ℕ, ∀ n : ℕ, Nε ≤ n →
      (gaussianObservationSampleLaw (n + 3)).real
          {D : Dataset (Observation 1 1) (n + 3) |
            |olsObservationTestError D| > eps} ≤
        6 * (n + 3 : ℝ) *
          Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := by
  let bias : ℕ → ℝ := olsObservationBiasEnvelope
  have hbiasT : Tendsto bias atTop (𝓝 0) := by
    change Tendsto olsObservationBiasEnvelope atTop (𝓝 0)
    exact tendsto_olsObservationBiasEnvelope_zero
  have hbiasEventually : ∀ᶠ n : ℕ in atTop, bias n < eps / 4 := by
    have hmem : Set.Iio (eps / 4) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by linarith)
    simpa only [Set.mem_Iio] using hbiasT.eventually hmem
  have hpenaltyEventually : ∀ᶠ n : ℕ in atTop,
      olsObservationGoodSetPenalty n < eps / 4 :=
    olsObservationGoodSetPenalty_eventually_lt eps heps
  have hsizeEventually : ∀ᶠ n : ℕ in atTop, 192 ≤ n + 3 := by
    filter_upwards [eventually_ge_atTop (189 : ℕ)] with n hn
    omega
  have hallEventually : ∀ᶠ n : ℕ in atTop,
      bias n < eps / 4 ∧
      olsObservationGoodSetPenalty n < eps / 4 ∧ 192 ≤ n + 3 :=
    hbiasEventually.and (hpenaltyEventually.and hsizeEventually)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hallEventually
  let Nε : ℕ := max N₀ 189
  refine ⟨Nε, ?_⟩
  intro n hnε
  have hn₀ : N₀ ≤ n := (Nat.le_max_left N₀ 189).trans hnε
  have hn189 : 189 ≤ n := (Nat.le_max_right N₀ 189).trans hnε
  have hconditions := hN₀ n hn₀
  have hnsize : 192 ≤ n + 3 := hconditions.2.2
  have hsmallBias : bias n < eps / 4 := hconditions.1
  have hsmallPenalty : olsObservationGoodSetPenalty n < eps / 4 :=
    hconditions.2.1
  have hn3 : 3 ≤ n := by omega
  let ν : Measure (Dataset (Observation 1 1) (n + 3)) :=
    gaussianObservationSampleLaw (n + 3)
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using gaussianObservationSampleLaw_isProbability (n + 3)
  let K : Set (Dataset (Observation 1 1) (n + 3)) :=
    olsObservationGoodSet n
  let D₀ : Dataset (Observation 1 1) (n + 3) :=
    olsObservationReferencePoint n
  let LK : ℝ := 36007 / Real.sqrt (n + 3 : ℝ)
  let H : Dataset (Observation 1 1) (n + 3) → ℝ :=
    olsObservationTestError
  have hHae : H =ᵐ[ν] fun D =>
      @looRiskL1 0 0 (n + 1) gaussianObservationLaw
        gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
        olsNoiseAbsoluteLoss (olsNoiseFittedLoss_integrable hn3) D -
        looEstimate (n := n + 1) (olsNoiseEstimator (n + 1))
          olsNoiseAbsoluteLoss D := by
    change (fun D : Dataset (Observation 1 1) (n + 3) =>
      olsObservationTestError D) =ᵐ[
        gaussianObservationSampleLaw (n + 3)] _
    have hbridge := olsNoiseError_eq_frozenRisk_sub_loo_ae hn3
    filter_upwards [hbridge] with D hD
    have hcoords : olsNoiseObservationSampleCoordinates D =
        olsObservationToPairSample D := rfl
    change olsTestError (olsObservationToPairSample D) = _
    rw [hcoords] at hD
    exact hD
  have hM₂ : Integrable observationNormSq gaussianObservationLaw :=
    gaussianObservationLaw_observationNormSq_integrable
  have hB : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg _
  have hδ : 0 ≤ bias n := by
    simp only [bias, olsObservationBiasEnvelope]
    positivity
  have hLKpos : 0 < LK := by
    dsimp [LK]
    positivity
  have hLK : 0 ≤ LK := hLKpos.le
  have hHmeas : Measurable H := by
    exact measurable_olsObservationTestError (n := n)
  have hHnorm :
      eLpNorm H 2 ν ≤ ENNReal.ofReal (Real.sqrt 12) := by
    simpa [H] using olsObservationTestError_eLpNorm_two_le_sqrt_twelve hn3
  have hHmean : |∫ D, H D ∂ν| ≤ bias n := by
    simpa [H, bias, olsObservationBiasEnvelope] using
      abs_integral_olsObservationTestError_gaussian_le_bias hn3
  have hHlip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E) := by
    intro D hD E hE
    have hpair := olsObservationTestError_pairwise_bound hnsize D E hD hE
    change |olsObservationTestError D - olsObservationTestError E| ≤
      36007 * datasetNorm (D - E) / Real.sqrt (n + 3 : ℝ) at hpair
    calc
      |H D - H E| ≤ 36007 * datasetNorm (D - E) /
          Real.sqrt (n + 3 : ℝ) := by simpa [H] using hpair
      _ = LK * datasetNorm (D - E) := by dsimp [LK]; ring
  have hD₀ : D₀ ∈ K := by
    exact olsObservationReferencePoint_mem_olsObservationGoodSet hnsize
  have hKmeas : MeasurableSet K :=
    measurableSet_olsObservationGoodSet n
  have hKne : K.Nonempty := olsObservationGoodSet_nonempty hnsize
  letI : IsProbabilityMeasure gaussianObservationLaw :=
    gaussianObservationLaw_isProbability
  have hDC := @LOOConcentration.dataDependentConcentration
    0 0 (n + 1) gaussianObservationLaw (by infer_instance) 1 hLSI hM₂
    olsNoiseEstimator olsNoiseAbsoluteLoss
    (olsNoiseFittedLoss_integrable hn3) H hHae
    (Real.sqrt 12) (bias n) LK hB hδ hLK K hKmeas hKne D₀ hD₀
  have hTail := hDC hHmeas hHnorm hHmean hHlip
  have hApply := (hTail (eps / 2) (by linarith)).1
  let η : ℝ := Real.sqrt (ν.real Kᶜ) *
    (Real.sqrt 12 + |H D₀| + LK *
      (Real.sqrt ((((n + 1 : ℕ) : ℝ) + 2) *
        (∫ z : Observation 1 1,
          observationNormSq z ∂gaussianObservationLaw)) + datasetNorm D₀))
  change ν.real {D | |H D| > bias n + η + eps / 2} ≤ _ at hApply
  have hEta : η = olsObservationGoodSetPenalty n := by
    simp only [η, ν, K, D₀, H, LK, olsObservationGoodSetPenalty,
      olsObservationGoodSetBadMass]
    rw [gaussianObservationLaw_M2]
    rw [show ((n + 1 : ℕ) : ℝ) + 2 = (n + 3 : ℝ) by push_cast; ring]
  have hApply' := hApply
  rw [hEta] at hApply'
  have hThreshold : bias n + olsObservationGoodSetPenalty n + eps / 2 ≤ eps := by
    linarith
  have hEvent : {D : Dataset (Observation 1 1) (n + 3) |
        |H D| > eps} ⊆
      {D | |H D| > bias n + olsObservationGoodSetPenalty n + eps / 2} := by
    intro D hD
    exact lt_of_le_of_lt hThreshold hD
  have hScalar := olsObservationScalarTailBound_le
    (eps := eps) hnsize
  have hNoiseBound : ν.real {D | |H D| > eps} ≤
      6 * (n + 3 : ℝ) *
        Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := by
    calc
      ν.real {D | |H D| > eps} ≤
          ν.real {D | |H D| > bias n +
            olsObservationGoodSetPenalty n + eps / 2} :=
        measureReal_mono hEvent
      _ ≤ olsObservationScalarTailBound eps n := by
        simpa [ν, K, D₀, H, LK, bias, olsObservationBiasEnvelope,
          olsObservationGoodSetPenalty, olsObservationGoodSetBadMass,
          olsObservationScalarTailBound,
          gaussianObservationLaw_M2, hLKpos.ne', Nat.add_assoc,
          gaussianObservationSampleLaw] using hApply'
      _ ≤ 6 * (n + 3 : ℝ) *
          Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := hScalar
  simpa [H, ν] using hNoiseBound

/-- Source-shaped response-law OLS concentration, conditional only on the
single Gaussian `HasLogSobolev` predecessor. The constants are chosen before
`α` and `β`, and the exact sample size remains `n + 3`. -/
theorem olsConcentration_of_hasLogSobolev
    (hLSI : @HasLogSobolev 0 0 gaussianObservationLaw
      gaussianObservationLaw_isProbability 1) :
    ∀ (eps : ℝ) (_heps : 0 < eps),
      ∃ Cε cε : ℝ, 0 < Cε ∧ 0 < cε ∧
      ∃ Nε : ℕ, ∀ (α β : ℝ) (n : ℕ), Nε ≤ n + 3 →
        (olsAffineResponseLaw (n + 3) α β).real
          {D : Fin (n + 3) → ℝ × ℝ |
            |olsResponseError α β D| > eps} ≤
          Cε * (n + 3 : ℝ) * Real.exp (-(cε * (n + 3 : ℝ))) := by
  intro eps _heps
  obtain ⟨N₀, hN₀⟩ := olsObservationErrorTail_of_hasLogSobolev hLSI eps _heps
  let Nbase : ℕ := max N₀ 189
  refine ⟨6, olsObservationTailRate eps, by norm_num,
    olsObservationTailRate_pos _heps, Nbase + 3, ?_⟩
  intro α β n hN
  have hNbase : Nbase ≤ n := by omega
  have hN₀le : N₀ ≤ Nbase := Nat.le_max_left N₀ 189
  have h189le : 189 ≤ Nbase := Nat.le_max_right N₀ 189
  have hn : N₀ ≤ n := le_trans hN₀le hNbase
  have hnlarge : 189 ≤ n := le_trans h189le hNbase
  have hn3 : 3 ≤ n := by omega
  have hnoise := hN₀ n hn
  have htransport := olsResponseErrorTailProbability_eq_noise
    (n := n) hn3 α β eps
  have hcoords := olsObservationErrorTailProbability_eq_pair (n := n) eps
  calc
    (olsAffineResponseLaw (n + 3) α β).real
        {D : Fin (n + 3) → ℝ × ℝ |
          |olsResponseError α β D| > eps} =
      (gaussianObservationSampleLaw (n + 3)).real
        {D : Dataset (Observation 1 1) (n + 3) |
          |olsObservationTestError D| > eps} := by
        rw [htransport, hcoords]
    _ ≤ 6 * (n + 3 : ℝ) *
        Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := hnoise
    _ = 6 * (n + 3 : ℝ) *
        Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := rfl

#print axioms olsObservationErrorTail_of_hasLogSobolev
#print axioms olsConcentration_of_hasLogSobolev

end LOOConcentration
