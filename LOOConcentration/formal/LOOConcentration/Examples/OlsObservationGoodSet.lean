import LOOConcentration.Examples.GaussianObservationTransport
import LOOConcentration.Examples.OlsGoodSetErrorLipschitz
import LOOConcentration.Examples.OlsGaussianTails
import LOOConcentration.Examples.OlsReferencePoint
import LOOConcentration.Examples.GaussianFirstMomentStrict
import LOOConcentration.Frozen.Norms.DatasetNorm
import LOOConcentration.Frozen.Norms.DatasetNormSq
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped ENNReal

private lemma olsObservation_sampleSize_real (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) + 2 = (n + 3 : ℝ) := by
  push_cast
  ring

/-!
# OLS good-set transport to the frozen observation carrier

The OLS pair sample is transported to `Dataset (Observation 1 1)` using the
coordinatewise inverse of `gaussianPairObservationCLE`.  The predicates and
error below are literal inverse-coordinate pullbacks on the full carrier.
-/

/-- Pull an observation sample back to its real-pair noise coordinates. -/
noncomputable def olsObservationToPairSample {N : ℕ}
    (D : Dataset (Observation 1 1) N) : Dataset (ℝ × ℝ) N :=
  fun i => gaussianPairObservationCLE.symm (D i)

/-- Push a pair sample to the frozen observation carrier. -/
noncomputable def olsPairToObservationSample {N : ℕ}
    (G : Dataset (ℝ × ℝ) N) : Dataset (Observation 1 1) N :=
  gaussianObservationSampleMap N G

@[simp]
theorem olsObservationToPairSample_pairToObservationSample {N : ℕ}
    (G : Dataset (ℝ × ℝ) N) :
    olsObservationToPairSample (olsPairToObservationSample G) = G := by
  funext i
  simp [olsObservationToPairSample, olsPairToObservationSample,
    gaussianObservationSampleMap]

@[simp]
theorem olsPairToObservationSample_observationToPairSample {N : ℕ}
    (D : Dataset (Observation 1 1) N) :
    olsPairToObservationSample (olsObservationToPairSample D) = D := by
  funext i
  apply Prod.ext
  · funext j
    fin_cases j
    simp [olsObservationToPairSample, olsPairToObservationSample,
      gaussianObservationSampleMap]
  · funext j
    fin_cases j
    simp [olsObservationToPairSample, olsPairToObservationSample,
      gaussianObservationSampleMap]

/-- The actual OLS good set on the full frozen observation sample carrier. -/
def olsObservationGoodSet (n : ℕ) :
    Set (Dataset (Observation 1 1) (n + 3)) :=
  {D | olsObservationToPairSample D ∈ olsGoodSet (n + 1)}

/-- The actual test error on the observation carrier, defined by inverse
coordinate pullback on every sample. -/
noncomputable def olsObservationTestError {n : ℕ}
    (D : Dataset (Observation 1 1) (n + 3)) : ℝ :=
  olsTestError (olsObservationToPairSample D)

theorem measurable_olsObservationToPairSample {N : ℕ} :
    Measurable (olsObservationToPairSample :
      Dataset (Observation 1 1) N → Dataset (ℝ × ℝ) N) := by
  apply measurable_pi_iff.mpr
  intro i
  exact gaussianPairObservationCLE_symm_measurable.comp (measurable_pi_apply i)

theorem measurableSet_olsObservationGoodSet (n : ℕ) :
    MeasurableSet (olsObservationGoodSet n) := by
  exact (measurableSet_olsGoodSet (n + 1)).preimage
    (measurable_olsObservationToPairSample (N := n + 3))

theorem measurable_olsObservationTestError {n : ℕ} :
    Measurable (olsObservationTestError :
      Dataset (Observation 1 1) (n + 3) → ℝ) := by
  exact (measurable_olsTestError (n := n + 1)).comp
    (measurable_olsObservationToPairSample (N := n + 3))

theorem observationNormSq_eq_gaussianPairNormSq_symm (z : Observation 1 1) :
    observationNormSq z =
      gaussianPairNormSq (gaussianPairObservationCLE.symm z) := by
  calc
    observationNormSq z = observationNormSq
        (gaussianPairObservationCLE (gaussianPairObservationCLE.symm z)) := by
      rw [gaussianPairObservationCLE.apply_symm_apply]
    _ = gaussianPairNormSq (gaussianPairObservationCLE.symm z) :=
      gaussianPairObservationCLE_observationNormSq _

/-- Exact squared-norm identity for every observation sample. -/
theorem olsObservation_datasetNormSq_eq_pairNormSq {N : ℕ}
    (D : Dataset (Observation 1 1) N) :
    datasetNormSq D = olsNoiseNormSq (olsObservationToPairSample D) := by
  unfold datasetNormSq olsNoiseNormSq
  apply Finset.sum_congr rfl
  intro i hi
  rw [observationNormSq_eq_gaussianPairNormSq_symm]
  rfl

/-- Exact Euclidean norm identity for every observation sample. -/
theorem olsObservation_datasetNorm_eq_pairNorm {N : ℕ}
    (D : Dataset (Observation 1 1) N) :
    datasetNorm D = olsNoiseNorm (olsObservationToPairSample D) := by
  unfold datasetNorm olsNoiseNorm
  rw [olsObservation_datasetNormSq_eq_pairNormSq]

theorem olsObservationToPairSample_sub {N : ℕ}
    (D D' : Dataset (Observation 1 1) N) :
    olsObservationToPairSample (D - D') =
      olsObservationToPairSample D - olsObservationToPairSample D' := by
  funext i
  exact gaussianPairObservationCLE.symm.map_sub (D i) (D' i)

/-- The pair-distance in the reviewed pair coordinates is exactly the frozen
dataset distance on observations. -/
theorem olsObservation_datasetNorm_sub_eq_pairDistance {N : ℕ}
    (D D' : Dataset (Observation 1 1) N) :
    datasetNorm (D - D') =
      olsPairDistance (olsObservationToPairSample D)
        (olsObservationToPairSample D') := by
  calc
    datasetNorm (D - D') =
        olsNoiseNorm (olsObservationToPairSample (D - D')) :=
      olsObservation_datasetNorm_eq_pairNorm (D - D')
    _ = olsNoiseNorm
        (olsObservationToPairSample D - olsObservationToPairSample D') := by
      rw [olsObservationToPairSample_sub]
    _ = olsPairDistance (olsObservationToPairSample D)
        (olsObservationToPairSample D') := rfl

/-- The reviewed pairwise bound transported to all pairs in the observation
good set, with the exact source constant. -/
theorem olsObservationTestError_pairwise_bound {n : ℕ}
    (hN : 192 ≤ n + 3)
    (D D' : Dataset (Observation 1 1) (n + 3))
    (hD : D ∈ olsObservationGoodSet n)
    (hD' : D' ∈ olsObservationGoodSet n) :
    |olsObservationTestError D - olsObservationTestError D'| ≤
      36007 * datasetNorm (D - D') / Real.sqrt (n + 3 : ℝ) := by
  change olsObservationToPairSample D ∈ olsGoodSet (n + 1) at hD
  change olsObservationToPairSample D' ∈ olsGoodSet (n + 1) at hD'
  have hpair := olsTestError_pairwise_bound (n := n + 1) (by omega)
    (olsObservationToPairSample D) (olsObservationToPairSample D')
    hD hD'
  rw [olsObservationTestError, olsObservationTestError]
  rw [← olsObservation_datasetNorm_sub_eq_pairDistance D D'] at hpair
  rw [olsObservation_sampleSize_real n] at hpair
  exact hpair

/-- The alternating-sign reference point on the frozen observation carrier. -/
noncomputable def olsObservationReferencePoint (n : ℕ) :
    Dataset (Observation 1 1) (n + 3) :=
  olsPairToObservationSample (olsReferencePoint (n + 1))

@[simp]
theorem olsObservationToPairSample_referencePoint (n : ℕ) :
    olsObservationToPairSample (olsObservationReferencePoint n) =
      olsReferencePoint (n + 1) := by
  simp [olsObservationReferencePoint]

theorem olsObservationReferencePoint_mem_olsObservationGoodSet {n : ℕ}
    (hN : 192 ≤ n + 3) :
    olsObservationReferencePoint n ∈ olsObservationGoodSet n := by
  change olsObservationToPairSample (olsObservationReferencePoint n) ∈
    olsGoodSet (n + 1)
  rw [olsObservationToPairSample_referencePoint]
  exact olsReferencePoint_mem_olsGoodSet (n := n + 1) (by omega)

theorem olsObservationGoodSet_nonempty {n : ℕ} (hN : 192 ≤ n + 3) :
    (olsObservationGoodSet n).Nonempty :=
  ⟨olsObservationReferencePoint n,
    olsObservationReferencePoint_mem_olsObservationGoodSet hN⟩

theorem olsObservationReferencePoint_norm (n : ℕ) :
    datasetNorm (olsObservationReferencePoint n) = Real.sqrt (n + 3 : ℝ) := by
  rw [olsObservation_datasetNorm_eq_pairNorm]
  rw [olsObservationToPairSample_referencePoint]
  have hnorm := olsReferencePoint_norm (n + 1)
  rw [olsObservation_sampleSize_real n] at hnorm
  exact hnorm

theorem olsObservationReferencePoint_testError_abs_lt_one (n : ℕ) :
    |olsObservationTestError (olsObservationReferencePoint n)| < 1 := by
  rw [olsObservationTestError, olsObservationToPairSample_referencePoint]
  exact olsReferencePoint_testError_abs_lt_one (n + 1)

/-- Transport the accepted OLS Gaussian complement tail to the actual finite
Pi law on frozen observations. -/
theorem measure_compl_olsObservationGoodSet_le {n : ℕ}
    (hN : 192 ≤ n + 3) :
    gaussianObservationSampleLaw (n + 3) (olsObservationGoodSet n)ᶜ ≤
      ENNReal.ofReal (4 * ((n + 3 : ℕ) : ℝ) *
        Real.exp (-((n + 3 : ℕ) : ℝ) / 128)) := by
  have hset : MeasurableSet (olsObservationGoodSet n)ᶜ :=
    (measurableSet_olsObservationGoodSet n).compl
  have hpre :
      gaussianObservationSampleMap (n + 3) ⁻¹' (olsObservationGoodSet n)ᶜ =
        (olsGoodSet (n + 1))ᶜ := by
    ext G
    change (olsObservationToPairSample
        (gaussianObservationSampleMap (n + 3) G) ∉ olsGoodSet (n + 1)) ↔
      G ∉ olsGoodSet (n + 1)
    rw [show olsObservationToPairSample
        (gaussianObservationSampleMap (n + 3) G) = G by
        funext i
        simp [olsObservationToPairSample, gaussianObservationSampleMap]]
  rw [← gaussianObservationSampleLaw_eq_map (n + 3)]
  rw [Measure.map_apply (gaussianObservationSampleMap_measurable (n + 3)) hset]
  rw [hpre]
  have htail := measure_compl_olsGoodSet_le (n := n + 1) (by omega)
  convert htail using 1
  · simp [gaussianObservationPairSampleLaw, gaussianObservationPairLaw,
      gaussianObservationCoordinateLaw, olsPairGaussianLaw, standardGaussian]

#print axioms olsObservationToPairSample_pairToObservationSample
#print axioms olsPairToObservationSample_observationToPairSample
#print axioms measurable_olsObservationToPairSample
#print axioms measurableSet_olsObservationGoodSet
#print axioms measurable_olsObservationTestError
#print axioms olsObservation_datasetNormSq_eq_pairNormSq
#print axioms olsObservation_datasetNorm_eq_pairNorm
#print axioms olsObservation_datasetNorm_sub_eq_pairDistance
#print axioms olsObservationTestError_pairwise_bound
#print axioms olsObservationReferencePoint_mem_olsObservationGoodSet
#print axioms olsObservationGoodSet_nonempty
#print axioms olsObservationReferencePoint_norm
#print axioms olsObservationReferencePoint_testError_abs_lt_one
#print axioms measure_compl_olsObservationGoodSet_le

end LOOConcentration
