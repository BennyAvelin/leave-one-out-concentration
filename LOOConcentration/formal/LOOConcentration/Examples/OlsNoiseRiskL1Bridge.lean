import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.OlsNoiseEstimator
import LOOConcentration.Examples.OlsRandomNoiseMoment
import LOOConcentration.Examples.GaussianObservationTransport
import LOOConcentration.Frozen.Probability.LooRiskL1Characterization
import LOOConcentration.Frozen.Probability.LooRiskL1Unique
import LOOConcentration.Probability.ProductConditionalRisk

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

local instance : IsProbabilityMeasure gaussianObservationLaw :=
  gaussianObservationLaw_isProbability

local instance (N : ℕ) :
    IsProbabilityMeasure (gaussianObservationSampleLaw N) :=
  gaussianObservationSampleLaw_isProbability N

/-- Decode a frozen observation sample coordinate by coordinate. -/
noncomputable def olsNoiseObservationSampleCoordinates {N : ℕ}
    (D : Dataset (Observation 1 1) N) : Fin N → ℝ × ℝ :=
  fun i => gaussianPairObservationCLE.symm (D i)

/-- Encode an independent noise pair in the frozen observation carrier. -/
noncomputable def olsNoisePairTestEncode (z : ℝ × ℝ) : Observation 1 1 :=
  gaussianPairObservationCLE z

/-- The sample/test coordinate encoder used for the actual noise law. -/
noncomputable def olsNoiseSampleTestEncode (N : ℕ) :
    (Fin N → ℝ × ℝ) × (ℝ × ℝ) →
      (Dataset (Observation 1 1) N) × Observation 1 1 :=
  fun p => (gaussianObservationSampleMap N p.1,
    olsNoisePairTestEncode p.2)

theorem olsNoiseObservation_eq_gaussianPairObservationCLE (z : ℝ × ℝ) :
    olsNoiseObservation z = gaussianPairObservationCLE z := by
  ext i <;> simp [olsNoiseObservation, gaussianPairObservationCLE_apply]

theorem olsNoiseObservationCoordinates_eq_symm (z : Observation 1 1) :
    olsNoiseObservationCoordinates z = gaussianPairObservationCLE.symm z := by
  ext
  · change z.1 _ = z.1 0
    congr 1
  · change z.2 _ = z.2 0
    congr 1

theorem olsNoiseObservations_eq_gaussianObservationSampleMap {N : ℕ}
    (G : Fin N → ℝ × ℝ) :
    olsNoiseObservations G = gaussianObservationSampleMap N G := by
  funext i
  exact olsNoiseObservation_eq_gaussianPairObservationCLE (G i)

theorem olsNoiseObservationTestLaw_eq_gaussianObservationLaw :
    olsNoiseObservationTestLaw = gaussianObservationLaw := by
  change olsTestLaw.map olsNoiseObservation =
    gaussianObservationPairLaw.map gaussianPairObservationCLE
  rw [show olsTestLaw = gaussianObservationPairLaw by rfl]
  congr 1

theorem olsPairGaussianLaw_eq_gaussianObservationPairSampleLaw (N : ℕ) :
    olsPairGaussianLaw N = gaussianObservationPairSampleLaw N := by
  rfl

theorem olsNoiseObservations_map_law (N : ℕ) :
    Measure.map (olsNoiseObservations : (Fin N → ℝ × ℝ) →
      Dataset (Observation 1 1) N) (olsPairGaussianLaw N) =
        gaussianObservationSampleLaw N := by
  calc
    _ = Measure.map (gaussianObservationSampleMap N) (olsPairGaussianLaw N) := by
      congr 1
    _ = gaussianObservationSampleLaw N := by
      rw [olsPairGaussianLaw_eq_gaussianObservationPairSampleLaw]
      exact gaussianObservationSampleLaw_eq_map N

theorem olsNoiseSampleTestEncode_map_law (N : ℕ) :
    Measure.map (olsNoiseSampleTestEncode N)
      ((olsPairGaussianLaw N).prod olsTestLaw) =
        (gaussianObservationSampleLaw N).prod gaussianObservationLaw := by
  have hsampleMeas : Measurable (olsNoiseObservations : (Fin N → ℝ × ℝ) →
      Dataset (Observation 1 1) N) := by
    rw [show olsNoiseObservations = gaussianObservationSampleMap N by
      funext G
      exact olsNoiseObservations_eq_gaussianObservationSampleMap G]
    exact gaussianObservationSampleMap_measurable N
  have hencode : olsNoiseSampleTestEncode N =
      Prod.map olsNoiseObservations olsNoiseObservation := by
    funext p
    exact Prod.ext (by
      funext i
      exact olsNoiseObservation_eq_gaussianPairObservationCLE (p.1 i))
      (olsNoiseObservation_eq_gaussianPairObservationCLE p.2)
  calc
    _ = Measure.map (Prod.map olsNoiseObservations olsNoiseObservation)
        ((olsPairGaussianLaw N).prod olsTestLaw) := by rw [hencode]
    _ = (Measure.map olsNoiseObservations (olsPairGaussianLaw N)).prod
        (Measure.map olsNoiseObservation olsTestLaw) := by
          symm
          exact Measure.map_prod_map _ _ hsampleMeas measurable_olsNoiseObservation
    _ = (gaussianObservationSampleLaw N).prod gaussianObservationLaw := by
          rw [olsNoiseObservations_map_law]
          exact congrArg (fun μ : Measure (Observation 1 1) =>
            (gaussianObservationSampleLaw N).prod μ)
            olsNoiseObservationTestLaw_eq_gaussianObservationLaw

private theorem olsNoiseEstimator_measurable_predictor {N : ℕ} :
    Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ =>
      olsNoisePredictor p.1 p.2) := by
  have he : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsEBar p.1) :=
    measurable_olsEBar.comp measurable_fst
  have hs : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsNoiseSlope p.1) :=
    measurable_olsNoiseSlope.comp measurable_fst
  have hx : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsXBar p.1) :=
    measurable_olsXBar.comp measurable_fst
  unfold olsNoisePredictor
  exact he.add (hs.mul (measurable_snd.sub hx))

private theorem olsNoiseRiskLoss_measurable {N : ℕ} :
    Measurable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      olsRiskLoss p.1 p.2) := by
  have hp : Measurable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      olsNoisePredictor p.1 p.2.1) :=
    olsNoiseEstimator_measurable_predictor.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  unfold olsRiskLoss
  exact measurable_abs.comp (measurable_snd.comp measurable_snd |>.sub hp)

private theorem olsTestGaussian_id_memLp (p : ℝ≥0) :
    MemLp (id : ℝ → ℝ) p olsTestGaussian := by
  exact ProbabilityTheory.memLp_id_gaussianReal p

private theorem olsTestGaussian_abs_integrable :
    Integrable (fun x : ℝ => |x|) standardGaussian := by
  have hid : Integrable (id : ℝ → ℝ) olsTestGaussian := by
    exact (olsTestGaussian_id_memLp 1).integrable (by norm_num)
  simpa only [Real.norm_eq_abs, id_eq] using hid.abs

private noncomputable def olsNoiseRiskLossAssoc {N : ℕ} :
    ((Fin N → ℝ × ℝ) × ℝ) × ℝ → ℝ :=
  fun p => |p.2 - olsNoisePredictor p.1.1 p.1.2|

private theorem olsNoiseRiskLossAssoc_measurable {N : ℕ} :
    Measurable (olsNoiseRiskLossAssoc (N := N)) := by
  have hp : Measurable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ =>
        olsNoisePredictor p.1.1 p.1.2) :=
    olsNoiseEstimator_measurable_predictor.comp
      (measurable_fst.comp measurable_fst |>.prodMk (measurable_snd.comp measurable_fst))
  unfold olsNoiseRiskLossAssoc
  exact measurable_abs.comp (measurable_snd.sub hp)

/-- The actual full sample/test noise loss is integrable under the pair law. -/
theorem integrable_olsRiskLoss_sampleTest {N : ℕ} (hN : 3 < N) :
    Integrable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      olsRiskLoss p.1 p.2) ((olsPairGaussianLaw N).prod olsTestLaw) := by
  let μ₀ : Measure ((Fin N → ℝ × ℝ) × ℝ) :=
    (olsPairGaussianLaw N).prod standardGaussian
  let μ₁ : Measure (((Fin N → ℝ × ℝ) × ℝ) × ℝ) :=
    μ₀.prod standardGaussian
  have hpredSq : Integrable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ =>
        (olsNoisePredictor p.1.1 p.1.2) ^ 2) μ₁ := by
    have hbase := integrable_olsNoisePredictor_sq_gaussian (N := N) hN
    have hfst := (measurePreserving_fst
      (μ := μ₀) (ν := standardGaussian)).integrable_comp_of_integrable hbase
    simpa [μ₀, μ₁, Function.comp_def] using hfst
  have hpredMajor : Integrable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ =>
        1 + (olsNoisePredictor p.1.1 p.1.2) ^ 2) μ₁ := by
    exact (integrable_const 1).add hpredSq
  have hpredAbs : Integrable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ =>
        |olsNoisePredictor p.1.1 p.1.2|) μ₁ := by
    apply hpredMajor.mono' (by
      exact (olsNoiseEstimator_measurable_predictor.comp
        (measurable_fst.comp measurable_fst |>.prodMk
          (measurable_snd.comp measurable_fst))).abs.aestronglyMeasurable)
    filter_upwards with p
    have hbound : |olsNoisePredictor p.1.1 p.1.2| ≤
        1 + (olsNoisePredictor p.1.1 p.1.2) ^ 2 := by
      nlinarith [sq_nonneg (|olsNoisePredictor p.1.1 p.1.2| - (1 / 2 : ℝ)),
        sq_abs (olsNoisePredictor p.1.1 p.1.2)]
    simpa only [Real.norm_eq_abs, abs_abs] using hbound
  have hnoise : Integrable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ => |p.2|) μ₁ := by
    have hbase := olsTestGaussian_abs_integrable.comp_snd μ₀
    simpa [μ₀, μ₁] using hbase
  have hlossMajor : Integrable
      (fun p : ((Fin N → ℝ × ℝ) × ℝ) × ℝ =>
        |p.2| + |olsNoisePredictor p.1.1 p.1.2|) μ₁ :=
    hnoise.add hpredAbs
  have hlossAssoc : Integrable (olsNoiseRiskLossAssoc (N := N)) μ₁ := by
    apply hlossMajor.mono' (olsNoiseRiskLossAssoc_measurable.aestronglyMeasurable)
    filter_upwards with p
    simpa only [olsNoiseRiskLossAssoc, Real.norm_eq_abs, abs_abs] using
      (abs_sub p.2 (olsNoisePredictor p.1.1 p.1.2))
  have hAssoc : MeasurePreserving MeasurableEquiv.prodAssoc μ₁
      ((olsPairGaussianLaw N).prod olsTestLaw) := by
    simpa [μ₀, μ₁, olsTestLaw, olsTestGaussian] using
      (measurePreserving_prodAssoc (olsPairGaussianLaw N)
        standardGaussian standardGaussian)
  have hcomp : (olsNoiseRiskLossAssoc (N := N) ∘
      MeasurableEquiv.prodAssoc.symm) =
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2) := by
    funext p
    rcases p with ⟨G, ⟨x, e⟩⟩
    rfl
  have htransport := hAssoc.symm.integrable_comp_of_integrable hlossAssoc
  rw [hcomp] at htransport
  exact htransport

/-- The sample encoder has the literal coordinatewise inverse on observation
samples. -/
theorem olsNoiseObservations_decode {N : ℕ}
    (D : Dataset (Observation 1 1) N) :
    olsNoiseObservations (olsNoiseObservationSampleCoordinates D) = D := by
  funext i
  change olsNoiseObservation (gaussianPairObservationCLE.symm (D i)) = D i
  rw [olsNoiseObservation_eq_gaussianPairObservationCLE]
  change gaussianPairObservationCLE
    (gaussianPairObservationCLE.symm (D i)) = D i
  exact gaussianPairObservationCLE.apply_symm_apply (D i)

theorem olsNoiseObservationSampleCoordinates_encode {N : ℕ}
    (G : Fin N → ℝ × ℝ) :
    olsNoiseObservationSampleCoordinates (gaussianObservationSampleMap N G) = G := by
  funext i
  change olsNoiseObservationCoordinates
    (gaussianPairObservationCLE (G i)) = G i
  rw [olsNoiseObservationCoordinates_eq_symm]
  exact gaussianPairObservationCLE.symm_apply_apply (G i)

/-- Exact frozen fitted loss formula after decoding observation coordinates. -/
theorem olsNoiseFittedLoss_formula {n : ℕ}
    (D : Dataset (Observation 1 1) (n + 3)) (z : Observation 1 1) :
    fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss D z =
      olsRiskLoss (olsNoiseObservationSampleCoordinates D)
        (gaussianPairObservationCLE.symm z) := by
  rw [← olsNoiseObservations_decode D]
  change olsNoiseEstimatorTestLoss (n := n + 1)
    (olsNoiseObservationSampleCoordinates D) z = _
  rw [olsNoiseEstimatorTestLoss_formula]
  change |(olsNoiseObservationCoordinates z).2 -
      olsNoisePredictor (olsNoiseObservationSampleCoordinates D)
        (olsNoiseObservationCoordinates z).1| = _
  rw [olsNoiseObservationCoordinates_eq_symm]
  rfl

private theorem measurable_olsNoiseObservationSampleCoordinates {N : ℕ} :
    Measurable (olsNoiseObservationSampleCoordinates :
      Dataset (Observation 1 1) N → Fin N → ℝ × ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  exact gaussianPairObservationCLE_symm_measurable.comp
    (continuous_apply i).measurable

private theorem measurable_olsNoiseFittedLoss {n : ℕ} :
    Measurable (fun p : Dataset (Observation 1 1) (n + 3) × Observation 1 1 =>
      fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss p.1 p.2) := by
  have hargs : Measurable (fun p :
      Dataset (Observation 1 1) (n + 3) × Observation 1 1 =>
        (olsNoiseObservationSampleCoordinates p.1,
          gaussianPairObservationCLE.symm p.2)) := by
    exact (measurable_olsNoiseObservationSampleCoordinates.comp measurable_fst).prodMk
      (gaussianPairObservationCLE_symm_measurable.comp measurable_snd)
  have hcomp := olsNoiseRiskLoss_measurable.comp hargs
  convert hcomp using 1
  funext p
  exact olsNoiseFittedLoss_formula p.1 p.2

private theorem measurable_olsNoiseSampleTestEncode (N : ℕ) :
    Measurable (olsNoiseSampleTestEncode N) := by
  change Measurable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
    (gaussianObservationSampleMap N p.1, gaussianPairObservationCLE p.2))
  exact ((gaussianObservationSampleMap_measurable N).comp measurable_fst).prodMk
    (gaussianPairObservationCLE_measurable.comp measurable_snd)

/-- Global fitted-loss integrability on the actual transported iid observation
sample and independent test law. -/
theorem olsNoiseFittedLoss_integrable {n : ℕ} (hn : 3 ≤ n) :
    Integrable
      (fun p : Dataset (Observation 1 1) (n + 3) × Observation 1 1 =>
        fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss p.1 p.2)
      ((gaussianObservationSampleLaw (n + 3)).prod gaussianObservationLaw) := by
  let N : ℕ := n + 3
  have hN : 3 < N := by dsimp [N]; omega
  have hsource := integrable_olsRiskLoss_sampleTest (N := N) hN
  have hcomp : Integrable
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
        fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss
          (olsNoiseSampleTestEncode N p).1 (olsNoiseSampleTestEncode N p).2)
      ((olsPairGaussianLaw N).prod olsTestLaw) := by
    have heq : (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
        fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss
          (olsNoiseSampleTestEncode N p).1 (olsNoiseSampleTestEncode N p).2) =
        fun p => olsRiskLoss p.1 p.2 := by
      funext p
      rw [olsNoiseFittedLoss_formula]
      change olsRiskLoss
        (olsNoiseObservationSampleCoordinates (gaussianObservationSampleMap N p.1))
        (gaussianPairObservationCLE.symm (gaussianPairObservationCLE p.2)) = _
      rw [olsNoiseObservationSampleCoordinates_encode]
      simp
    rw [heq]
    exact hsource
  have hmap := (integrable_map_measure
      (f := olsNoiseSampleTestEncode N)
      (g := fun p : Dataset (Observation 1 1) (n + 3) × Observation 1 1 =>
        fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss p.1 p.2)
      (measurable_olsNoiseFittedLoss.aestronglyMeasurable)
      (measurable_olsNoiseSampleTestEncode N).aemeasurable).2 hcomp
  rw [olsNoiseSampleTestEncode_map_law N] at hmap
  simpa [N] using hmap

/-- Every frozen observation section integrates to the actual Gaussian noise
test risk of the decoded sample. -/
theorem olsNoiseFittedLoss_section_integral {n : ℕ}
    (D : Dataset (Observation 1 1) (n + 3)) :
    (∫ z : Observation 1 1,
      fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss D z
        ∂gaussianObservationLaw) =
      olsTestRisk (olsNoiseObservationSampleCoordinates D) := by
  rw [← olsNoiseObservations_decode D]
  rw [← olsNoiseObservationTestLaw_eq_gaussianObservationLaw]
  change (∫ z, olsNoiseEstimatorTestLoss
      (n := n + 1) (olsNoiseObservationSampleCoordinates D) z
        ∂olsNoiseObservationTestLaw) = _
  exact integral_olsNoiseEstimatorTestLoss_eq_olsTestRisk
    (olsNoiseObservationSampleCoordinates D)

private theorem olsNoiseTestRisk_decode_integrable {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun D : Dataset (Observation 1 1) (n + 3) =>
      olsTestRisk (olsNoiseObservationSampleCoordinates D))
      (gaussianObservationSampleLaw (n + 3)) := by
  have hsections := (olsNoiseFittedLoss_integrable hn).integral_prod_left
  apply hsections.congr
  exact ae_of_all _ fun D => by
    simpa only [Prod.fst, Prod.snd] using olsNoiseFittedLoss_section_integral D

/-- The actual noise pair risk is the frozen conditional-risk representative
almost everywhere under the encoded iid sample law. -/
theorem olsNoiseRiskL1Characterization_ae {n : ℕ} (hn : 3 ≤ n) :
    (∀ᵐ D ∂gaussianObservationSampleLaw (n + 3),
      olsTestRisk (olsNoiseObservationSampleCoordinates D) =
        @looRiskL1 0 0 (n + 1) gaussianObservationLaw
          gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
          olsNoiseAbsoluteLoss (olsNoiseFittedLoss_integrable hn) D) ∧
    ((gaussianObservationSampleLaw (n + 3)).prod gaussianObservationLaw)[
      (fun p : Dataset (Observation 1 1) (n + 3) × Observation 1 1 =>
        fittedLoss (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          (gaussianObservationSampleLaw (n + 3)).prod gaussianObservationLaw]
      fun p => @looRiskL1 0 0 (n + 1) gaussianObservationLaw
        gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
        olsNoiseAbsoluteLoss (olsNoiseFittedLoss_integrable hn) p.1 := by
  let ν := gaussianObservationSampleLaw (n + 3)
  let μ := gaussianObservationLaw
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using gaussianObservationSampleLaw_isProbability (n + 3)
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using gaussianObservationLaw_isProbability
  let f : Dataset (Observation 1 1) (n + 3) × Observation 1 1 → ℝ :=
    fun p => fittedLoss (olsNoiseEstimator (n + 2))
      olsNoiseAbsoluteLoss p.1 p.2
  have hf : Integrable f (ν.prod μ) := olsNoiseFittedLoss_integrable hn
  have hRiskInt : Integrable
      (fun D : Dataset (Observation 1 1) (n + 3) =>
        olsTestRisk (olsNoiseObservationSampleCoordinates D)) ν :=
    olsNoiseTestRisk_decode_integrable hn
  let R : Dataset (Observation 1 1) (n + 3) →₁[ν] ℝ :=
    hRiskInt.toL1 (fun D => olsTestRisk
      (olsNoiseObservationSampleCoordinates D))
  have hRco : (fun D => R D) =ᵐ[ν]
      (fun D => olsTestRisk (olsNoiseObservationSampleCoordinates D)) :=
    hRiskInt.coeFn_toL1
  have hsections : (fun D : Dataset (Observation 1 1) (n + 3) =>
      ∫ z, f (D, z) ∂μ) =ᵐ[ν]
      (fun D => olsTestRisk (olsNoiseObservationSampleCoordinates D)) := by
    filter_upwards with D
    simpa [f, μ] using olsNoiseFittedLoss_section_integral D
  have hRsections : (fun D => R D) =ᵐ[ν]
      (fun D => ∫ z, f (D, z) ∂μ) := hRco.trans hsections.symm
  have hsource := condExp_fst_prod_eq_integral_test_of_integrable ν μ f hf
  have hRpair :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae_eq_comp hRsections
  have hcondR : (ν.prod μ)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      ν.prod μ] fun p => R p.1 := by
    exact hsource.trans (by
      simpa only [Function.comp_def] using hRpair.symm)
  have hunique := @looRiskL1_unique 0 0 (n + 1) μ
    gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
    olsNoiseAbsoluteLoss hf R hcondR
  have hchar := @looRiskL1_characterization 0 0 (n + 1) μ
    gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
    olsNoiseAbsoluteLoss hf
  have hRiskEq : (fun D : Dataset (Observation 1 1) (n + 3) =>
      olsTestRisk (olsNoiseObservationSampleCoordinates D)) =ᵐ[ν]
      (fun D => @looRiskL1 0 0 (n + 1) μ gaussianObservationLaw_isProbability
        (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss hf D) := by
    have hpoint : ∀ D, R D =
        @looRiskL1 0 0 (n + 1) μ gaussianObservationLaw_isProbability
          (olsNoiseEstimator (n + 2)) olsNoiseAbsoluteLoss hf D := by
      intro D
      exact congrArg (fun Q : Dataset (Observation 1 1) (n + 3) →₁[ν] ℝ => Q D)
        hunique
    exact hRco.symm.trans (ae_of_all _ hpoint)
  exact ⟨hRiskEq, by
    simpa [ν, μ, f, gaussianObservationSampleLaw, Nat.add_assoc] using hchar⟩

/-- Exact a.e. identification of the source generalization error with the
frozen conditional risk minus the pointwise frozen leave-one-out estimate. -/
theorem olsNoiseError_eq_frozenRisk_sub_loo_ae {n : ℕ} (hn : 3 ≤ n) :
    ∀ᵐ D ∂gaussianObservationSampleLaw (n + 3),
      olsTestError (n := n + 1)
        (olsNoiseObservationSampleCoordinates D) =
        @looRiskL1 0 0 (n + 1) gaussianObservationLaw
          gaussianObservationLaw_isProbability (olsNoiseEstimator (n + 2))
          olsNoiseAbsoluteLoss (olsNoiseFittedLoss_integrable hn) D -
          looEstimate (n := n + 1) (olsNoiseEstimator (n + 1))
            olsNoiseAbsoluteLoss D := by
  have hRisk := (olsNoiseRiskL1Characterization_ae hn).1
  have hEmp : ∀ D : Dataset (Observation 1 1) (n + 3),
      looEstimate (n := n + 1) (olsNoiseEstimator (n + 1))
          olsNoiseAbsoluteLoss D =
        olsValidationError (olsNoiseObservationSampleCoordinates D) := by
    intro D
    rw [← olsNoiseObservations_decode D]
    exact looEstimate_olsNoiseEstimator_eq_olsValidationError
      (olsNoiseObservationSampleCoordinates D)
  filter_upwards [hRisk] with D hD
  simp only [olsTestError]
  rw [hD, ← hEmp D]

#print axioms integrable_olsRiskLoss_sampleTest
#print axioms olsNoiseSampleTestEncode_map_law
#print axioms olsNoiseFittedLoss_integrable
#print axioms olsNoiseRiskL1Characterization_ae
#print axioms olsNoiseError_eq_frozenRisk_sub_loo_ae

end LOOConcentration
