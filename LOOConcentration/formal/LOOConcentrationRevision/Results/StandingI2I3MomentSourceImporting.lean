import LOOConcentrationRevision.Results.StandingI2I3MomentSource
import LOOConcentrationRevision.Probability.DatasetCarrierTransport

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

theorem standingValidationAverage_eq_standingV
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ) (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) :
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt D =
      standingV μ T L δ₁ δ₂ δ₃ c d hSt D := by
  have hden : (n + 2 : ℝ) ≠ 0 := by positivity
  simp only [standingValidationAverage, standingV]
  field_simp [hden]

/-- Actual I2 under the original ordered product law, with no surrogate
function or analytic proof-step premise. -/
theorem standingI2_original_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ) (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun D : Dataset (Observation k m) (n + 2) =>
      standingI2 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI2 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingI2 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI2 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ)
      (ENNReal.ofReal p) (Measure.pi fun _ : Fin (n + 2) => μ) ≤
      ENNReal.ofReal
        (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
          (c / Real.sqrt (n + 2 : ℝ) +
            d / (n + 2 : ℝ) * Real.sqrt ((n + 2 : ℝ) *
              ∫ z, observationNormSq z ∂μ +
                (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let law := datasetLawOfObservation (r := n + 2) μ
  let I2 := standingI2 μ T L δ₁ δ₂ δ₃ c d hSt
  let F := standingValidationAverageFullEuclidean μ T L δ₁ δ₂ δ₃ c d hSt
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hI2int := (standingThreeErrors_integrable μ T L δ₁ δ₂ δ₃ c d hSt).2.1
  have hVint := hparts.2.1
  have hmeanI2 : ∫ D, I2 D ∂ν = 0 := by
    change ∫ D, standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
      standingV μ T L δ₁ δ₂ δ₃ c d hSt D ∂ν = 0
    rw [integral_sub (integrable_const _) hVint]
    simp [standingEV]
  have hmeanF : ∫ x, F x ∂law = standingEV μ T L δ₁ δ₂ δ₃ c d hSt := by
    have hmap := integral_datasetFunction_datasetLaw_eq μ
      (standingV μ T L δ₁ δ₂ δ₃ c d hSt) hVint
    calc
      _ = ∫ x, standingV μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) ∂law := by
        apply integral_congr_ae
        filter_upwards with x
        exact standingValidationAverage_eq_standingV μ T L δ₁ δ₂ δ₃ c d hSt _
      _ = ∫ D, standingV μ T L δ₁ δ₂ δ₃ c d hSt D ∂ν := by simpa [law, ν] using hmap
      _ = standingEV μ T L δ₁ δ₂ δ₃ c d hSt := rfl
  have hpoint : ∀ x, I2 (datasetOfEuclidean x) =
      -(F x - ∫ y, F y ∂law) := by
    intro x
    rw [hmeanF]
    change standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
      standingV μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) =
      -(standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
        standingEV μ T L δ₁ δ₂ δ₃ c d hSt)
    rw [← standingValidationAverage_eq_standingV μ T L δ₁ δ₂ δ₃ c d hSt]
    ring_nf
  have hmoment := standing_validation_average_actual_centered_moment
    μ T L δ₁ δ₂ δ₃ c d hSt hp
  have hI2memLaw : MemLp (fun x => I2 (datasetOfEuclidean x))
      (ENNReal.ofReal p) law := by
    have heq : (fun x => I2 (datasetOfEuclidean x)) =ᵐ[law]
        (fun x => -(F x - ∫ y, F y ∂law)) := Filter.Eventually.of_forall hpoint
    exact (memLp_congr_ae heq).2 hmoment.1.neg
  have hI2mem := (memLp_datasetFunction_datasetLaw_iff μ I2 (ENNReal.ofReal p)).mp hI2memLaw
  have hI2normTransport := centered_eLpNorm_datasetFunction_datasetLaw_eq μ I2 hI2int
    (ENNReal.ofReal p)
  have hI2meanLaw : ∫ x, I2 (datasetOfEuclidean x) ∂law = 0 := by
    rw [integral_datasetFunction_datasetLaw_eq μ I2 hI2int, hmeanI2]
  have hI2normLaw : eLpNorm (fun x => I2 (datasetOfEuclidean x) -
      ∫ y, I2 (datasetOfEuclidean y) ∂law) (ENNReal.ofReal p) law =
      eLpNorm (fun x => F x - ∫ y, F y ∂law) (ENNReal.ofReal p) law := by
    have heq : (fun x => I2 (datasetOfEuclidean x) -
      ∫ y, I2 (datasetOfEuclidean y) ∂law) =ᵐ[law]
        (fun x => -(F x - ∫ y, F y ∂law)) := by
      filter_upwards with x
      rw [hI2meanLaw, hpoint x]
      simp
    calc
      _ = eLpNorm (fun x => -(F x - ∫ y, F y ∂law)) (ENNReal.ofReal p) law :=
        eLpNorm_congr_ae heq
      _ = eLpNorm (fun x => F x - ∫ y, F y ∂law) (ENNReal.ofReal p) law :=
        eLpNorm_neg _ _ _
  have hI2norm := hI2normTransport.symm.trans hI2normLaw
  have hI2memCentered : MemLp (fun D => I2 D - ∫ E, I2 E ∂ν)
      (ENNReal.ofReal p) ν := by
    have hcenter : (fun D => I2 D - ∫ E, I2 E ∂ν) = I2 := by
      funext D
      simp [hmeanI2]
    simpa only [hcenter] using hI2mem
  refine ⟨hI2memCentered, ?_⟩
  simpa only [I2, hmeanI2] using hI2norm ▸ hmoment.2

/-- Actual I3 under the original ordered product law. Its representative is
the literal expected full-fit loss, and its risk carrier is the same frozen
`looRiskL1` built from `hSt.stable.integrable_full n`. -/
theorem standingI3_original_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ) (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun D : Dataset (Observation k m) (n + 2) =>
      standingI3 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI3 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingI3 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI3 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ)
      (ENNReal.ofReal p) (Measure.pi fun _ : Fin (n + 2) => μ) ≤
      ENNReal.ofReal
        (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
          ((∫ z, δ₁ (n + 2) z ∂μ) +
            (∫ z, δ₂ (n + 2) z ∂μ) * Real.sqrt ((n + 2 : ℝ) *
              ∫ z, observationNormSq z ∂μ +
                (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let law := datasetLawOfObservation (r := n + 2) μ
  let I3 := standingI3 μ T L δ₁ δ₂ δ₃ c d hSt
  let F := expectedFullRiskEuclidean (n := n) μ T L
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    ∫ z, fittedLoss (T (n + 1)) L D z ∂μ
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hI3int := (standingThreeErrors_integrable μ T L δ₁ δ₂ δ₃ c d hSt).2.2
  have hRint : Integrable R ν := by
    simpa [R, ν] using (hSt.stable.integrable_full n).integral_prod_left
  have hRiskRep : (fun D => standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D) =ᵐ[ν] R := by
    have hchar := looRiskL1_characterization μ (T (n + 1)) L
      (hSt.stable.integrable_full n)
    have hsource := LOOConcentration.condExp_fst_prod_eq_integral_test_of_integrable
      ν μ (fun q : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss (T (n + 1)) L q.1 q.2) (hSt.stable.integrable_full n)
    have hp := Measure.ae_ae_of_ae_prod (hchar.symm.trans hsource)
    filter_upwards [hp] with D hD
    obtain ⟨z, hz⟩ := hD.exists
    exact hz
  have hRepInt := integral_datasetFunction_datasetLaw_eq μ R hRint
  have hRiskMean : ∫ D, R D ∂ν = standingER μ T L δ₁ δ₂ δ₃ c d hSt := by
    calc
      _ = ∫ D, standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D ∂ν :=
        integral_congr_ae hRiskRep.symm
      _ = standingER μ T L δ₁ δ₂ δ₃ c d hSt := rfl
  have hMeanF : ∫ x, F x ∂law = standingER μ T L δ₁ δ₂ δ₃ c d hSt := by
    calc
      _ = ∫ D, R D ∂ν := by
        calc
          _ = ∫ x, R (datasetOfEuclidean x) ∂law := by
            apply integral_congr_ae
            filter_upwards with x
            rfl
          _ = ∫ D, R D ∂ν := by simpa [law, ν] using hRepInt
      _ = standingER μ T L δ₁ δ₂ δ₃ c d hSt := hRiskMean
  have hsourceMeans : ∫ x, F x ∂law = ∫ D, R D ∂ν :=
    hMeanF.trans hRiskMean.symm
  have hI3ae : (fun D => I3 D) =ᵐ[ν]
      (fun D => R D - ∫ x, F x ∂law) := by
    filter_upwards [hRiskRep] with D hD
    change standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D -
      standingER μ T L δ₁ δ₂ δ₃ c d hSt = _
    rw [← hMeanF, hD]
  have hmoment := standing_expected_full_loss_actual_centered_moment
    μ T L δ₁ δ₂ δ₃ c d hSt hp
  have hRcenterMem : MemLp (fun D => R D - ∫ x, F x ∂law)
      (ENNReal.ofReal p) ν := by
    have htrans := memLp_datasetFunction_datasetLaw_iff μ
      (fun D : Dataset (Observation k m) (n + 2) => R D - ∫ x, F x ∂law)
      (ENNReal.ofReal p)
    have hEuclid : MemLp (fun x => R (datasetOfEuclidean x) - ∫ y, F y ∂law)
        (ENNReal.ofReal p) law := by
      simpa [R, F, expectedFullRiskEuclidean] using hmoment.1
    exact htrans.mp (by simpa [R, F] using hEuclid)
  have hI3mem : MemLp I3 (ENNReal.ofReal p) ν :=
    (memLp_congr_ae hI3ae).2 hRcenterMem
  have hmeanI3 : ∫ D, I3 D ∂ν = 0 := by
    change ∫ D, standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D -
      standingER μ T L δ₁ δ₂ δ₃ c d hSt ∂ν = 0
    rw [integral_sub hparts.1 (integrable_const _)]
    simp [standingER]
  have hI3normToRep :
      eLpNorm (fun D => I3 D - ∫ E, I3 E ∂ν) (ENNReal.ofReal p) ν =
        eLpNorm (fun D => R D - ∫ x, F x ∂law) (ENNReal.ofReal p) ν := by
    have heq : (fun D => I3 D - ∫ E, I3 E ∂ν) =ᵐ[ν]
        (fun D => R D - ∫ x, F x ∂law) := by
      filter_upwards [hI3ae] with D hD
      rw [hmeanI3]
      simpa using hD
    exact eLpNorm_congr_ae heq
  have hRepNormTransport := centered_eLpNorm_datasetFunction_datasetLaw_eq μ R hRint
    (ENNReal.ofReal p)
  have hRepNorm :
      eLpNorm (fun D => R D - ∫ x, F x ∂law) (ENNReal.ofReal p) ν =
        eLpNorm (fun x => F x - ∫ y, F y ∂law) (ENNReal.ofReal p) law := by
    have h := hRepNormTransport.symm
    calc
      _ = eLpNorm (fun D => R D - ∫ E, R E ∂ν) (ENNReal.ofReal p) ν := by
        apply eLpNorm_congr_ae
        filter_upwards with D
        rw [hsourceMeans]
      _ = eLpNorm (fun x => R (datasetOfEuclidean x) -
          ∫ y, R (datasetOfEuclidean y) ∂law) (ENNReal.ofReal p) law := h
      _ = eLpNorm (fun x => F x - ∫ y, F y ∂law) (ENNReal.ofReal p) law := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        simp [R, F, expectedFullRiskEuclidean]
  have hI3norm := hI3normToRep.trans hRepNorm
  have hI3memCentered : MemLp (fun D => I3 D - ∫ E, I3 E ∂ν)
      (ENNReal.ofReal p) ν := by
    have hcenter : (fun D => I3 D - ∫ E, I3 E ∂ν) = I3 := by
      funext D
      simp [hmeanI3]
    simpa only [hcenter] using hI3mem
  refine ⟨hI3memCentered, ?_⟩
  simpa only [I3, hmeanI3] using hI3norm ▸ hmoment.2

end LOOConcentration.Revision
