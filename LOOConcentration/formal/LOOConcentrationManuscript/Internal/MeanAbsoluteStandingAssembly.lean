import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanAbsoluteLossLipschitz
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanAbsoluteLossDeleteBias
import LOOConcentrationManuscript.Internal.MeanQuadraticIntegrability
import LOOConcentrationManuscript.Internal.MeanQuadraticObservationIntegrability
import LOOConcentrationManuscript.Internal.ScalarObservationLSITransportConsumer
import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransportConsumer
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

private theorem sfinite_of_sigmaFinite {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : SFinite μ := by
  infer_instance

private def absoluteMeanResponseProjection (r : ℕ) :
    EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (r + 1)) where
  toFun D := WithLp.toLp 2 (fun i => D (i, Sum.inr (0 : Fin 1)))
  map_add' D E := by
    ext i
    rfl
  map_smul' c D := by
    ext i
    rfl

private theorem absoluteMeanResponseProjection_apply (r : ℕ)
    (D : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1)))
    (i : Fin (r + 1)) :
    (absoluteMeanResponseProjection r D) i = D (i, Sum.inr 0) := rfl

private theorem absoluteMeanResponseProjection_norm_le (r : ℕ)
    (D : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1))) :
    ‖absoluteMeanResponseProjection r D‖ ≤ ‖D‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [absoluteMeanResponseProjection_apply, Real.norm_eq_abs, sq_abs]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type]
  exact Finset.sum_le_sum fun i _ =>
    le_add_of_nonneg_left (sq_nonneg (D (i, Sum.inl 0)))

private noncomputable def absoluteMeanResponseProjectionCLM (r : ℕ) :
    EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (r + 1)) :=
  LinearMap.toContinuousLinearMap (absoluteMeanResponseProjection r)

private theorem absoluteMeanResponseProjection_opNorm_le (r : ℕ) :
    ‖absoluteMeanResponseProjectionCLM r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro D
  calc
    ‖absoluteMeanResponseProjectionCLM r D‖ ≤ ‖D‖ := by
      exact absoluteMeanResponseProjection_norm_le r D
    _ = 1 * ‖D‖ := by ring

private theorem empiricalMean_absoluteLoss_actualDataset_lipschitz
    (r : ℕ) (z : ℝ) :
    LipschitzWith (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (fun D : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
          abs (empiricalMean r (WithLp.toLp 2
            (fun i => (LOOConcentration.Revision.datasetOfEuclidean D i).2 0)) - z)) := by
  let S := absoluteMeanResponseProjectionCLM r
  have hS : LipschitzWith 1 S := by
    apply LipschitzWith.of_dist_le_mul
    intro D E
    rw [dist_eq_norm, dist_eq_norm]
    change ‖S (D - E)‖ ≤ 1 * ‖D - E‖
    calc
      ‖S (D - E)‖ ≤ ‖S‖ * ‖D - E‖ := S.le_opNorm _
      _ ≤ 1 * ‖D - E‖ := by
        exact mul_le_mul_of_nonneg_right (absoluteMeanResponseProjection_opNorm_le r)
          (norm_nonneg _)
  have h :=
    (LOOConcentration.Manuscript.empiricalMean_absoluteLoss_lipschitz r z).comp hS
  simpa [S, absoluteMeanResponseProjectionCLM,
    absoluteMeanResponseProjection, LOOConcentration.Revision.datasetOfEuclidean,
    Function.comp_def] using h

private theorem absoluteResponse_memLp_two
    (ν : Measure (LOOConcentration.Observation 1 1))
    (hSecond : Integrable LOOConcentration.observationNormSq ν) :
    MemLp (fun z : LOOConcentration.Observation 1 1 => z.2 0) 2 ν := by
  have hSquare : Integrable
      (fun z : LOOConcentration.Observation 1 1 => (z.2 0) ^ 2) ν :=
    hSecond.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [LOOConcentration.observationNormSq, Fin.sum_univ_one]
      exact le_add_of_nonneg_left (sq_nonneg _))
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hSquare

private theorem empiricalMean_absolute_actualObservation_integrability_bias
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (n : ℕ) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    (∀ z : LOOConcentration.Observation 1 1,
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 1) =>
          LOOConcentration.fittedLoss (T n) L D z)
        (Measure.pi fun _ : Fin (n + 1) => ν)) ∧
    (∀ i : Fin (n + 2),
      Integrable
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) =>
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => ν)) ∧
    (Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
          LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => ν).prod ν) ∧
    (∀ i : Fin (n + 2),
      |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2),
          LOOConcentration.fittedLoss (T n) L
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi fun _ : Fin (n + 2) => ν) -
        (∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
            LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
            ∂((Measure.pi fun _ : Fin (n + 2) => ν).prod ν))| ≤
        2 * (∫ x : ℝ, |x| ∂μ) / (n + 1 : ℝ))) := by
  classical
  intro φ ν T L
  have hφ : Measurable φ := by fun_prop
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hνSecond := (scalarObservation_sample_and_fresh_test_transport
    μ hSecond true 0).2.1
  have hResponseLp := absoluteResponse_memLp_two ν hνSecond
  let Pν (r : ℕ) := Measure.pi (fun _ : Fin (r + 1) => ν)
  have hCoordLaw (r : ℕ) (i : Fin (r + 1)) :
      IdentDistrib (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 => D i)
        (id : LOOConcentration.Observation 1 1 → LOOConcentration.Observation 1 1)
        (Pν r) ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [Pν] using
      (Measure.pi_map_eval (μ := fun _ : Fin (r + 1) => ν) i)
  have hResponseCoordLp (r : ℕ) (i : Fin (r + 1)) :
      MemLp (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 => (D i).2 0)
        2 (Pν r) := by
    have hLaw := (hCoordLaw r i).comp (u := fun z => (z.2 0)) (by fun_prop)
    simpa only [Function.comp_def, id_eq] using hLaw.memLp_iff.mpr hResponseLp
  refine ⟨?_, ?_⟩
  · intro z
    have hMeanLp := empiricalMean_memLp_two_of_coordinates (Pν n) n
      (fun i D => (D i).2 0) (fun i => hResponseCoordLp n i)
    have hContrastLp : MemLp
        ((fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
          empiricalMean n (WithLp.toLp 2 (fun i => (D i).2 0))) -
          (fun _ => z.2 0)) 2 (Pν n) :=
      hMeanLp.sub (memLp_const (z.2 0))
    change Integrable (fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
      abs (empiricalMean n (WithLp.toLp 2 (fun i => (D i).2 0)) - z.2 0)) (Pν n)
    exact (hContrastLp.integrable one_le_two).abs
  · refine ⟨?_, ?_⟩
    · intro i
      have hDelMeanLp := empiricalMean_memLp_two_of_coordinates (Pν (n + 1)) n
        (fun j D => (D (i.succAbove j)).2 0)
        (fun j => hResponseCoordLp (n + 1) (i.succAbove j))
      have hDelContrastLp : MemLp
          ((fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
            empiricalMean n (WithLp.toLp 2
              (fun j => (D (i.succAbove j)).2 0))) -
            (fun D => (D i).2 0)) 2 (Pν (n + 1)) :=
        hDelMeanLp.sub (hResponseCoordLp (n + 1) i)
      change Integrable (fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
        abs (empiricalMean n (WithLp.toLp 2 (fun j => (D (i.succAbove j)).2 0)) -
          (D i).2 0)) (Pν (n + 1))
      exact (hDelContrastLp.integrable one_le_two).abs
    · let Pμ : Measure (Fin (n + 3) → ℝ) := Measure.pi (fun _ => μ)
      let Pνn : Measure (Fin (n + 2) → LOOConcentration.Observation 1 1) :=
        Measure.pi fun _ => ν
      let PairMap : (Fin (n + 3) → ℝ) →
          ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
            LOOConcentration.Observation 1 1) := fun a =>
        ((fun i => φ (a i.castSucc)), φ (a (Fin.last (n + 2))))
      let del (i : Fin (n + 2)) :
          (Fin (n + 2) → LOOConcentration.Observation 1 1) → ℝ := fun D =>
        LOOConcentration.fittedLoss (T n) L
          (LOOConcentration.deleteAt D i) (D i)
      let delPair (i : Fin (n + 2)) :
          ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
            LOOConcentration.Observation 1 1) → ℝ := fun p => del i p.1
      let full : ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) → ℝ := fun p =>
        LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
      have hLaw : ∀ j : Fin (n + 3),
          IdentDistrib (fun a : Fin (n + 3) → ℝ => a j) (id : ℝ → ℝ) Pμ μ := by
        intro j
        refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
        simpa [Pμ] using (Measure.pi_map_eval (μ := fun _ : Fin (n + 3) => μ) j)
      have hInd : iIndepFun
          (fun j : Fin (n + 3) => fun a : Fin (n + 3) → ℝ => a j) Pμ :=
        iIndepFun_pi (X := fun _ : Fin (n + 3) => id) (fun _ => aemeasurable_id)
      have hIdLp : MemLp (id : ℝ → ℝ) 2 μ :=
        (memLp_two_iff_integrable_sq (measurable_id.aestronglyMeasurable)).2 hSecond
      have hCoordLp : ∀ j : Fin (n + 3),
          MemLp (fun a : Fin (n + 3) → ℝ => a j) 2 Pμ := by
        intro j
        exact (hLaw j).memLp_iff.mpr hIdLp
      have hFullMeanLp := empiricalMean_memLp_two_of_coordinates Pμ (n + 1)
        (fun j a => a j.castSucc) (fun j => hCoordLp j.castSucc)
      have hFullContrastLp : MemLp
          ((fun a : Fin (n + 3) → ℝ =>
            empiricalMean (n + 1) (WithLp.toLp 2
              (fun j : Fin (n + 2) => a j.castSucc))) -
            (fun a => a (Fin.last (n + 2)))) 2 Pμ :=
        hFullMeanLp.sub (hCoordLp (Fin.last (n + 2)))
      have hFullScalarInt : Integrable
          (fun a : Fin (n + 3) → ℝ => abs
            (empiricalMean (n + 1) (WithLp.toLp 2
              (fun j : Fin (n + 2) => a j.castSucc)) - a (Fin.last (n + 2)))) Pμ := by
        exact (hFullContrastLp.integrable one_le_two).abs
      have hpair : Pμ.map PairMap = Pνn.prod ν := by
        simpa only [Pμ, Pνn, PairMap, φ] using
          (meanQuadratic_observation_product_laws μ hSecond).2 n
      have hPairMap : Measurable PairMap := by
        dsimp [PairMap]
        fun_prop
      have hfullMeas : Measurable full := by
        change Measurable (fun p : ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
            LOOConcentration.Observation 1 1) =>
          |empiricalMean (n + 1) (WithLp.toLp 2
            (fun j : Fin (n + 2) => (p.1 j).2 0)) - p.2.2 0|)
        fun_prop [empiricalMean]
      have hfullMeasMap : AEStronglyMeasurable full (Pμ.map PairMap) := by
        rw [hpair]
        exact hfullMeas.aestronglyMeasurable
      have hfullPair : Integrable full (Pνn.prod ν) := by
        rw [← hpair]
        apply (integrable_map_measure hfullMeasMap hPairMap.aemeasurable).2
        change Integrable
          (fun a : Fin (n + 3) → ℝ =>
            |empiricalMean (n + 1) (WithLp.toLp 2
              (fun j : Fin (n + 2) => a j.castSucc)) - a (Fin.last (n + 2))|) Pμ
        exact hFullScalarInt
      have hfullPairMap : Integrable full (Pμ.map PairMap) := by
        rw [hpair]
        exact hfullPair
      have hfullId (a : Fin (n + 3) → ℝ) :
          full (PairMap a) =
            |empiricalMean (n + 1) (WithLp.toLp 2
              (fun j : Fin (n + 2) => a j.castSucc)) - a (Fin.last (n + 2))| := by
        simp [full, PairMap, LOOConcentration.fittedLoss, T, L, φ,
          ContinuousMap.const_apply]
      have hνfinite : IsFiniteMeasure ν := ⟨by
        rw [IsProbabilityMeasure.measure_univ]
        exact ENNReal.one_lt_top⟩
      have hνsigma : SigmaFinite ν := @IsFiniteMeasure.toSigmaFinite _ _ ν hνfinite
      have hνsfinite : SFinite ν := @sfinite_of_sigmaFinite _ _ ν hνsigma
      have hPνsfinite : SFinite Pνn := by
        have hPνProb : IsProbabilityMeasure Pνn := by infer_instance
        have hPνfinite : IsFiniteMeasure Pνn := ⟨by
          rw [hPνProb.measure_univ]
          exact ENNReal.one_lt_top⟩
        have hPνsigma : SigmaFinite Pνn :=
          @IsFiniteMeasure.toSigmaFinite _ _ Pνn hPνfinite
        exact @sfinite_of_sigmaFinite _ _ Pνn hPνsigma
      have hfullTransport :
          (∫ p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
              LOOConcentration.Observation 1 1, full p ∂(Pνn.prod ν)) =
            ∫ a : Fin (n + 3) → ℝ,
              |empiricalMean (n + 1) (WithLp.toLp 2
                (fun j : Fin (n + 2) => a j.castSucc)) - a (Fin.last (n + 2))| ∂Pμ := by
        calc
          _ = ∫ a, full (PairMap a) ∂Pμ := by
            rw [← hpair]
            exact integral_map hPairMap.aemeasurable hfullPairMap.aestronglyMeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards [] with a
            exact hfullId a
      refine ⟨hfullPair, ?_⟩
      intro i
      have hDelMeanLp := empiricalMean_memLp_two_of_coordinates Pμ n
        (fun j a => a ((i.succAbove j).castSucc))
        (fun j => hCoordLp ((i.succAbove j).castSucc))
      have hDelContrastLp : MemLp
          ((fun a : Fin (n + 3) → ℝ =>
            empiricalMean n (WithLp.toLp 2
              (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc)))) -
            (fun a => a i.castSucc)) 2 Pμ :=
        hDelMeanLp.sub (hCoordLp i.castSucc)
      have hDelScalarInt : Integrable
          (fun a : Fin (n + 3) → ℝ => abs
            (empiricalMean n (WithLp.toLp 2
              (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) - a i.castSucc)) Pμ := by
        exact (hDelContrastLp.integrable one_le_two).abs
      have hdelMeas (i : Fin (n + 2)) : Measurable (delPair i) := by
        change Measurable (fun p : ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
            LOOConcentration.Observation 1 1) =>
          |empiricalMean n (WithLp.toLp 2
            (fun j => (p.1 (i.succAbove j)).2 0)) - (p.1 i).2 0|)
        fun_prop [empiricalMean]
      have hdelMeasMap :
          AEStronglyMeasurable (delPair i) (Pμ.map PairMap) := by
        rw [hpair]
        exact (hdelMeas i).aestronglyMeasurable
      have hdelPair : Integrable (delPair i) (Pνn.prod ν) := by
        rw [← hpair]
        apply (integrable_map_measure hdelMeasMap hPairMap.aemeasurable).2
        change Integrable
          (fun a : Fin (n + 3) → ℝ =>
            |empiricalMean n (WithLp.toLp 2
              (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) - a i.castSucc|) Pμ
        exact hDelScalarInt
      have hdelPairMap : Integrable (delPair i) (Pμ.map PairMap) := by
        rw [hpair]
        exact hdelPair
      have hdelId (a : Fin (n + 3) → ℝ) :
          delPair i (PairMap a) =
            |empiricalMean n (WithLp.toLp 2
              (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) - a i.castSucc| := by
        simp [delPair, del, PairMap, LOOConcentration.fittedLoss, T, L, φ,
          LOOConcentration.deleteAt, ContinuousMap.const_apply]
      have hdelTransport :
          (∫ D : Fin (n + 2) → LOOConcentration.Observation 1 1,
            del i D ∂Pνn) =
            ∫ a : Fin (n + 3) → ℝ,
              |empiricalMean n (WithLp.toLp 2
                (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) - a i.castSucc| ∂Pμ := by
        calc
          _ = ∫ p, delPair i p ∂(Pνn.prod ν) := by
            symm
            rw [@integral_fun_fst _ _ ℝ _ _ Pνn ν _ hνsfinite _ hPνsfinite
              (fun D => del i D)]
            simp [del]
          _ = ∫ a, delPair i (PairMap a) ∂Pμ := by
            rw [← hpair]
            exact integral_map hPairMap.aemeasurable hdelPairMap.aestronglyMeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards [] with a
            exact hdelId a
      rw [hdelTransport, hfullTransport]
      exact LOOConcentration.Manuscript.empiricalMean_absoluteLoss_delete_bias
        Pμ μ hSecond n (fun j a => a j) hLaw hInd i

/-- The literal response-only empirical mean with source absolute loss satisfies
all Standing fields at every sample index, with the source-rate constants. -/
theorem empiricalMean_absoluteStanding_of_scalarLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (n : ℕ) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    let δ₁ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 =>
      (Real.sqrt (N : ℝ))⁻¹
    let δ₂ := fun _N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (0 : ℝ)
    let δ₃ := fun N : ℕ =>
      2 * (∫ x : ℝ, |x| ∂μ) / ((N : ℝ) - 1)
    LOOConcentration.Revision.StandingAssumption (n := n) ν T L δ₁ δ₂ δ₃ 1 0 := by
  classical
  intro φ ν
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro T L δ₁ δ₂ δ₃
  have hLSI : LOOConcentration.Revision.observationLogSobolevConstant ν < ⊤ :=
    lt_of_le_of_lt (scalarResponseObservation_nativeConstant_le μ) hFinite
  have hMoment := scalarObservation_sample_and_fresh_test_transport μ hSecond true 0
  have hActual := empiricalMean_absolute_actualObservation_integrability_bias μ hSecond n
  have hAbs := (iidResponse_full_and_deleted_absolute_mean ν hMoment.2.1).1
  have hm : 0 ≤ ∫ x : ℝ, |x| ∂μ := integral_nonneg (fun x => abs_nonneg x)
  have hN₁ : Tendsto (fun r : ℕ => (r : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hN₁
  have hsqrt := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN₁)
  have hδ₃_eq : (fun r : ℕ => δ₃ (r + 2)) =
      (fun r : ℕ => 2 * (∫ x : ℝ, |x| ∂μ) / ((r : ℝ) + 1)) := by
    funext r
    simp only [δ₃, Nat.cast_add, Nat.cast_ofNat]
    ring
  have hStable : LOOConcentration.Revision.Stable ν hLSI T L δ₁ δ₂ δ₃ := by
    refine {
      measurable_loss := ?_
      delta₁_nonneg := ?_
      delta₂_nonneg := ?_
      delta₃_nonneg := ?_
      delta₁_tendsto := ?_
      delta₂_tendsto := ?_
      delta₃_tendsto := ?_
      locallyLipschitz_loss := ?_
      gradient_loss := ?_
      integrable_deleted := ?_
      integrable_full := ?_
      bias := ?_ }
    · intro r
      change Measurable (fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
        |empiricalMean r (WithLp.toLp 2 (fun i => (p.1 i).2 0)) - p.2.2 0|)
      fun_prop [empiricalMean]
    · intro r z
      simp only [δ₁]
      positivity
    · intro r z
      simp only [δ₂]
      norm_num
    · intro r
      simp only [δ₃]
      have hden : 0 < ((r + 2 : ℕ) : ℝ) - 1 := by
        have heq : ((r + 2 : ℕ) : ℝ) - 1 = (r : ℝ) + 1 := by
          push_cast
          ring
        rw [heq]
        positivity
      exact div_nonneg (mul_nonneg (by norm_num) hm) hden.le
    · filter_upwards [] with z
      simpa only [δ₁, one_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using hsqrt
    · filter_upwards [] with z
      simp only [δ₂]
      exact tendsto_const_nhds
    · simpa only [hδ₃_eq] using
        (tendsto_const_nhds.div_atTop hN₁)
    · intro r
      filter_upwards [] with z
      have hLip := empiricalMean_absoluteLoss_actualDataset_lipschitz r (z.2 0)
      simpa [LOOConcentration.fittedLoss, T, L, LOOConcentration.Revision.datasetOfEuclidean,
        ContinuousMap.const_apply] using hLip.locallyLipschitz
    · intro r
      filter_upwards [] with z
      have hLip := empiricalMean_absoluteLoss_actualDataset_lipschitz r (z.2 0)
      have hLocal : LocallyLipschitz (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
            LOOConcentration.fittedLoss (T r) L
              (LOOConcentration.Revision.datasetOfEuclidean x) z) := by
        simpa [LOOConcentration.fittedLoss, T, L,
          LOOConcentration.Revision.datasetOfEuclidean, ContinuousMap.const_apply] using
            hLip.locallyLipschitz
      have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean
        _ hLocal
      filter_upwards [hAE] with x hx
      refine ⟨hx, ?_⟩
      have hNorm : ‖gradient (fun y : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
            LOOConcentration.fittedLoss (T r) L
              (LOOConcentration.Revision.datasetOfEuclidean y) z) x‖ =
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
              LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean y) z) x‖ := by
        rw [gradient]
        exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
      rw [hNorm]
      have hK : (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : ℝ) =
          (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
        simp
      calc
        ‖fderiv ℝ (fun y : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
              LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean y) z) x‖ ≤
            (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : ℝ) :=
          norm_fderiv_le_of_lipschitz ℝ hLip
        _ = δ₁ (r + 1) z := by simp only [δ₁, hK]
        _ = δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖ := by simp [δ₂]
    · intro r i
      have hFields := empiricalMean_absolute_actualObservation_integrability_bias μ hSecond r
      simpa [LOOConcentration.fittedLoss, T, L,
        LOOConcentration.deleteAt, LOOConcentration.Revision.datasetOfEuclidean,
        ContinuousMap.const_apply] using hFields.2.1 i
    · intro r
      have hFields := empiricalMean_absolute_actualObservation_integrability_bias μ hSecond r
      simpa [LOOConcentration.fittedLoss, T, L,
        LOOConcentration.Revision.datasetOfEuclidean, ContinuousMap.const_apply] using
        hFields.2.2.1
    · intro r i
      have hBias := (empiricalMean_absolute_actualObservation_integrability_bias μ hSecond r).2.2.2 i
      have hden : ((r + 2 : ℕ) : ℝ) - 1 = (r : ℝ) + 1 := by
        push_cast
        ring
      change |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2),
          LOOConcentration.fittedLoss (T r) L
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi fun _ : Fin (r + 2) => ν) -
        (∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2) ×
            LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss (T (r + 1)) L p.1 p.2
            ∂(Measure.pi fun _ : Fin (r + 2) => ν).prod ν)| ≤
        2 * (∫ x : ℝ, |x| ∂μ) / (((r + 2 : ℕ) : ℝ) - 1)
      rw [hden]
      simpa only [LOOConcentration.fittedLoss, T, L, φ,
        ContinuousMap.const_apply] using hBias
  have hRates :
      Integrable (δ₁ (n + 1)) ν ∧ Integrable (δ₂ (n + 1)) ν ∧
      Integrable (δ₁ (n + 2)) ν ∧ Integrable (δ₂ (n + 2)) ν := by
    have hConst (c : ℝ) : Integrable (fun _ : LOOConcentration.Observation 1 1 => c) ν :=
      integrable_const c
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [δ₁] using hConst ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
    · simpa only [δ₂] using hConst 0
    · simpa only [δ₁, Nat.cast_add, Nat.cast_ofNat] using
        hConst ((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹)
    · simpa only [δ₂] using hConst 0
  have hZero (r : ℕ) : Integrable
      (fun z : LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T r) L 0 z) ν := by
    have h := hAbs
    change Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) ν at h
    simpa [LOOConcentration.fittedLoss, T, L, empiricalMean,
      ContinuousMap.const_apply] using h
  have hMean : ∀ z : LOOConcentration.Observation 1 1,
      Integrable (fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T n) L D z)
        (Measure.pi fun _ : Fin (n + 1) => ν) := hActual.1
  have hQueryLip : LipschitzWith 1 (fun z : ℝ =>
      ∫ D : Fin (n + 1) → LOOConcentration.Observation 1 1,
        |empiricalMean n (WithLp.toLp 2 (fun i => (D i).2 0)) - z|
          ∂Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    let P := Measure.pi (fun _ : Fin (n + 1) => ν)
    have hPProb : IsProbabilityMeasure P := by infer_instance
    let f := fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
      empiricalMean n (WithLp.toLp 2 (fun i => (D i).2 0))
    have hLossInt (q : ℝ) : Integrable (fun D => |f D - q|) P := by
      change Integrable
        (fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T n) L D
            (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => q)) :
              LOOConcentration.Observation 1 1)) P
      exact hMean (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => q)) :
        LOOConcentration.Observation 1 1)
    have hSub := integral_sub (hLossInt z) (hLossInt w)
    rw [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs]
    change |(∫ D, |f D - z| ∂P) - (∫ D, |f D - w| ∂P)| ≤
      (1 : ℝ) * |z - w|
    rw [one_mul]
    rw [← hSub]
    have hBound : ∀ᵐ D ∂P, ‖|f D - z| - |f D - w|‖ ≤ |z - w| := by
      filter_upwards with D
      change |(|f D - z| - |f D - w|)| ≤ |z - w|
      have hh := abs_abs_sub_abs_le_abs_sub (f D - z) (f D - w)
      have heq : (f D - z) - (f D - w) = -(z - w) := by ring
      simpa only [heq, abs_neg] using hh
    have hUniv : P.real Set.univ = 1 := by simp [P]
    have hIntegral := norm_integral_le_of_norm_le_const hBound
    rw [hUniv, mul_one] at hIntegral
    simpa only [Real.norm_eq_abs] using hIntegral
  have hMeanLip : LipschitzWith 1 (fun x : EuclideanSpace ℝ
      (LOOConcentration.ObservationCoordinate 1 1) =>
        LOOConcentration.Revision.meanFittedLoss ν (T n) L
          (LOOConcentration.Revision.observationOfEuclidean x)
          (hMean (LOOConcentration.Revision.observationOfEuclidean x))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    let z := x (Sum.inr (0 : Fin 1))
    let w := y (Sum.inr (0 : Fin 1))
    have hxy := hQueryLip.dist_le_mul z w
    have hcoord : |z - w| ≤ ‖x - y‖ := by
      change |x (Sum.inr (0 : Fin 1)) - y (Sum.inr (0 : Fin 1))| ≤ ‖x - y‖
      simpa only [Real.norm_eq_abs, WithLp.ofLp_sub, Pi.sub_apply] using
        (PiLp.norm_apply_le (x - y) (Sum.inr (0 : Fin 1)))
    have hG (q : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1)) :
        LOOConcentration.Revision.meanFittedLoss ν (T n) L
            (LOOConcentration.Revision.observationOfEuclidean q)
            (hMean (LOOConcentration.Revision.observationOfEuclidean q)) =
          ∫ D : Fin (n + 1) → LOOConcentration.Observation 1 1,
            |empiricalMean n (WithLp.toLp 2 (fun i => (D i).2 0)) -
              q (Sum.inr (0 : Fin 1))| ∂Measure.pi (fun _ => ν) := by
      rfl
    rw [hG x, hG y]
    change |(∫ D, |empiricalMean n (WithLp.toLp 2
        (fun i => (D i).2 0)) - z| ∂Measure.pi (fun _ => ν)) -
      (∫ D, |empiricalMean n (WithLp.toLp 2
        (fun i => (D i).2 0)) - w| ∂Measure.pi (fun _ => ν))| ≤
      (1 : ℝ) * ‖x - y‖
    rw [one_mul]
    have hxy' : |(∫ D, |empiricalMean n (WithLp.toLp 2
        (fun i => (D i).2 0)) - z| ∂Measure.pi (fun _ => ν)) -
        (∫ D, |empiricalMean n (WithLp.toLp 2
        (fun i => (D i).2 0)) - w| ∂Measure.pi (fun _ => ν))| ≤ |z - w| := by
      calc
        _ ≤ ((1 : NNReal) : ℝ) * |z - w| := by
          simpa only [Real.dist_eq] using hxy
        _ = |z - w| := by norm_num
    exact hxy'.trans hcoord
  refine {
    lsi := hLSI
    second_moment := hMoment.2.1
    stable := hStable
    delta₁_deleted_integrable := hRates.1
    delta₂_deleted_integrable := hRates.2.1
    delta₁_full_integrable := hRates.2.2.1
    delta₂_full_integrable := hRates.2.2.2
    zero_deleted_integrable := hZero n
    zero_full_integrable := hZero (n + 1)
    c_nonneg := by norm_num
    d_nonneg := by norm_num
    mean_integrable := hMean
    mean_locallyLipschitz := hMeanLip.locallyLipschitz
    mean_gradient := ?_ }
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean
    _ hMeanLip.locallyLipschitz
  filter_upwards [hAE] with x hx
  refine ⟨hx, ?_⟩
  have hNorm : ‖gradient (fun y : EuclideanSpace ℝ
      (LOOConcentration.ObservationCoordinate 1 1) =>
        LOOConcentration.Revision.meanFittedLoss ν (T n) L
          (LOOConcentration.Revision.observationOfEuclidean y)
          (hMean (LOOConcentration.Revision.observationOfEuclidean y))) x‖ =
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ
        (LOOConcentration.ObservationCoordinate 1 1) =>
          LOOConcentration.Revision.meanFittedLoss ν (T n) L
            (LOOConcentration.Revision.observationOfEuclidean y)
            (hMean (LOOConcentration.Revision.observationOfEuclidean y))) x‖ := by
    rw [gradient]
    exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
  rw [hNorm]
  have hGrad := norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hMeanLip
  calc
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
        LOOConcentration.Revision.meanFittedLoss ν (T n) L
          (LOOConcentration.Revision.observationOfEuclidean y)
          (hMean (LOOConcentration.Revision.observationOfEuclidean y))) x‖ ≤ 1 := hGrad
    _ = 1 + 0 * ‖x‖ := by simp

end LOOConcentration.Manuscript.Internal
