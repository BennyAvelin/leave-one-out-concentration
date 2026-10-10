import LOOConcentrationManuscript.Internal.MeanQuadraticObservationIntegrability
import LOOConcentrationManuscript.Internal.MeanQuadraticIntegrabilityConsumer
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem sfinite_of_sigmaFinite {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : SFinite μ := by
  infer_instance

/-- The empirical-mean quadratic obligations on the literal response-only
observation law, including the held-out/full-fit bias transport. -/
theorem empiricalMean_actualObservation_quadratic_integrability_bias
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => (y 0 - y' 0) ^ 2
    (∀ r : ℕ, ∀ z : LOOConcentration.Observation 1 1,
      Integrable
        (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L D z)
        (Measure.pi fun _ : Fin (r + 1) => ν) ∧
      (∫ D : Fin (r + 1) → LOOConcentration.Observation 1 1,
        LOOConcentration.fittedLoss (T r) L D z
          ∂Measure.pi fun _ : Fin (r + 1) => ν) =
        (z.2 0 - ∫ x : ℝ, x ∂μ) ^ 2 +
          variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)) ∧
    (∀ n : ℕ,
      (∀ i : Fin (n + 2),
        Integrable
          (fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
            LOOConcentration.fittedLoss (T n) L
              (LOOConcentration.deleteAt D i) (D i))
          (Measure.pi fun _ : Fin (n + 2) => ν)) ∧
      Integrable
        (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
            LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2)
        ((Measure.pi fun _ : Fin (n + 2) => ν).prod ν) ∧
      (∀ i : Fin (n + 2),
        |(∫ D : Fin (n + 2) → LOOConcentration.Observation 1 1,
            LOOConcentration.fittedLoss (T n) L
              (LOOConcentration.deleteAt D i) (D i)
              ∂Measure.pi fun _ : Fin (n + 2) => ν) -
          (∫ p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
              LOOConcentration.Observation 1 1,
            LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
              ∂((Measure.pi fun _ : Fin (n + 2) => ν).prod ν))| =
          variance (id : ℝ → ℝ) μ /
            ((n + 2 : ℝ) * (n + 1 : ℝ)))) := by
  classical
  intro φ ν T L
  have hφ : Measurable φ := by
    change Measurable (fun x : ℝ => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x)))
    fun_prop
  have hνprob : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hνne : ν ≠ 0 := by
    intro h
    have hu : ν Set.univ = 1 := hνprob.measure_univ
    rw [h] at hu
    simp at hu
  have hνfinite : IsFiniteMeasure ν := ⟨by
    rw [hνprob.measure_univ]
    exact ENNReal.one_lt_top⟩
  have hνsigma : SigmaFinite ν :=
    @IsFiniteMeasure.toSigmaFinite _ _ ν hνfinite
  have hνsfinite : SFinite ν := @sfinite_of_sigmaFinite _ _ ν hνsigma
  have htransport := meanQuadratic_observation_product_laws μ hSecond
  have hsample := htransport.1
  have hfresh := htransport.2
  let Pμ (r : ℕ) := Measure.pi fun _ : Fin (r + 1) => μ
  let Pν (r : ℕ) := Measure.pi fun _ : Fin (r + 1) => ν
  let Φ (r : ℕ) (D : Fin (r + 1) → ℝ) := fun i => φ (D i)
  constructor
  · intro r z
    have hscalar := empiricalMean_quadraticRisk_product_consumer μ hSecond r
    have hmap : (Pμ r).map (Φ r) = Pν r := by
      simpa only [Pμ, Pν, Φ] using hsample r
    have hΦ : Measurable (Φ r) := by
      dsimp [Φ]
      fun_prop [empiricalMean]
    have hactualMeas : Measurable
        (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L D z) := by
      change Measurable (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
        (empiricalMean r (WithLp.toLp 2 (fun i => (D i).2 0)) - z.2 0) ^ 2)
      fun_prop [empiricalMean]
    have hactualMapMeas : AEStronglyMeasurable
        (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L D z) ((Pμ r).map (Φ r)) := by
      rw [hmap]
      exact hactualMeas.aestronglyMeasurable
    constructor
    · change Integrable
        (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L D z) (Pν r)
      rw [← hmap]
      change Integrable
        (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L D z) ((Pμ r).map (Φ r))
      apply (integrable_map_measure hactualMapMeas
        hΦ.aemeasurable).2
      change Integrable
        (fun a : Fin (r + 1) → ℝ =>
          (empiricalMean r (WithLp.toLp 2 a) - z.2 0) ^ 2) (Pμ r)
      exact hscalar.1 (z.2 0)
    · calc
        (∫ D : Fin (r + 1) → LOOConcentration.Observation 1 1,
            LOOConcentration.fittedLoss (T r) L D z ∂Pν r) =
          ∫ a : Fin (r + 1) → ℝ,
            LOOConcentration.fittedLoss (T r) L (Φ r a) z ∂Pμ r := by
              rw [← hmap]
              exact integral_map hΦ.aemeasurable hactualMapMeas
        _ = ∫ a : Fin (r + 1) → ℝ,
            (empiricalMean r (WithLp.toLp 2 a) - z.2 0) ^ 2 ∂Pμ r := by
              apply integral_congr_ae
              filter_upwards [] with a
              simp [LOOConcentration.fittedLoss, T, L, Φ, φ, empiricalMean]
        _ = (z.2 0 - ∫ x : ℝ, x ∂μ) ^ 2 +
            variance (id : ℝ → ℝ) μ / (r + 1 : ℝ) := hscalar.2 (z.2 0)
  · intro n
    let Pμn : Measure (Fin (n + 3) → ℝ) := Measure.pi fun _ => μ
    let Pνn : Measure (Fin (n + 2) → LOOConcentration.Observation 1 1) :=
      Measure.pi fun _ => ν
    let PairMap : (Fin (n + 3) → ℝ) →
        ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) := fun a =>
      ((fun i => φ (a i.castSucc)), φ (a (Fin.last (n + 2))))
    let del (i : Fin (n + 2)) :
        (Fin (n + 2) → LOOConcentration.Observation 1 1) → ℝ :=
      fun D => LOOConcentration.fittedLoss (T n) L
        (LOOConcentration.deleteAt D i) (D i)
    let delPair (i : Fin (n + 2)) :
        ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) → ℝ := fun p => del i p.1
    let full : ((Fin (n + 2) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1) → ℝ := fun p =>
      LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2
    have hpair : Pμn.map PairMap = Pνn.prod ν := by
      simpa only [Pμn, Pνn, PairMap] using hfresh n
    have hPairMap : Measurable PairMap := by
      dsimp [PairMap]
      fun_prop
    have hscalar := empiricalMean_quadraticDelete_product_consumer μ hSecond n
    have hPνuniv : Pνn Set.univ = 1 := by
      change (Measure.pi (fun _ : Fin (n + 2) => ν)) Set.univ = 1
      rw [@MeasureTheory.Measure.pi_univ (Fin (n + 2))
        (fun _ : Fin (n + 2) => LOOConcentration.Observation 1 1)
        inferInstance (fun _ => inferInstance) (fun _ => ν) (fun _ => hνsigma)]
      simp [hνprob.measure_univ]
    have hPνfinite : IsFiniteMeasure Pνn := ⟨by
      rw [hPνuniv]
      exact ENNReal.one_lt_top⟩
    have hPνsigma : SigmaFinite Pνn :=
      @IsFiniteMeasure.toSigmaFinite _ _ Pνn hPνfinite
    have hPνsfinite : SFinite Pνn := @sfinite_of_sigmaFinite _ _ Pνn hPνsigma
    have hdelMeas (i : Fin (n + 2)) : Measurable (delPair i) := by
      change Measurable (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
        (empiricalMean n (WithLp.toLp 2
          (fun j => (p.1 (i.succAbove j)).2 0)) - (p.1 i).2 0) ^ 2)
      fun_prop [empiricalMean]
    have hdelMeasMap (i : Fin (n + 2)) :
        AEStronglyMeasurable (delPair i) (Pμn.map PairMap) := by
      rw [hpair]
      exact (hdelMeas i).aestronglyMeasurable
    have hfullMeas : Measurable full := by
      change Measurable (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
        (empiricalMean (n + 1) (WithLp.toLp 2
          (fun j : Fin (n + 2) => (p.1 j).2 0)) - p.2.2 0) ^ 2)
      fun_prop [empiricalMean]
    have hfullMeasMap : AEStronglyMeasurable full (Pμn.map PairMap) := by
      rw [hpair]
      exact hfullMeas.aestronglyMeasurable
    have hdelPair (i : Fin (n + 2)) : Integrable (delPair i) (Pνn.prod ν) := by
      rw [← hpair]
      apply (integrable_map_measure (hdelMeasMap i)
        hPairMap.aemeasurable).2
      change Integrable
        (fun a : Fin (n + 3) → ℝ =>
          (empiricalMean n (WithLp.toLp 2
            (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) -
            a i.castSucc) ^ 2) Pμn
      exact (hscalar.1 i).1
    have hdelPairMap (i : Fin (n + 2)) :
        Integrable (delPair i) (Pμn.map PairMap) := by
      rw [hpair]
      exact hdelPair i
    have hfullPair : Integrable full (Pνn.prod ν) := by
      rw [← hpair]
      apply (integrable_map_measure hfullMeasMap
        hPairMap.aemeasurable).2
      change Integrable
        (fun a : Fin (n + 3) → ℝ =>
          (empiricalMean (n + 1) (WithLp.toLp 2
            (fun j : Fin (n + 2) => a j.castSucc)) -
            a (Fin.last (n + 2))) ^ 2) Pμn
      exact (hscalar.1 0).2
    have hfullPairMap : Integrable full (Pμn.map PairMap) := by
      rw [hpair]
      exact hfullPair
    have hdelId (i : Fin (n + 2)) (a : Fin (n + 3) → ℝ) :
        delPair i (PairMap a) =
          (empiricalMean n (WithLp.toLp 2
            (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) -
            a i.castSucc) ^ 2 := by
      simp [delPair, del, PairMap, LOOConcentration.fittedLoss, T, L, φ,
        LOOConcentration.deleteAt, ContinuousMap.const_apply]
    have hfullId (a : Fin (n + 3) → ℝ) :
        full (PairMap a) =
          (empiricalMean (n + 1) (WithLp.toLp 2
            (fun j : Fin (n + 2) => a j.castSucc)) -
            a (Fin.last (n + 2))) ^ 2 := by
      simp [full, PairMap, LOOConcentration.fittedLoss, T, L, φ,
        ContinuousMap.const_apply]
    have hdel (i : Fin (n + 2)) :
        Integrable (fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 => del i D)
          Pνn := by
      exact @Integrable.of_comp_fst _ _ ℝ _ _ Pνn ν _ hνsfinite hPνsfinite
        (fun D => del i D) (hdelPair i) hνne
    have hdelTransport (i : Fin (n + 2)) :
        (∫ D : Fin (n + 2) → LOOConcentration.Observation 1 1, del i D ∂Pνn) =
          ∫ a : Fin (n + 3) → ℝ,
            (empiricalMean n (WithLp.toLp 2
              (fun j : Fin (n + 1) => a ((i.succAbove j).castSucc))) -
              a i.castSucc) ^ 2 ∂Pμn := by
      calc
        _ = ∫ p, delPair i p ∂(Pνn.prod ν) := by
          symm
          rw [@MeasureTheory.integral_fun_fst _ _ ℝ _ _ Pνn ν _ hνsfinite _ hPνsfinite
            (fun D => del i D)]
          simp [del]
        _ = ∫ a, delPair i (PairMap a) ∂Pμn := by
          rw [← hpair]
          exact integral_map hPairMap.aemeasurable (hdelPairMap i).aestronglyMeasurable
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with a
          exact hdelId i a
    have hfullTransport :
        (∫ p, full p ∂(Pνn.prod ν)) =
          ∫ a : Fin (n + 3) → ℝ,
            (empiricalMean (n + 1) (WithLp.toLp 2
              (fun j : Fin (n + 2) => a j.castSucc)) -
              a (Fin.last (n + 2))) ^ 2 ∂Pμn := by
      calc
        _ = ∫ a, full (PairMap a) ∂Pμn := by
          rw [← hpair]
          exact integral_map hPairMap.aemeasurable hfullPairMap.aestronglyMeasurable
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with a
          exact hfullId a
    refine ⟨hdel, ?_, ?_⟩
    · simpa only [full] using hfullPair
    · intro i
      rw [hdelTransport i, hfullTransport]
      exact hscalar.2 i

end LOOConcentration.Manuscript.Internal
