import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransportConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped ENNReal

/-- Product laws for the literal response-only embedding into `Observation 1 1`. -/
theorem meanQuadratic_observation_product_laws
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    (∀ r : ℕ,
      (Measure.pi fun _ : Fin (r + 1) => μ).map
        (fun D : Fin (r + 1) → ℝ => fun i => φ (D i)) =
          Measure.pi fun _ : Fin (r + 1) => ν) ∧
    (∀ n : ℕ,
      (Measure.pi fun _ : Fin (n + 3) => μ).map
        (fun a : Fin (n + 3) → ℝ =>
          ((fun i : Fin (n + 2) => φ (a i.castSucc)), φ (a (Fin.last (n + 2))))) =
        (Measure.pi fun _ : Fin (n + 2) => ν).prod ν) := by
  classical
  intro φ ν
  have hφ : Measurable φ := by
    change Measurable (fun x : ℝ => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x)))
    fun_prop
  have hνprob : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hνsigma : SigmaFinite ν := by
    exact @IsFiniteMeasure.toSigmaFinite _ _ ν
      ⟨by rw [hνprob.measure_univ]; exact ENNReal.one_lt_top⟩
  have hsample (r : ℕ) :
      (Measure.pi fun _ : Fin (r + 1) => μ).map
        (fun D : Fin (r + 1) → ℝ => fun i => φ (D i)) =
          Measure.pi fun _ : Fin (r + 1) => ν := by
    have hSigmaFamily : ∀ _i : Fin (r + 1), SigmaFinite (μ.map φ) := by
      intro i
      simpa only [ν] using hνsigma
    simpa only [ν] using
      (Measure.pi_map_pi (hμ := hSigmaFamily) fun _ => hφ.aemeasurable)
  refine ⟨hsample, ?_⟩
  intro n
  have hMomentTransport :=
    scalarObservation_sample_and_fresh_test_transport μ hSecond true n
  have hfull :
      (Measure.pi fun _ : Fin (n + 3) => μ).map
        (fun a : Fin (n + 3) → ℝ => fun i => φ (a i)) =
          Measure.pi fun _ : Fin (n + 3) => ν := by
    simpa [φ, ν] using hMomentTransport.2.2.2.2.1
  have hsplit := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 3) => ν)
      (Fin.last (n + 2)))
  change MeasurePreserving
    (fun D : Fin (n + 3) → LOOConcentration.Observation 1 1 =>
      ((fun i : Fin (n + 2) => D ((Fin.last (n + 2)).succAbove i)),
        D (Fin.last (n + 2))))
    (Measure.pi fun _ : Fin (n + 3) => ν)
    ((Measure.pi fun _ : Fin (n + 2) => ν).prod ν) at hsplit
  simp only [Fin.succAbove_last] at hsplit
  have hmap : Measurable
      (fun D : Fin (n + 3) → LOOConcentration.Observation 1 1 =>
        ((fun i : Fin (n + 2) => D i.castSucc), D (Fin.last (n + 2)))) := by
    fun_prop
  have hsource : Measurable
      (fun a : Fin (n + 3) → ℝ => fun i => φ (a i)) := by
    fun_prop
  calc
    (Measure.pi fun _ : Fin (n + 3) => μ).map
        (fun a : Fin (n + 3) → ℝ =>
          ((fun i : Fin (n + 2) => φ (a i.castSucc)), φ (a (Fin.last (n + 2))))) =
        ((Measure.pi fun _ : Fin (n + 3) => μ).map
          (fun a : Fin (n + 3) → ℝ => fun i => φ (a i))).map
          (fun D : Fin (n + 3) → LOOConcentration.Observation 1 1 =>
            ((fun i : Fin (n + 2) => D i.castSucc), D (Fin.last (n + 2)))) := by
      exact (Measure.map_map hmap hsource).symm
    _ = (Measure.pi fun _ : Fin (n + 3) => ν).map
        (fun D : Fin (n + 3) → LOOConcentration.Observation 1 1 =>
          ((fun i : Fin (n + 2) => D i.castSucc), D (Fin.last (n + 2)))) := by
      rw [hfull]
    _ = (Measure.pi fun _ : Fin (n + 2) => ν).prod ν := hsplit.map_eq

end LOOConcentration.Manuscript.Internal
