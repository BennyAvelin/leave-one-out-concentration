import LOOConcentrationRevision.Concentration.NormCapMgf
import LOOConcentrationRevision.Probability.ProductNormCapExpectations
import LOOConcentrationRevision.FunctionalInequalities.BoundedProductLSI

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual squared-norm exponential moment, with its uniform cap estimates
supplied internally by the same admissible completed-pair LSI constant. -/
theorem norm_sq_log_mgf_le_of_admissible_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (s : ℝ) (hs : 0 ≤ s) (hCut : 2 * C * s < 1) :
    Integrable (fun x => Real.exp (s * ‖x‖ ^ 2)) μ ∧
      Real.log (∫ x, Real.exp (s * ‖x‖ ^ 2) ∂μ) ≤
        s * (∫ x, ‖x‖ ^ 2 ∂μ) / (1 - 2 * C * s) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) := by fun_prop
  have hMeans := actual_cap_expectation_monotone_tendsto μ (fun x => ‖x‖ ^ 2)
    hmeas (fun x => sq_nonneg _) hM2
  have hden : 0 < 1 - 2 * C * s := sub_pos.mpr hCut
  let B := s * (∫ x, ‖x‖ ^ 2 ∂μ) / (1 - 2 * C * s)
  have hcap (j : ℕ) :
      (∫ x, Real.exp (s * (((j+1 : ℕ) : ℝ) *
        (1 - Real.exp (-‖x‖ ^ 2 / ((j+1 : ℕ) : ℝ))))) ∂μ) ≤ Real.exp B := by
    let N : ℝ := ((j+1 : ℕ) : ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    have hBound := bounded_norm_cap_log_mgf_bound μ C hC hLC N hN s hs hCut
    have hMeanLE : (∫ x, N * (1 - Real.exp (-‖x‖ ^ 2 / N)) ∂μ) ≤
        ∫ x, ‖x‖ ^ 2 ∂μ := by
      apply ge_of_tendsto hMeans.2
      exact Filter.eventually_atTop.2 ⟨j, fun k hjk => hMeans.1 hjk⟩
    have hLogLE : Real.log (∫ x, Real.exp
        (s * (N * (1 - Real.exp (-‖x‖ ^ 2 / N)))) ∂μ) ≤ B :=
      hBound.2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMeanLE hs) hden.le)
    obtain ⟨hSmooth, hPoint, _⟩ := norm_cap_bounded_smooth
      (E := EuclideanSpace ℝ ι) N hN
    have hQmeas : Measurable (fun x : EuclideanSpace ℝ ι =>
        N * (1 - Real.exp (-‖x‖ ^ 2 / N))) := hSmooth.continuous.measurable
    have hQbound : ∀ x : EuclideanSpace ℝ ι,
        |N * (1 - Real.exp (-‖x‖ ^ 2 / N))| ≤ N := by
      intro x
      rw [abs_of_nonneg (hPoint x).1]
      exact (hPoint x).2.1
    have hPos := bounded_mgf_partition_pos (μ := μ)
      (fun x : EuclideanSpace ℝ ι => N * (1 - Real.exp (-‖x‖ ^ 2 / N)))
      hQmeas (B := N) (s := s) hQbound
    change 0 < (∫ x, Real.exp (s * (N * (1 - Real.exp (-‖x‖ ^ 2 / N)))) ∂μ) at hPos
    have hExpLE := Real.exp_le_exp.mpr hLogLE
    rw [Real.exp_log hPos] at hExpLE
    exact hExpLE
  obtain ⟨hInt, hIntegralLE⟩ := actual_cap_exponential_limit μ (fun x => ‖x‖ ^ 2)
    hmeas (fun x => sq_nonneg _) s (Real.exp B) hs (Real.exp_nonneg _) hcap
  have hOne : (1 : ℝ) ≤ ∫ x, Real.exp (s * ‖x‖ ^ 2) ∂μ := by
    have h := integral_mono (integrable_const (1 : ℝ)) hInt
      (fun x => Real.one_le_exp_iff.mpr (mul_nonneg hs (sq_nonneg _)))
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hLog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hOne) hIntegralLE
  rw [Real.log_exp] at hLog
  exact ⟨hInt, hLog⟩

/-- The manuscript's positive finite product norm-MGF bound, with the same
optimal base constant and the actual product second moment. -/
theorem euclideanProduct_norm_sq_log_mgf_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (s : ℝ) (hs : 0 ≤ s)
    (hCut : 2 * (logSobolevConstant μ).toReal * s < 1) :
    let ν := euclideanProductLaw (κ := Fin (r+1)) μ
    Integrable (fun x => Real.exp (s * ‖x‖ ^ 2)) ν ∧
      Real.log (∫ x, Real.exp (s * ‖x‖ ^ 2) ∂ν) ≤
        s * ((r+1 : ℕ) : ℝ) * (∫ z, ‖z‖ ^ 2 ∂μ) /
          (1 - 2 * (logSobolevConstant μ).toReal * s) := by
  let ν := euclideanProductLaw (κ := Fin (r+1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal (logSobolevConstant μ).toReal := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    exact logSobolevConstant_euclideanProductLaw_le r μ hfinite
  have h := norm_sq_log_mgf_le_of_admissible_constant ν (logSobolevConstant μ).toReal
    ENNReal.toReal_nonneg hLC (integrable_euclideanProductLaw_norm_sq μ hM2) s hs hCut
  have hMean := integral_euclideanProductLaw_norm_sq (κ := Fin (r+1)) μ hM2
  change (∫ x, ‖x‖ ^ 2 ∂ν) = _ at hMean
  rw [hMean] at h
  simpa only [Fintype.card_fin, mul_assoc] using h

/-- The same exact bound for every finite product size, including the empty
product. The zero-size law lives on the zero-dimensional Euclidean carrier. -/
theorem euclideanProduct_norm_sq_log_mgf_bound_all_sizes
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (s : ℝ) (hs : 0 ≤ s)
    (hCut : 2 * (logSobolevConstant μ).toReal * s < 1) :
    let ν := euclideanProductLaw (κ := Fin r) μ
    Integrable (fun x => Real.exp (s * ‖x‖ ^ 2)) ν ∧
      Real.log (∫ x, Real.exp (s * ‖x‖ ^ 2) ∂ν) ≤
        s * (r : ℝ) * (∫ z, ‖z‖ ^ 2 ∂μ) /
          (1 - 2 * (logSobolevConstant μ).toReal * s) := by
  cases r with
  | zero =>
    let ν := euclideanProductLaw (κ := Fin 0) μ
    let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    have hf : (fun x : EuclideanSpace ℝ (Fin 0 × ι) => Real.exp (s * ‖x‖ ^ 2)) =
        fun _ => (1 : ℝ) := by
      funext x
      rw [Subsingleton.elim x 0]
      simp
    change Integrable _ ν ∧ _
    rw [hf]
    constructor
    · exact integrable_const 1
    · simp
  | succ r =>
    exact euclideanProduct_norm_sq_log_mgf_bound r μ hfinite hM2 s hs hCut

end LOOConcentration.Revision
