import LOOConcentrationRevision.Concentration.BoundedProductQuadraticMgf
import LOOConcentrationRevision.Analysis.SourceMollifiedL1Limit
import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator
import LOOConcentration.Analysis.ClipLimit

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology

private theorem centered_lintegral_le_of_log_partition
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (F : α → ℝ) (hF : Measurable F) (B t V : ℝ) (hBound : ∀ x, |F x| ≤ B)
    (hLog : LOOConcentration.logPartitionLog ν F t - t * (∫ x, F x ∂ν) ≤ V) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * (F x - ∫ y, F y ∂ν))) ∂ν ≤
      ENNReal.ofReal (Real.exp V) := by
  let m := ∫ y, F y ∂ν
  have hExp := bounded_mgf_integrable (μ := ν) F hF (B := B) (s := t) hBound
  have hEq : (fun x => Real.exp (t * (F x - m))) =
      fun x => Real.exp (t * F x) * Real.exp (-(t * m)) := by
    funext x
    rw [show t * (F x - m) = t * F x + -(t * m) by ring, Real.exp_add]
  have hInt : Integrable (fun x => Real.exp (t * (F x - m))) ν := by
    rw [hEq]
    exact hExp.mul_const _
  have hPos := bounded_mgf_partition_pos (μ := ν) F hF (B := B) (s := t) hBound
  change 0 < (∫ x, Real.exp (t * F x) ∂ν) at hPos
  have hIntegral : (∫ x, Real.exp (t * (F x - m)) ∂ν) =
      Real.exp (LOOConcentration.logPartitionLog ν F t - t * m) := by
    rw [hEq, integral_mul_const]
    change _ = Real.exp (Real.log (∫ x, Real.exp (t * F x) ∂ν) - t * m)
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hPos]
  calc
    _ = ENNReal.ofReal (∫ x, Real.exp (t * (F x - m)) ∂ν) := by
      exact (ofReal_integral_eq_lintegral_ofReal hInt
        (ae_of_all _ fun x => Real.exp_nonneg _)).symm
    _ = ENNReal.ofReal (Real.exp
        (LOOConcentration.logPartitionLog ν F t - t * m)) := by rw [hIntegral]
    _ ≤ ENNReal.ofReal (Real.exp V) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hLog)

private theorem source_mollification_radius_pos (j : ℕ) :
    0 < mollificationRadius j := by
  dsimp [mollificationRadius]
  positivity

private theorem source_mollification_radius_tendsto :
    Tendsto mollificationRadius atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ))
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Positive-growth source inputs give the original centered exponential
bound after both the actual mollification and clipping limits. -/
theorem source_product_centered_exp_positive_growth
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : NNReal) (hb : 0 < (b : ℝ))
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (t : ℝ) (hcut : |t| ≤ 1 / (4 * C * (b : ℝ))) :
    Integrable F (euclideanProductLaw (κ := Fin (r + 1)) μ) ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp (t * (F x -
        ∫ y, F y ∂euclideanProductLaw (κ := Fin (r + 1)) μ)))
          ∂euclideanProductLaw (κ := Fin (r + 1)) μ) ≤
        ENNReal.ofReal (Real.exp ((2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
          ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2)) := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hνM2 := integrable_euclideanProductLaw_norm_sq (κ := Fin (r + 1)) μ hM2
  have hsource := source_segment_estimate_and_integrable ν hνM2 F hloc a b hgrad
  have hlim := source_clipThenMollify_L1_and_mean_tendsto ν hνM2 F hloc a b hgrad
  let K : ℝ := 2 * (b : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ)
  let envelope : ℕ → ENNReal := fun j => ENNReal.ofReal (Real.exp
    ((2 * C * (((a : ℝ) + (b : ℝ) * mollificationRadius j) ^ 2 + K)) * t ^ 2))
  let limitBound : ENNReal := ENNReal.ofReal
    (Real.exp ((2 * C * ((a : ℝ) ^ 2 + K)) * t ^ 2))
  have hEnvelope : Tendsto envelope atTop (𝓝 limitBound) := by
    have hlinear : Tendsto
        (fun j => (a : ℝ) + (b : ℝ) * mollificationRadius j) atTop (𝓝 (a : ℝ)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.mul source_mollification_radius_tendsto)
    have hsquare := hlinear.pow 2
    have hexponent := ((hsquare.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K))).const_mul (2 * C)).mul_const
      (t ^ 2)
    exact (ENNReal.continuous_ofReal.comp Real.continuous_exp).continuousAt.tendsto.comp hexponent
  have hClipped (R : NNReal) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (t * (clipFunction R F x -
        ∫ y, clipFunction R F y ∂ν))) ∂ν) ≤ limitBound := by
    let f : ℕ → EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ :=
      fun j => clipThenMollify F R (mollificationRadius j)
    have hfamily := hlim.2 R
    have hApprox (j : ℕ) :
        (∫⁻ x, ENNReal.ofReal (Real.exp (t * (f j x - ∫ y, f j y ∂ν))) ∂ν) ≤
          envelope j := by
      have hη := source_mollification_radius_pos j
      obtain ⟨hsmooth, B, hB, hBound⟩ :=
        clipThenMollify_bounded_smooth F hloc.continuous R (mollificationRadius j) hη
      let aj : NNReal := ⟨(a : ℝ) + (b : ℝ) * mollificationRadius j, by positivity⟩
      have hGrowth : ∀ x, ‖gradient (f j) x‖ ≤ (aj : ℝ) + (b : ℝ) * ‖x‖ := by
        intro x
        exact clipThenMollify_gradient_growth F hloc.continuous a b R
          (mollificationRadius j) hη hsource.1 x
      have hLog := bounded_smooth_product_centered_log_mgf_bound
        r μ C hC hLC hM2 (f j) hsmooth B hB hBound aj b hb hGrowth t hcut
      exact centered_lintegral_le_of_log_partition ν (f j) hsmooth.continuous.measurable
        B t ((2 * C * ((aj : ℝ) ^ 2 + K)) * t ^ 2) (fun x => (hBound x).1) hLog
    let phi : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (t * z))
    have hphi : Continuous phi :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hfatou := LOOConcentration.centeredTransform_fatou
      hfamily.1 hfamily.2.1 (ae_of_all _ hfamily.2.2.2.2)
      hfamily.2.2.2.1 phi hphi
    calc
      _ ≤ atTop.liminf (fun j => ∫⁻ x, ENNReal.ofReal
          (Real.exp (t * (f j x - ∫ y, f j y ∂ν))) ∂ν) := hfatou
      _ ≤ atTop.liminf envelope := liminf_le_liminf (Eventually.of_forall hApprox)
      _ = limitBound := hEnvelope.liminf_eq
  have hclipInt (j : ℕ) : Integrable (LOOConcentration.clipValueSequence F j) ν := by
    let R : NNReal := ⟨(j : ℝ) + 1, by positivity⟩
    exact (hlim.2 R).2.1
  have hclipBound (j : ℕ) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (t * (LOOConcentration.clipValueSequence F j x -
        ∫ y, LOOConcentration.clipValueSequence F j y ∂ν))) ∂ν) ≤ limitBound := by
    let R : NNReal := ⟨(j : ℝ) + 1, by positivity⟩
    exact hClipped R
  refine ⟨hsource.2, ?_⟩
  exact LOOConcentration.centeredExp_fatou hclipInt hsource.2
    (ae_of_all _ (LOOConcentration.clipValueSequence_tendsto F))
    (LOOConcentration.clipValueSequence_integral_tendsto hsource.2) t limitBound hclipBound

/-- The nonnegative exponential limit is finite, and hence has its actual
real integral and log bound; finiteness is proved before using those integrals. -/
theorem source_product_centered_mgf_positive_growth
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : NNReal) (hb : 0 < (b : ℝ))
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (t : ℝ) (hcut : |t| ≤ 1 / (4 * C * (b : ℝ))) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    let V := (2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
      ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ Real.exp V ∧
        Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ V := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  obtain ⟨hFInt, hLin⟩ := source_product_centered_exp_positive_growth
    r μ C hC hLC hM2 F hloc a b hb hgrad t hcut
  let V := (2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
      ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2
  have hMeas : Measurable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) := by
    exact (measurable_const.mul (hloc.continuous.measurable.sub measurable_const)).exp
  have hFinite : (∫⁻ x, ENNReal.ofReal (Real.exp (t * (F x - ∫ y, F y ∂ν))) ∂ν) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hLin ENNReal.ofReal_lt_top)
  have hInt := (lintegral_ofReal_ne_top_iff_integrable hMeas.aestronglyMeasurable
    (ae_of_all _ fun x => Real.exp_nonneg _)).mp hFinite
  have hBound : (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ Real.exp V := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg V)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun x => Real.exp_nonneg _)]
    exact hLin
  have hPos := integral_exp_pos hInt
  exact ⟨hFInt, hInt, hBound, (Real.log_le_iff_le_exp hPos).2 hBound⟩

end LOOConcentration.Revision
