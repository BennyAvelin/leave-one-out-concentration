import LOOConcentrationRevision.Concentration.BoundedQuadraticTiltEntropy
import LOOConcentrationRevision.Concentration.NormMgfAbsorptionConsumer
import LOOConcentration.Concentration.EntropyToMGF

set_option autoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory

/-- The variational norm bound for the actual tilt of a bounded observable.
All density and weighted-moment integrability is supplied internally. -/
private theorem bounded_tilt_norm_variational
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ x, |F x| ≤ B)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) ν)
    (lam s : ℝ) (hs : 0 ≤ s)
    (hExp : Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (s * ‖x‖ ^ 2)) ν) :
    s * (∫ x, LOOConcentration.tiltDensity ν F lam x * ‖x‖ ^ 2 ∂ν) ≤
      LOOConcentration.tiltEntropy ν F lam +
        Real.log (∫ x : EuclideanSpace ℝ ι, Real.exp (s * ‖x‖ ^ 2) ∂ν) := by
  let w := LOOConcentration.tiltDensity ν F lam
  have hZ : 0 < LOOConcentration.tiltPartition ν F lam :=
    LOOConcentration.tiltPartition_pos hF hB hBound
  have hwpos : ∀ x, 0 < w x := fun x => div_pos (Real.exp_pos _) hZ
  have hwmeas : Measurable w :=
    (Real.measurable_exp.comp (measurable_const.mul hF)).div_const _
  have hw : Integrable w ν := by
    have h := LOOConcentration.integrable_tiltDensity_mul_of_nonneg_integrable
      (μ := ν) (F := F) (Q := fun _ => (1 : ℝ)) (t := lam)
      hF hB hBound measurable_const (fun _ => zero_le_one) (integrable_const 1)
    simpa only [mul_one] using h
  have hwone : ∫ x, w x ∂ν = 1 :=
    LOOConcentration.tiltDensity_integral_eq_one hF hB hBound
  have hMoment : Integrable (fun x => w x * ‖x‖ ^ 2) ν :=
    LOOConcentration.integrable_tiltDensity_mul_of_nonneg_integrable
      hF hB hBound (by fun_prop) (fun x => sq_nonneg _) hM2
  have hlog : ∀ x, Real.log (w x) =
      lam * F x - Real.log (LOOConcentration.tiltPartition ν F lam) := by
    intro x
    dsimp [w, LOOConcentration.tiltDensity]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hZ.ne', Real.log_exp]
  have hLogBound : ∀ᵐ x ∂ν, ‖Real.log (w x)‖ ≤
      |lam| * B + |Real.log (LOOConcentration.tiltPartition ν F lam)| := by
    filter_upwards with x
    rw [Real.norm_eq_abs, hlog x]
    calc
      |lam * F x - Real.log (LOOConcentration.tiltPartition ν F lam)| ≤
          |lam * F x| + |Real.log (LOOConcentration.tiltPartition ν F lam)| :=
        by simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (lam * F x) (-Real.log (LOOConcentration.tiltPartition ν F lam))
      _ ≤ |lam| * B + |Real.log (LOOConcentration.tiltPartition ν F lam)| := by
        rw [abs_mul]
        gcongr
        exact hBound x
  have hEntropy : Integrable (fun x => w x * Real.log (w x)) ν :=
    by simpa only [Function.comp_def, mul_comm] using
      hw.bdd_mul (Real.measurable_log.comp hwmeas).aestronglyMeasurable hLogBound
  have hExpPos : 0 < ∫ x : EuclideanSpace ℝ ι, Real.exp (s * ‖x‖ ^ 2) ∂ν := by
    have hLower := integral_mono (integrable_const (1 : ℝ)) hExp
      (fun x => by simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (mul_nonneg hs (sq_nonneg ‖x‖))))
    rw [integral_const, probReal_univ, one_smul] at hLower
    exact lt_of_lt_of_le zero_lt_one hLower
  exact LOOConcentration.probability_density_variational_inequality
    hwpos hw hwone hExp hExpPos rfl hMoment hEntropy

/-- Actual bounded smooth entropy absorption under the same product LSI.
The gradient and variational predecessors are proved inside this consumer. -/
theorem bounded_smooth_product_tilt_entropy_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (a b : NNReal) (hb : 0 < (b : ℝ))
    (hGrowth : ∀ x, ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (lam : ℝ) (hlam : 0 < |lam|) (hcut : |lam| ≤ 1 / (4 * C * (b : ℝ))) :
    LOOConcentration.tiltEntropy (euclideanProductLaw (κ := Fin (r + 1)) μ) F lam ≤
      2 * C * lam ^ 2 * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
        ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ)) := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hfinite := lt_of_le_of_lt hLC ENNReal.ofReal_lt_top
  have hνLC : logSobolevConstant ν ≤ ENNReal.ofReal C :=
    (logSobolevConstant_euclideanProductLaw_le r μ hfinite).trans hLC
  have hνM2 := integrable_euclideanProductLaw_norm_sq (κ := Fin (r + 1)) μ hM2
  have hEntropy := bounded_smooth_tilt_entropy_affine_growth_bound
    ν C hC.le hνLC F hF B hB hBound hνM2 a b hGrowth lam
  let s : ℝ := 2 * C * lam ^ 2 * (b : ℝ) ^ 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hscaled := (le_div_iff₀ (by positivity : 0 < 4 * C * (b : ℝ))).mp hcut
  have hsq : (4 * C * (b : ℝ) * |lam|) ^ 2 ≤ 1 := by
    have hn : 0 ≤ 4 * C * (b : ℝ) * |lam| := by positivity
    have hl : 4 * C * (b : ℝ) * |lam| ≤ 1 := by nlinarith [hscaled]
    nlinarith
  have hsCut : 2 * C * s < 1 := by
    dsimp [s]
    rw [mul_pow, mul_pow, sq_abs] at hsq
    nlinarith
  have hNorm := norm_sq_log_mgf_le_of_admissible_constant ν C hC.le hνLC hνM2 s hs hsCut
  have hTilt := bounded_tilt_norm_variational ν F hF.continuous.measurable B hB
    (fun x => (hBound x).1) hνM2 lam s hs hNorm.1
  exact (product_norm_mgf_entropy_absorption_of_tilt_bounds (r + 1) μ C hC hLC hM2
    (a : ℝ) (b : ℝ) lam (LOOConcentration.tiltEntropy ν F lam)
    (∫ x, LOOConcentration.tiltDensity ν F lam x * ‖x‖ ^ 2 ∂ν)
    a.2 hb hlam hcut hEntropy hTilt).2

/-- The original bounded smooth product observable has the centered log-MGF
bound, including parameter zero, without entropy or norm-MGF premises. -/
theorem bounded_smooth_product_centered_log_mgf_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (a b : NNReal) (hb : 0 < (b : ℝ))
    (hGrowth : ∀ x, ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (t : ℝ) (hcut : |t| ≤ 1 / (4 * C * (b : ℝ))) :
    LOOConcentration.logPartitionLog (euclideanProductLaw (κ := Fin (r + 1)) μ) F t -
      t * (∫ x, F x ∂euclideanProductLaw (κ := Fin (r + 1)) μ) ≤
        (2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
          (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2 := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  apply LOOConcentration.boundedObservable_logPartitionLog_centered_of_entropy_bound
    hF.continuous.measurable hB (fun x => (hBound x).1) (ht := hcut)
  intro u hu hucut
  have h := bounded_smooth_product_tilt_entropy_bound
    r μ C hC hLC hM2 F hF B hB hBound a b hb hGrowth u hu hucut
  convert h using 1; ring

end LOOConcentration.Revision
