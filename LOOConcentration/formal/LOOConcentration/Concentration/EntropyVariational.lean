import LOOConcentration.Frozen.Norms.DatasetNormSq
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Variational inequality for an exponential tilt

The norm exponential moment and the tilted norm moment used below are finite
integrability inputs. In the concentration argument, the former is supplied
by the future `lemma:norm` provider.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partition function of the exponential tilt by `F` at `λ`. -/
def tiltPartition (μ : Measure Ω) (F : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * F ω) ∂μ

/-- The normalized density of the exponential tilt by `F` at `λ`. -/
def tiltDensity (μ : Measure Ω) (F : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (t * F ω) / tiltPartition μ F t

/-- Entropy of a normalized exponential tilt, written as relative entropy. -/
def tiltEntropy (μ : Measure Ω) (F : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, tiltDensity μ F t ω * Real.log (tiltDensity μ F t ω) ∂μ

private theorem integrable_of_measurable_norm_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {K : ℝ}
    (hf : Measurable f) (_hK : 0 ≤ K) (hbound : ∀ ω, ‖f ω‖ ≤ K) :
    Integrable f μ := by
  refine Integrable.mono' (integrable_const K) hf.aestronglyMeasurable ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg _hK] using hbound ω

private theorem integrable_exp_mul_bounded {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (_hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => Real.exp (t * F ω)) μ := by
  apply integrable_of_measurable_norm_le
    (Real.measurable_exp.comp (measurable_const.mul hFmeas))
    (Real.exp_nonneg _)
  intro ω
  change |Real.exp (t * F ω)| ≤ Real.exp (|t| * B)
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * F ω ≤ |t * F ω| := le_abs_self _
    _ = |t| * |F ω| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg _)

omit [MeasurableSpace Ω] in
private theorem exp_neg_abs_mul_le_exp_mul {F : Ω → ℝ} {B t : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) (ω : Ω) :
    Real.exp (-(|t| * B)) ≤ Real.exp (t * F ω) := by
  apply Real.exp_le_exp.mpr
  have hmul : |t * F ω| ≤ |t| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg _)
  calc
    -( |t| * B) ≤ -|t * F ω| := neg_le_neg hmul
    _ ≤ t * F ω := neg_abs_le _

/-- A bounded measurable observable has a finite, strictly positive partition
function under a probability measure. -/
theorem tiltPartition_pos {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    0 < tiltPartition μ F t := by
  let c : ℝ := Real.exp (-(|t| * B))
  have hExp := integrable_exp_mul_bounded (μ := μ) (F := F) hFmeas hB hF (t := t)
  have hLower : (∫ _ω, c ∂μ) ≤ tiltPartition μ F t := by
    rw [tiltPartition]
    exact integral_mono (integrable_const c) hExp (fun ω => by
      exact exp_neg_abs_mul_le_exp_mul hF ω)
  rw [integral_const, probReal_univ, one_smul] at hLower
  exact (Real.exp_pos _).trans_le (by simpa [c] using hLower)

/-- The normalized exponential tilt has total mass one. -/
theorem tiltDensity_integral_eq_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    ∫ ω, tiltDensity μ F t ω ∂μ = 1 := by
  have hZ := tiltPartition_pos (μ := μ) (F := F) hFmeas hB hF (t := t)
  have hmul :
      (∫ ω, Real.exp (t * F ω) * (tiltPartition μ F t)⁻¹ ∂μ) =
        (∫ ω, Real.exp (t * F ω) ∂μ) * (tiltPartition μ F t)⁻¹ :=
    integral_mul_const (tiltPartition μ F t)⁻¹ _
  calc
    ∫ ω, tiltDensity μ F t ω ∂μ =
        ∫ ω, Real.exp (t * F ω) * (tiltPartition μ F t)⁻¹ ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          simp [tiltDensity, div_eq_mul_inv]
    _ = (∫ ω, Real.exp (t * F ω) ∂μ) * (tiltPartition μ F t)⁻¹ := hmul
    _ = 1 := by
      simpa only [tiltPartition] using mul_inv_cancel₀ hZ.ne'

private theorem integrable_tiltDensity {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (tiltDensity μ F t) μ := by
  have hExp := integrable_exp_mul_bounded (μ := μ) (F := F) hFmeas hB hF (t := t)
  change Integrable
    (fun ω => Real.exp (t * F ω) / tiltPartition μ F t) μ
  simpa only [div_eq_mul_inv] using
    hExp.mul_const (tiltPartition μ F t)⁻¹

private theorem integrable_tiltDensity_mul_observable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => tiltDensity μ F t ω * F ω) μ := by
  have hZ := tiltPartition_pos (μ := μ) (F := F) hFmeas hB hF (t := t)
  have hDensityPos : ∀ ω, 0 < tiltDensity μ F t ω := by
    intro ω
    exact div_pos (Real.exp_pos _) hZ
  have hDensityMeas : Measurable (tiltDensity μ F t) := by
    change Measurable (fun ω => Real.exp (t * F ω) / tiltPartition μ F t)
    exact (Real.measurable_exp.comp (measurable_const.mul hFmeas)).div_const _
  let K : ℝ := Real.exp (|t| * B) / tiltPartition μ F t
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (Real.exp_pos _) hZ
  have hUpper : ∀ ω, tiltDensity μ F t ω ≤ K := by
    intro ω
    dsimp [K]
    apply (div_le_div_iff_of_pos_right hZ).2
    apply Real.exp_le_exp.mpr
    calc
      t * F ω ≤ |t * F ω| := le_abs_self _
      _ = |t| * |F ω| := abs_mul _ _
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg _)
  apply integrable_of_measurable_norm_le (hDensityMeas.mul hFmeas)
    (mul_nonneg hK.le hB)
  intro ω
  change |tiltDensity μ F t ω * F ω| ≤ K * B
  rw [abs_mul, abs_of_pos (hDensityPos ω)]
  calc
    tiltDensity μ F t ω * |F ω| ≤ K * |F ω| :=
      mul_le_mul_of_nonneg_right (hUpper ω) (abs_nonneg _)
    _ ≤ K * B := mul_le_mul_of_nonneg_left (hF ω) hK.le

private theorem integrable_tiltEntropy_integrand {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable
      (fun ω => tiltDensity μ F t ω * Real.log (tiltDensity μ F t ω)) μ := by
  have hDensity := integrable_tiltDensity hFmeas hB hF (μ := μ) (t := t)
  have hObs := integrable_tiltDensity_mul_observable
    hFmeas hB hF (μ := μ) (t := t)
  have hZ := tiltPartition_pos (μ := μ) (F := F) hFmeas hB hF (t := t)
  have hEq :
      (fun ω => tiltDensity μ F t ω * Real.log (tiltDensity μ F t ω)) =
        fun ω => t * (tiltDensity μ F t ω * F ω) -
          Real.log (tiltPartition μ F t) * tiltDensity μ F t ω := by
    funext ω
    have hlog : Real.log (tiltDensity μ F t ω) =
        t * F ω - Real.log (tiltPartition μ F t) := by
      change Real.log (Real.exp (t * F ω) / tiltPartition μ F t) = _
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hZ.ne', Real.log_exp]
    rw [hlog]
    ring
  have hRhs : Integrable
      (fun ω => t * (tiltDensity μ F t ω * F ω) -
        Real.log (tiltPartition μ F t) * tiltDensity μ F t ω) μ :=
    (hObs.const_mul t).sub (hDensity.const_mul _)
  rw [hEq]
  exact hRhs

/-- The integral definition of tilt entropy equals `t` times the tilted
observable mean minus the log partition function. Together with the usual
bounded-observable derivative formula for `log Z`, this is `t ψ'(t) - ψ(t)`.
-/
theorem tiltEntropy_eq_tiltMean_sub_logPartition {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hFmeas : Measurable F)
    {B t : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    tiltEntropy μ F t =
      t * (∫ ω, tiltDensity μ F t ω * F ω ∂μ) -
        Real.log (tiltPartition μ F t) := by
  have hDensity := integrable_tiltDensity hFmeas hB hF (μ := μ) (t := t)
  have hObs := integrable_tiltDensity_mul_observable
    hFmeas hB hF (μ := μ) (t := t)
  have hEntropy := integrable_tiltEntropy_integrand
    hFmeas hB hF (μ := μ) (t := t)
  have hDensityOne := tiltDensity_integral_eq_one
    (μ := μ) (F := F) hFmeas hB hF (t := t)
  have hEq :
      (fun ω => tiltDensity μ F t ω * Real.log (tiltDensity μ F t ω)) =
        fun ω => t * (tiltDensity μ F t ω * F ω) -
          Real.log (tiltPartition μ F t) * tiltDensity μ F t ω := by
    funext ω
    have hZ := tiltPartition_pos (μ := μ) (F := F) hFmeas hB hF (t := t)
    have hlog : Real.log (tiltDensity μ F t ω) =
        t * F ω - Real.log (tiltPartition μ F t) := by
      change Real.log (Real.exp (t * F ω) / tiltPartition μ F t) = _
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hZ.ne', Real.log_exp]
    rw [hlog]
    ring
  calc
    tiltEntropy μ F t =
        ∫ ω, t * (tiltDensity μ F t ω * F ω) -
          Real.log (tiltPartition μ F t) * tiltDensity μ F t ω ∂μ := by
      unfold tiltEntropy
      exact integral_congr_ae (ae_of_all _ fun ω => congrFun hEq ω)
    _ = t * (∫ ω, tiltDensity μ F t ω * F ω ∂μ) -
          Real.log (tiltPartition μ F t) *
            (∫ ω, tiltDensity μ F t ω ∂μ) := by
      rw [integral_sub (hObs.const_mul t) (hDensity.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = t * (∫ ω, tiltDensity μ F t ω * F ω ∂μ) -
          Real.log (tiltPartition μ F t) := by rw [hDensityOne]; ring

/-- Finite form of the entropy variational inequality. The integrability
premises ensure that every integral used in the argument is finite. -/
theorem probability_density_variational_inequality
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w g : Ω → ℝ} {s M : ℝ}
    (hwpos : ∀ ω, 0 < w ω)
    (hw : Integrable w μ) (hwone : ∫ ω, w ω ∂μ = 1)
    (hExp : Integrable (fun ω => Real.exp (s * g ω)) μ)
    (hMpos : 0 < M) (hM : M = ∫ ω, Real.exp (s * g ω) ∂μ)
    (hMoment : Integrable (fun ω => w ω * g ω) μ)
    (hEntropy : Integrable (fun ω => w ω * Real.log (w ω)) μ) :
    s * (∫ ω, w ω * g ω ∂μ) ≤
      (∫ ω, w ω * Real.log (w ω) ∂μ) + Real.log M := by
  have hPoint : ∀ ω,
      w ω * (s * g ω - Real.log M - Real.log (w ω)) ≤
        Real.exp (s * g ω) / M - w ω := by
    intro ω
    have hwω := hwpos ω
    have hratio : 0 < Real.exp (s * g ω) / (M * w ω) :=
      div_pos (Real.exp_pos _) (mul_pos hMpos hwω)
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hlogEq : Real.log (Real.exp (s * g ω) / (M * w ω)) =
        s * g ω - Real.log M - Real.log (w ω) := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos _))
        (mul_ne_zero hMpos.ne' (ne_of_gt hwω)),
        Real.log_mul hMpos.ne' (ne_of_gt hwω), Real.log_exp]
      ring
    calc
      w ω * (s * g ω - Real.log M - Real.log (w ω)) =
          w ω * Real.log (Real.exp (s * g ω) / (M * w ω)) := by rw [hlogEq]
      _ ≤ w ω * (Real.exp (s * g ω) / (M * w ω) - 1) :=
        mul_le_mul_of_nonneg_left hlog hwω.le
      _ = Real.exp (s * g ω) / M - w ω := by
        field_simp
  have hLeft : Integrable
      (fun ω => w ω * (s * g ω - Real.log M - Real.log (w ω))) μ := by
    have hA : Integrable (fun ω => s * (w ω * g ω)) μ := hMoment.const_mul s
    have hB : Integrable (fun ω => Real.log M * w ω) μ := hw.const_mul _
    have hEq :
        (fun ω => w ω * (s * g ω - Real.log M - Real.log (w ω))) =
          fun ω => s * (w ω * g ω) - Real.log M * w ω -
            w ω * Real.log (w ω) := by
      funext ω
      ring
    rw [hEq]
    exact (hA.sub hB).sub hEntropy
  have hRight : Integrable
      (fun ω => Real.exp (s * g ω) / M - w ω) μ := by
    have hExpDiv : Integrable
        (fun ω => Real.exp (s * g ω) * M⁻¹) μ := hExp.mul_const M⁻¹
    have hEq :
        (fun ω => Real.exp (s * g ω) / M - w ω) =
          fun ω => Real.exp (s * g ω) * M⁻¹ - w ω := by
      funext ω
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hExpDiv.sub hw
  have hIntegral := integral_mono hLeft hRight hPoint
  have hLeftIntegral :
      (∫ ω, w ω * (s * g ω - Real.log M - Real.log (w ω)) ∂μ) =
        s * (∫ ω, w ω * g ω ∂μ) -
          Real.log M * (∫ ω, w ω ∂μ) -
          (∫ ω, w ω * Real.log (w ω) ∂μ) := by
    have hEq :
        (fun ω => w ω * (s * g ω - Real.log M - Real.log (w ω))) =
          fun ω => s * (w ω * g ω) - Real.log M * w ω -
            w ω * Real.log (w ω) := by
      funext ω
      ring
    have hA : Integrable (fun ω => s * (w ω * g ω)) μ := hMoment.const_mul s
    have hB : Integrable (fun ω => Real.log M * w ω) μ := hw.const_mul (Real.log M)
    calc
      _ = ∫ ω, s * (w ω * g ω) - Real.log M * w ω -
          w ω * Real.log (w ω) ∂μ := by rw [hEq]
      _ = (∫ ω, s * (w ω * g ω) - Real.log M * w ω ∂μ) -
          ∫ ω, w ω * Real.log (w ω) ∂μ :=
        integral_sub (hA.sub hB) hEntropy
      _ = (s * (∫ ω, w ω * g ω ∂μ) - Real.log M * (∫ ω, w ω ∂μ)) -
          ∫ ω, w ω * Real.log (w ω) ∂μ := by
        rw [integral_sub hA hB, integral_const_mul, integral_const_mul]
  have hRightIntegral :
      (∫ ω, Real.exp (s * g ω) / M - w ω ∂μ) = 0 := by
    have hExpOver : Integrable (fun ω => Real.exp (s * g ω) / M) μ := by
      simpa only [div_eq_mul_inv] using hExp.mul_const M⁻¹
    calc
      _ = (∫ ω, Real.exp (s * g ω) / M ∂μ) - ∫ ω, w ω ∂μ :=
        integral_sub hExpOver hw
      _ = (∫ ω, Real.exp (s * g ω) ∂μ) / M - ∫ ω, w ω ∂μ := by
        rw [integral_div M]
      _ = 0 := by rw [← hM, hwone]; field_simp [hMpos.ne']; norm_num
  rw [hLeftIntegral, hRightIntegral, hwone] at hIntegral
  linarith

private theorem datasetNormSq_nonneg {k m n : ℕ}
    (D : Dataset (Observation k m) n) : 0 ≤ datasetNormSq D := by
  unfold datasetNormSq
  apply Finset.sum_nonneg
  intro i hi
  unfold observationNormSq
  apply add_nonneg
  · exact Finset.sum_nonneg fun j hj => sq_nonneg ((D i).1 j)
  · exact Finset.sum_nonneg fun j hj => sq_nonneg ((D i).2 j)

/-- Variational bound for `datasetNormSq` under the normalized exponential tilt.
The `hNormExp` premise is the finite norm-MGF input expected from the future
`lemma:norm` provider. The tilted norm moment is a second explicit finite input;
boundedness of `F` supplies the finite entropy integral. -/
theorem datasetNormSq_tilt_variational_inequality
    {k m n : ℕ} {μ : Measure (Dataset (Observation k m) n)}
    [IsProbabilityMeasure μ] (F : Dataset (Observation k m) n → ℝ)
    (hFmeas : Measurable F) {B t s : ℝ}
    (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B) (hs : 0 < s)
    (hNormExp : Integrable
      (fun D => Real.exp (s * datasetNormSq D)) μ)
    (hTiltMoment : Integrable
      (fun D => tiltDensity μ F t D * datasetNormSq D) μ) :
    s * (∫ D, tiltDensity μ F t D * datasetNormSq D ∂μ) ≤
      tiltEntropy μ F t +
        Real.log (∫ D, Real.exp (s * datasetNormSq D) ∂μ) := by
  have hZpos := tiltPartition_pos (μ := μ) hFmeas hB hF (t := t)
  have hDensityPos : ∀ D, 0 < tiltDensity μ F t D := by
    intro D
    exact div_pos (Real.exp_pos _) hZpos
  have hDensityInt := integrable_tiltDensity
    hFmeas hB hF (μ := μ) (t := t)
  have hTiltEntropy := integrable_tiltEntropy_integrand
    hFmeas hB hF (μ := μ) (t := t)
  have hDensityOne := tiltDensity_integral_eq_one (μ := μ) hFmeas hB hF (t := t)
  have hMpos : 0 < ∫ D, Real.exp (s * datasetNormSq D) ∂μ := by
    have hLower :
        (∫ _D, (1 : ℝ) ∂μ) ≤
          ∫ D, Real.exp (s * datasetNormSq D) ∂μ :=
    integral_mono (integrable_const 1) hNormExp (fun D => by
        calc
          1 = Real.exp 0 := by simp
          _ ≤ Real.exp (s * datasetNormSq D) :=
            Real.exp_le_exp.mpr (mul_nonneg hs.le (datasetNormSq_nonneg D)))
    rw [integral_const, probReal_univ, one_smul] at hLower
    exact lt_of_lt_of_le zero_lt_one hLower
  have hVariational := probability_density_variational_inequality
    (μ := μ) (w := tiltDensity μ F t) (g := datasetNormSq)
    hDensityPos hDensityInt hDensityOne hNormExp hMpos rfl
    hTiltMoment hTiltEntropy
  simpa [tiltEntropy] using hVariational

end
end LOOConcentration
