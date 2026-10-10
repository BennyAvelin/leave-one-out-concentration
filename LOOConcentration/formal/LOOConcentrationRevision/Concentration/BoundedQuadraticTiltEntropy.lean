import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
import LOOConcentration.Concentration.EntropyVariational
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.Concentration.TiltedNormMoment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory
open InnerProductSpace

namespace LOOConcentration.Revision

noncomputable section

private theorem gradient_exp_const_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a : ℝ)
    (x : EuclideanSpace ℝ ι) :
    gradient (fun y => Real.exp (a * F y)) x =
      (a * Real.exp (a * F x)) • gradient F x := by
  rw [gradient, gradient]
  have hd : DifferentiableAt ℝ F x := hF.contDiffAt.differentiableAt (by simp)
  rw [fderiv_exp (hd.const_mul a), fderiv_const_mul hd a]
  simp only [map_smul, smul_smul]
  congr 1
  ring

private theorem integrable_sq_gradient_of_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖gradient F x‖ ≤ B) :
    Integrable (fun x => ‖gradient F x‖ ^ 2) μ := by
  let E := EuclideanSpace ℝ ι
  have hgradCont : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hmeas : Measurable (fun x : E => ‖gradient F x‖ ^ 2) :=
    (hgradCont.norm.pow 2).measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 2) ?_
  filter_upwards with x
  change |‖gradient F x‖ ^ 2| ≤ B ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x)

private theorem tiltEntropy_eq_looconcentrationEntropy_exp_div
    {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} [IsProbabilityMeasure μ]
    {F : ι → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    LOOConcentration.tiltEntropy μ F t =
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (t * F x)) /
        LOOConcentration.tiltPartition μ F t := by
  let w : ι → ℝ := fun x => Real.exp (t * F x)
  have hZ : 0 < LOOConcentration.tiltPartition μ F t :=
    LOOConcentration.tiltPartition_pos hFmeas hB hF
  have hIpos : 0 < (∫ x, Real.exp (t * F x) ∂μ) := by
    simpa [LOOConcentration.tiltPartition] using hZ
  have hW : Integrable w μ :=
    LOOConcentration.logPartition_integrable hFmeas hF
  have hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ B := by
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hF x
  have hWF : Integrable (fun x => w x * F x) μ := by
    convert hW.bdd_mul hFmeas.aestronglyMeasurable hFbound using 1
    ext x
    ring
  have hWlog : (∫ x, w x * Real.log (w x) ∂μ) =
      t * (∫ x, F x * Real.exp (t * F x) ∂μ) := by
    calc
      (∫ x, w x * Real.log (w x) ∂μ) =
          ∫ x, t * (F x * Real.exp (t * F x)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [w, Real.log_exp]
            ring
      _ = t * (∫ x, F x * Real.exp (t * F x) ∂μ) := integral_const_mul t _
  have hMean :
      (∫ x, LOOConcentration.tiltDensity μ F t x * F x ∂μ) =
        (∫ x, F x * Real.exp (t * F x) ∂μ) /
          LOOConcentration.tiltPartition μ F t := by
    calc
      (∫ x, LOOConcentration.tiltDensity μ F t x * F x ∂μ) =
          ∫ x, (F x * Real.exp (t * F x)) *
            (LOOConcentration.tiltPartition μ F t)⁻¹ ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              simp [LOOConcentration.tiltDensity, div_eq_mul_inv]
              ring
      _ = (∫ x, F x * Real.exp (t * F x) ∂μ) *
            (LOOConcentration.tiltPartition μ F t)⁻¹ := integral_mul_const _ _
      _ = _ := by rw [div_eq_mul_inv]
  rw [LOOConcentration.tiltEntropy_eq_tiltMean_sub_logPartition
    hFmeas hB hF, hMean]
  unfold LOOConcentration.looconcentrationEntropy
  dsimp [w]
  rw [hWlog, LOOConcentration.tiltPartition]
  field_simp [ne_of_gt hIpos]

/-- The actual smooth tilted entropy is controlled by the same admissible
log-Sobolev constant and the actual squared gradient under its own tilt. -/
theorem bounded_smooth_tilt_entropy_gradient_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hFbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (lam : ℝ) :
    LOOConcentration.tiltEntropy μ F lam ≤
      (C * lam ^ 2 / 2) *
        (∫ x, LOOConcentration.tiltDensity μ F lam x *
          ‖gradient F x‖ ^ 2 ∂μ) := by
  let a : ℝ := lam / 2
  let G : EuclideanSpace ℝ ι → ℝ := fun x => Real.exp (a * F x)
  let A : ℝ := Real.exp (|a| * B)
  let D : ℝ := |a| * A * B
  have hA : 0 ≤ A := Real.exp_nonneg _
  have hD : 0 ≤ D := by positivity
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    dsimp [G]
    fun_prop
  have hFmeas : Measurable F := hF.continuous.measurable
  have hGbound : ∀ x, |G x| ≤ A ∧ ‖gradient G x‖ ≤ D := by
    intro x
    have hExp : Real.exp (a * F x) ≤ A := by
      apply Real.exp_le_exp.mpr
      calc
        a * F x ≤ |a * F x| := le_abs_self _
        _ = |a| * |F x| := abs_mul _ _
        _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hFbound x).1 (abs_nonneg _)
    have hGabs : |G x| ≤ A := by
      dsimp [G]
      rw [abs_of_pos (Real.exp_pos _)]
      exact hExp
    have hgradEq := gradient_exp_const_mul_eq hF a x
    have hgradNorm : ‖gradient G x‖ = |a| * Real.exp (a * F x) * ‖gradient F x‖ := by
      rw [hgradEq, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hgrad : ‖gradient G x‖ ≤ D := by
      rw [hgradNorm]
      calc
        |a| * Real.exp (a * F x) * ‖gradient F x‖ ≤
            |a| * Real.exp (a * F x) * B :=
          mul_le_mul_of_nonneg_left (hFbound x).2 (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
        _ ≤ |a| * A * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact mul_le_mul_of_nonneg_left hExp (abs_nonneg _)
        _ = D := rfl
    exact ⟨hGabs, hgrad⟩
  let J : ℝ := A + D
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hGpair : ∀ x, |G x| ≤ J ∧ ‖gradient G x‖ ≤ J := by
    intro x
    exact ⟨(hGbound x).1.trans (le_add_of_nonneg_right hD),
      (hGbound x).2.trans (le_add_of_nonneg_left hA)⟩
  have hBase := bounded_smooth_entropy_le_of_logSobolevConstant_le
    μ C hC hLC G hGsmooth J hJ hGpair
  change LOOConcentration.looconcentrationEntropy μ (fun x => G x ^ 2) ≤
    2 * C * ∫ x, ‖gradient G x‖ ^ 2 ∂μ at hBase
  have hGsq : (fun x => G x ^ 2) = fun x => Real.exp (lam * F x) := by
    funext x
    dsimp [G, a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hGsq] at hBase
  have hGradFCont : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hWeightedMeas : Measurable (fun x : EuclideanSpace ℝ ι =>
      Real.exp (lam * F x) * ‖gradient F x‖ ^ 2) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul hF.continuous)).mul
      (hGradFCont.norm.pow 2)).measurable
  have hWeightedInt : Integrable (fun x : EuclideanSpace ℝ ι =>
      Real.exp (lam * F x) * ‖gradient F x‖ ^ 2) μ := by
    let K := Real.exp (|lam| * B) * B ^ 2
    refine Integrable.of_bound hWeightedMeas.aestronglyMeasurable K ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    have hExp : Real.exp (lam * F x) ≤ Real.exp (|lam| * B) := by
      apply Real.exp_le_exp.mpr
      calc
        lam * F x ≤ |lam * F x| := le_abs_self _
        _ = |lam| * |F x| := abs_mul _ _
        _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hFbound x).1 (abs_nonneg _)
    have hGrad : ‖gradient F x‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hB).2 (hFbound x).2
    calc
      Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ≤
          Real.exp (lam * F x) * B ^ 2 :=
        mul_le_mul_of_nonneg_left hGrad (Real.exp_nonneg _)
      _ ≤ Real.exp (|lam| * B) * B ^ 2 :=
        mul_le_mul_of_nonneg_right hExp (sq_nonneg _)
  have hGradGInt := integrable_sq_gradient_of_bound μ G hGsmooth hJ
    (fun x => (hGpair x).2)
  have hExpSq (x : EuclideanSpace ℝ ι) :
      Real.exp (a * F x) ^ 2 = Real.exp (lam * F x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  have hEnergyPoint (x : EuclideanSpace ℝ ι) :
      ‖gradient G x‖ ^ 2 = (lam ^ 2 / 4) *
        (Real.exp (lam * F x) * ‖gradient F x‖ ^ 2) := by
    rw [gradient_exp_const_mul_eq hF a x, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _), mul_pow, mul_pow, sq_abs, hExpSq]
    dsimp [a]
    ring
  have hEnergy :
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤
        (lam ^ 2 / 4) * ∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ := by
    calc
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤
          ∫ x, (lam ^ 2 / 4) *
            (Real.exp (lam * F x) * ‖gradient F x‖ ^ 2) ∂μ :=
        integral_mono hGradGInt (hWeightedInt.const_mul (lam ^ 2 / 4))
          (fun x => le_of_eq (hEnergyPoint x))
      _ = (lam ^ 2 / 4) *
          ∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ := integral_const_mul _ _
  have hRaw : LOOConcentration.looconcentrationEntropy μ
      (fun x => Real.exp (lam * F x)) ≤
      (2 * C) * ((lam ^ 2 / 4) *
        ∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ) := by
    calc
      _ ≤ 2 * C * ∫ x, ‖gradient G x‖ ^ 2 ∂μ := hBase
      _ ≤ (2 * C) * ((lam ^ 2 / 4) *
          ∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hEnergy (by positivity)
  have hZ : 0 < LOOConcentration.tiltPartition μ F lam :=
    LOOConcentration.tiltPartition_pos hFmeas (B := B) hB (fun x => (hFbound x).1)
  have hWeightedTilt :
      (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖gradient F x‖ ^ 2 ∂μ) =
        (∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ) /
          LOOConcentration.tiltPartition μ F lam := by
    calc
      (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖gradient F x‖ ^ 2 ∂μ) =
          ∫ x, (Real.exp (lam * F x) * ‖gradient F x‖ ^ 2) *
            (LOOConcentration.tiltPartition μ F lam)⁻¹ ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              simp [LOOConcentration.tiltDensity, div_eq_mul_inv]
              ring
      _ = (∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ) *
            (LOOConcentration.tiltPartition μ F lam)⁻¹ := integral_mul_const _ _
      _ = _ := by rw [div_eq_mul_inv]
  have hDiv : LOOConcentration.looconcentrationEntropy μ
      (fun x => Real.exp (lam * F x)) /
        LOOConcentration.tiltPartition μ F lam ≤
      (C * lam ^ 2 / 2) *
        (∫ x, LOOConcentration.tiltDensity μ F lam x *
          ‖gradient F x‖ ^ 2 ∂μ) := by
    rw [hWeightedTilt]
    calc
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (lam * F x)) /
          LOOConcentration.tiltPartition μ F lam ≤
        ((2 * C) * ((lam ^ 2 / 4) *
            ∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ)) /
          LOOConcentration.tiltPartition μ F lam :=
        div_le_div_of_nonneg_right hRaw hZ.le
      _ = (C * lam ^ 2 / 2) *
            ((∫ x, Real.exp (lam * F x) * ‖gradient F x‖ ^ 2 ∂μ) /
              LOOConcentration.tiltPartition μ F lam) := by field_simp [ne_of_gt hZ]; ring
  calc
    LOOConcentration.tiltEntropy μ F lam =
        LOOConcentration.looconcentrationEntropy μ
          (fun x => Real.exp (lam * F x)) /
            LOOConcentration.tiltPartition μ F lam :=
      tiltEntropy_eq_looconcentrationEntropy_exp_div hFmeas hB
        (fun x => (hFbound x).1)
    _ ≤ (C * lam ^ 2 / 2) *
        (∫ x, LOOConcentration.tiltDensity μ F lam x *
          ‖gradient F x‖ ^ 2 ∂μ) := hDiv

/-- The affine-growth form of the actual smooth tilted entropy estimate. The
tilted norm moment is integrated against the same normalized density. -/
theorem bounded_smooth_tilt_entropy_affine_growth_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hFbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (a b : NNReal)
    (hGrowth : ∀ x, ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (lam : ℝ) :
    LOOConcentration.tiltEntropy μ F lam ≤
      C * lam ^ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 *
        (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ)) := by
  have hEntropy := bounded_smooth_tilt_entropy_gradient_bound μ C hC hLC F hF B hB
    hFbound lam
  have hFmeas : Measurable F := hF.continuous.measurable
  have hGradCont : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hGradSqMeas : Measurable (fun x : EuclideanSpace ℝ ι =>
      ‖gradient F x‖ ^ 2) := (hGradCont.norm.pow 2).measurable
  have hGradSqInt := integrable_sq_gradient_of_bound μ F hF hB (fun x => (hFbound x).2)
  have hGradTiltInt : Integrable
      (fun x => LOOConcentration.tiltDensity μ F lam x * ‖gradient F x‖ ^ 2) μ :=
    LOOConcentration.integrable_tiltDensity_mul_of_nonneg_integrable
      (μ := μ) (F := F) (Q := fun x => ‖gradient F x‖ ^ 2) hFmeas hB
      (fun x => (hFbound x).1) hGradSqMeas (fun x => sq_nonneg _) hGradSqInt
  have hNormSqMeas : Measurable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) := by fun_prop
  have hNormTiltInt : Integrable
      (fun x => LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2) μ :=
    LOOConcentration.integrable_tiltDensity_mul_of_nonneg_integrable
      (μ := μ) (F := F) (Q := fun x => ‖x‖ ^ 2) hFmeas hB
      (fun x => (hFbound x).1) hNormSqMeas (fun x => sq_nonneg _) hM2
  have hDensityInt : Integrable (LOOConcentration.tiltDensity μ F lam) μ := by
    have h := LOOConcentration.integrable_tiltDensity_mul_of_nonneg_integrable
      (μ := μ) (F := F) (Q := fun _ : EuclideanSpace ℝ ι => (1 : ℝ))
      (t := lam) hFmeas hB (fun x => (hFbound x).1) measurable_const (fun _ => le_of_lt one_pos)
      (integrable_const (1 : ℝ))
    simpa only [mul_one] using h
  have hDensityOne : ∫ x, LOOConcentration.tiltDensity μ F lam x ∂μ = 1 :=
    LOOConcentration.tiltDensity_integral_eq_one
      (μ := μ) (F := F) hFmeas hB (fun x => (hFbound x).1)
  have hDensityNonneg (x : EuclideanSpace ℝ ι) :
      0 ≤ LOOConcentration.tiltDensity μ F lam x := by
    exact div_nonneg (Real.exp_nonneg _) (LOOConcentration.tiltPartition_pos
      (μ := μ) (F := F) hFmeas hB (fun x => (hFbound x).1)).le
  have hAInt : Integrable
      (fun x => LOOConcentration.tiltDensity μ F lam x * (2 * (a : ℝ) ^ 2)) μ :=
    hDensityInt.mul_const _
  have hBInt : Integrable
      (fun x => LOOConcentration.tiltDensity μ F lam x *
        (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2)) μ := by
    have h := hNormTiltInt.const_mul (2 * (b : ℝ) ^ 2)
    refine h.congr ?_
    filter_upwards with x
    ring
  have hMajorInt : Integrable (fun x => LOOConcentration.tiltDensity μ F lam x *
      (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2)) μ := by
    have heq : (fun x => LOOConcentration.tiltDensity μ F lam x *
        (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2)) =
        (fun x => LOOConcentration.tiltDensity μ F lam x * (2 * (a : ℝ) ^ 2)) +
        (fun x => LOOConcentration.tiltDensity μ F lam x *
          (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2)) := by
      funext x
      change LOOConcentration.tiltDensity μ F lam x *
          (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) =
        LOOConcentration.tiltDensity μ F lam x * (2 * (a : ℝ) ^ 2) +
          LOOConcentration.tiltDensity μ F lam x *
            (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2)
      ring
    rw [heq]
    exact hAInt.add hBInt
  have hPoint (x : EuclideanSpace ℝ ι) :
      LOOConcentration.tiltDensity μ F lam x * ‖gradient F x‖ ^ 2 ≤
        LOOConcentration.tiltDensity μ F lam x *
          (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) := by
    have hRight : 0 ≤ (a : ℝ) + (b : ℝ) * ‖x‖ := by positivity
    have hSquare : ‖gradient F x‖ ^ 2 ≤
        2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2 := by
      have hs := (sq_le_sq₀ (norm_nonneg _) hRight).2 (hGrowth x)
      nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ) * ‖x‖)]
    exact mul_le_mul_of_nonneg_left hSquare (hDensityNonneg x)
  have hMomentUpper :
      (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖gradient F x‖ ^ 2 ∂μ) ≤
        2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
          (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ x, LOOConcentration.tiltDensity μ F lam x *
          (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) ∂μ :=
        integral_mono hGradTiltInt hMajorInt hPoint
      _ = (∫ x, LOOConcentration.tiltDensity μ F lam x *
                (2 * (a : ℝ) ^ 2) ∂μ) +
              (∫ x, LOOConcentration.tiltDensity μ F lam x *
                (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) ∂μ) := by
            calc
              _ = ∫ x, LOOConcentration.tiltDensity μ F lam x *
                    (2 * (a : ℝ) ^ 2) + LOOConcentration.tiltDensity μ F lam x *
                      (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                ring
              _ = _ := integral_add hAInt hBInt
          _ = (∫ x, LOOConcentration.tiltDensity μ F lam x ∂μ) *
                (2 * (a : ℝ) ^ 2) +
              2 * (b : ℝ) ^ 2 *
                (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ) := by
            rw [integral_mul_const]
            congr 1
            calc
              (∫ x, LOOConcentration.tiltDensity μ F lam x *
                  (2 * (b : ℝ) ^ 2 * ‖x‖ ^ 2) ∂μ) =
                  ∫ x, (2 * (b : ℝ) ^ 2) *
                    (LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2) ∂μ := by
                      apply integral_congr_ae
                      filter_upwards with x
                      ring
              _ = 2 * (b : ℝ) ^ 2 *
                  (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ) :=
                    integral_const_mul _ _
          _ = _ := by rw [hDensityOne]; ring
  have hCoeff : 0 ≤ C * lam ^ 2 / 2 := by positivity
  calc
    LOOConcentration.tiltEntropy μ F lam ≤
        (C * lam ^ 2 / 2) *
          (∫ x, LOOConcentration.tiltDensity μ F lam x *
            ‖gradient F x‖ ^ 2 ∂μ) := hEntropy
    _ ≤ (C * lam ^ 2 / 2) *
          (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
            (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hMomentUpper hCoeff
    _ = C * lam ^ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 *
          (∫ x, LOOConcentration.tiltDensity μ F lam x * ‖x‖ ^ 2 ∂μ)) := by ring

end

end LOOConcentration.Revision
