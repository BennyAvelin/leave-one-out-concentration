import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open InnerProductSpace
open scoped ENNReal

private theorem regularizedPower_contDiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε q : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F x ^ 2 + ε) ^ (q / 4)) := by
  have hBase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => F x ^ 2 + ε) := (hF.pow 2).add contDiff_const
  exact hBase.rpow_const_of_ne (fun x => ne_of_gt (by positivity))

private theorem regularizedPower_fderiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε q : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y => (F y ^ 2 + ε) ^ (q / 4)) x =
      ((q / 2) * F x * (F x ^ 2 + ε) ^ (q / 4 - 1)) • fderiv ℝ F x := by
  have hFx : DifferentiableAt ℝ F x := hF.contDiffAt.differentiableAt (by simp)
  have hRx : DifferentiableAt ℝ (fun y => F y ^ 2 + ε) x :=
    (hFx.pow 2).add_const ε
  have hRderiv : fderiv ℝ (fun y => F y ^ 2 + ε) x =
      (2 * F x) • fderiv ℝ F x := by
    rw [fderiv_add_const, fderiv_fun_pow 2 hFx]
    norm_num [pow_one]
  have hRpos : 0 < F x ^ 2 + ε := by positivity
  have hPderiv := hRx.hasFDerivAt.rpow_const
    (p := q / 4) (Or.inl (ne_of_gt hRpos))
  rw [hPderiv.fderiv, hRderiv, smul_smul]
  congr 1
  ring

private theorem regularizedPower_gradient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε q : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    gradient (fun y => (F y ^ 2 + ε) ^ (q / 4)) x =
      ((q / 2) * F x * (F x ^ 2 + ε) ^ (q / 4 - 1)) • gradient F x := by
  rw [gradient, gradient, regularizedPower_fderiv F hF ε q hε x]
  simp only [map_smul]

private theorem regularizedPower_gradient_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε q : ℝ) (hε : 0 < ε) (hq : 2 < q)
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (fun y => (F y ^ 2 + ε) ^ (q / 4)) x‖ ^ 2 ≤
      (q ^ 2 / 4) * (F x ^ 2 + ε) ^ (q / 2 - 1) * ‖gradient F x‖ ^ 2 := by
  let α : ℝ := q / 4 - 1
  let β : ℝ := q / 2 - 2
  have hRpos : 0 < F x ^ 2 + ε := by positivity
  have hRnonneg : 0 ≤ F x ^ 2 + ε := hRpos.le
  have hGradSq :
      ‖gradient (fun y => (F y ^ 2 + ε) ^ (q / 4)) x‖ ^ 2 =
        (q ^ 2 / 4) * F x ^ 2 * (F x ^ 2 + ε) ^ β * ‖gradient F x‖ ^ 2 := by
    rw [regularizedPower_gradient F hF ε q hε x, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ q / 2),
      abs_of_nonneg (Real.rpow_nonneg hRnonneg _)]
    have hPow : ((F x ^ 2 + ε) ^ α) ^ 2 = (F x ^ 2 + ε) ^ β := by
      calc
        ((F x ^ 2 + ε) ^ α) ^ 2 = ((F x ^ 2 + ε) ^ α) ^ (2 : ℝ) := by
          rw [← Real.rpow_two]
        _ = (F x ^ 2 + ε) ^ (α * 2) :=
          (Real.rpow_mul hRnonneg α (2 : ℝ)).symm
        _ = (F x ^ 2 + ε) ^ β := by congr 1; dsimp [α, β]; ring
    have hPow' : ((F x ^ 2 + ε) ^ (q / 4 - 1)) ^ 2 =
        (F x ^ 2 + ε) ^ (q / 2 - 2) := by simpa [α, β] using hPow
    simp only [mul_pow]
    rw [sq_abs, hPow']
    ring
  have hFle : F x ^ 2 ≤ F x ^ 2 + ε := by linarith
  have hpowPos : 0 ≤ (F x ^ 2 + ε) ^ β := Real.rpow_nonneg hRnonneg _
  have hinner : F x ^ 2 * (F x ^ 2 + ε) ^ β ≤
      (F x ^ 2 + ε) * (F x ^ 2 + ε) ^ β :=
    mul_le_mul_of_nonneg_right hFle hpowPos
  have hRadd : (F x ^ 2 + ε) * (F x ^ 2 + ε) ^ β =
      (F x ^ 2 + ε) ^ (q / 2 - 1) := by
    calc
      (F x ^ 2 + ε) * (F x ^ 2 + ε) ^ β =
          (F x ^ 2 + ε) ^ (1 : ℝ) * (F x ^ 2 + ε) ^ β := by rw [Real.rpow_one]
      _ = (F x ^ 2 + ε) ^ ((1 : ℝ) + β) := (Real.rpow_add hRpos _ _).symm
      _ = (F x ^ 2 + ε) ^ (q / 2 - 1) := by congr 1; dsimp [β]; ring
  rw [hGradSq]
  have hcoeff : 0 ≤ q ^ 2 / 4 := by positivity
  calc
    (q ^ 2 / 4) * F x ^ 2 * (F x ^ 2 + ε) ^ β * ‖gradient F x‖ ^ 2 =
        (q ^ 2 / 4) * (F x ^ 2 * (F x ^ 2 + ε) ^ β) * ‖gradient F x‖ ^ 2 := by ring
    _ ≤ (q ^ 2 / 4) * ((F x ^ 2 + ε) * (F x ^ 2 + ε) ^ β) *
          ‖gradient F x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner hcoeff) (sq_nonneg ‖gradient F x‖)
    _ = (q ^ 2 / 4) * (F x ^ 2 + ε) ^ (q / 2 - 1) * ‖gradient F x‖ ^ 2 := by
      rw [hRadd]

/-- For the actual bounded smooth generator, the power profile
`(F^2+epsilon)^(q/4)` is itself a bounded smooth generator.  Its exact
chain-rule derivative, the pointwise inequality `F^2 ≤ F^2+epsilon`, and the
same-constant generator LSI give the literal entropy bound with coefficient
`C*q^2/2`. -/
theorem bounded_smooth_regularized_power_entropy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (ε q : ℝ) (hε : 0 < ε) (hq : 2 < q) :
    (∫ x, (F x ^ 2 + ε) ^ (q / 2) *
        Real.log ((F x ^ 2 + ε) ^ (q / 2)) ∂μ) -
      (∫ x, (F x ^ 2 + ε) ^ (q / 2) ∂μ) *
        Real.log (∫ x, (F x ^ 2 + ε) ^ (q / 2) ∂μ) ≤
      (C * q ^ 2 / 2) *
        ∫ x, (F x ^ 2 + ε) ^ (q / 2 - 1) * ‖gradient F x‖ ^ 2 ∂μ := by
  let R : EuclideanSpace ℝ ι → ℝ := fun x => F x ^ 2 + ε
  let P : EuclideanSpace ℝ ι → ℝ := fun x => R x ^ (q / 4)
  let W : EuclideanSpace ℝ ι → ℝ := fun x => R x ^ (q / 2 - 1) * ‖gradient F x‖ ^ 2
  let Rmax : ℝ := B ^ 2 + ε
  let α : ℝ := q / 4 - 1
  let γ : ℝ := q / 2 - 1
  have hq4 : 0 < q / 4 := by positivity
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hRmax : 0 < Rmax := by dsimp [Rmax]; positivity
  have hRbounds (x : EuclideanSpace ℝ ι) : ε ≤ R x ∧ R x ≤ Rmax := by
    constructor
    · dsimp [R]
      nlinarith [sq_nonneg (F x)]
    · dsimp [R, Rmax]
      have hsq : F x ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg (F x)) hB).2 (hbound x).1
      linarith
  have hRpos (x : EuclideanSpace ℝ ι) : 0 < R x := lt_of_lt_of_le hε (hRbounds x).1
  have hRpowBound (x : EuclideanSpace ℝ ι) :
      R x ^ (q / 4) ≤ Rmax ^ (q / 4) :=
    Real.rpow_le_rpow (by positivity) (hRbounds x).2 (by linarith)
  have hAlphaBound (x : EuclideanSpace ℝ ι) :
      R x ^ α ≤ max (ε ^ α) (Rmax ^ α) := by
    by_cases hα : 0 ≤ α
    · exact (Real.rpow_le_rpow (by positivity) (hRbounds x).2 hα).trans (le_max_right _ _)
    · have hα' : α ≤ 0 := le_of_not_ge hα
      exact (Real.rpow_le_rpow_of_nonpos hε (hRbounds x).1 hα').trans (le_max_left _ _)
  let Kp : ℝ := Rmax ^ (q / 4)
  let Kg : ℝ := (q / 2) * B * max (ε ^ α) (Rmax ^ α) * B
  let K : ℝ := max Kp Kg
  have hKp : 0 ≤ Kp := by dsimp [Kp]; positivity
  have hKg : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hPcontDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P := by
    simpa [P, R] using regularizedPower_contDiff F hF ε q hε
  have hGradFcont : Continuous (gradient F) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hGradPcont : Continuous (gradient P) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hPcontDiff.continuous_fderiv (by simp))
  have hPbound (x : EuclideanSpace ℝ ι) : |P x| ≤ K ∧ ‖gradient P x‖ ≤ K := by
    constructor
    · rw [abs_of_pos (Real.rpow_pos_of_pos (hRpos x) _)]
      exact (hRpowBound x).trans (le_max_left _ _)
    · rw [regularizedPower_gradient F hF ε q hε x, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ q / 2),
        abs_of_nonneg (Real.rpow_nonneg (hRpos x).le _)]
      calc
        (q / 2) * |F x| * R x ^ α * ‖gradient F x‖ ≤
            (q / 2) * B * max (ε ^ α) (Rmax ^ α) * B := by
          gcongr
          · exact (hbound x).1
          · exact hAlphaBound x
          · exact (hbound x).2
        _ = Kg := rfl
        _ ≤ K := le_max_right _ _
  have hBaseLSI := bounded_smooth_entropy_le_of_logSobolevConstant_le
    μ C hC hLC P hPcontDiff K hK hPbound
  have hGradPSqInt : Integrable (fun x => ‖gradient P x‖ ^ 2) μ := by
    have hMem : MemLp (gradient P) 2 μ :=
      MemLp.of_bound hGradPcont.aestronglyMeasurable K
        (Filter.Eventually.of_forall fun x => (hPbound x).2)
    exact (memLp_two_iff_integrable_sq_norm hMem.aestronglyMeasurable).mp hMem
  have hWcont : Continuous W := by
    have hBase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := by
      dsimp [R]
      exact (hF.pow 2).add contDiff_const
    have hPow : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => R x ^ γ) :=
      hBase.rpow_const_of_ne (fun x => ne_of_gt (hRpos x))
    dsimp [W]
    exact hPow.continuous.mul (hGradFcont.norm.pow 2)
  have hWbound (x : EuclideanSpace ℝ ι) : ‖W x‖ ≤ Rmax ^ γ * B ^ 2 := by
    have hpow : R x ^ γ ≤ Rmax ^ γ :=
      Real.rpow_le_rpow (by positivity) (hRbounds x).2 (by linarith)
    have hGradSq : ‖gradient F x‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x).2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hRpos x).le _) (sq_nonneg _))]
    exact mul_le_mul hpow hGradSq (sq_nonneg ‖gradient F x‖) (Real.rpow_nonneg hRmax.le _)
  have hWInt : Integrable W μ :=
    (integrable_const (Rmax ^ γ * B ^ 2)).mono' hWcont.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hWbound)
  have hPowerEnergy :
      (∫ x, ‖gradient P x‖ ^ 2 ∂μ) ≤ (q ^ 2 / 4) * ∫ x, W x ∂μ := by
    calc
      _ ≤ ∫ x, (q ^ 2 / 4) * W x ∂μ :=
        integral_mono_ae hGradPSqInt (hWInt.const_mul (q ^ 2 / 4))
          (Filter.Eventually.of_forall fun x => by
            simpa [P, R, W, mul_assoc] using
              regularizedPower_gradient_sq_le F hF ε q hε hq x)
      _ = (q ^ 2 / 4) * ∫ x, W x ∂μ := integral_const_mul _ _
  have hEntropyRewrite :
      (∫ x, P x ^ 2 * Real.log (P x ^ 2) ∂μ) -
          (∫ x, P x ^ 2 ∂μ) * Real.log (∫ x, P x ^ 2 ∂μ) =
        (∫ x, R x ^ (q / 2) * Real.log (R x ^ (q / 2)) ∂μ) -
          (∫ x, R x ^ (q / 2) ∂μ) * Real.log (∫ x, R x ^ (q / 2) ∂μ) := by
    have hpow (x : EuclideanSpace ℝ ι) : P x ^ 2 = R x ^ (q / 2) := by
      dsimp [P]
      calc
        (R x ^ (q / 4)) ^ 2 = (R x ^ (q / 4)) ^ (2 : ℝ) := by rw [← Real.rpow_two]
        _ = R x ^ ((q / 4) * 2) := (Real.rpow_mul (hRpos x).le _ _).symm
        _ = R x ^ (q / 2) := by congr 1; ring
    have hDensity :
        (∫ x, P x ^ 2 * Real.log (P x ^ 2) ∂μ) =
          ∫ x, R x ^ (q / 2) * Real.log (R x ^ (q / 2)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change P x ^ 2 * Real.log (P x ^ 2) =
          R x ^ (q / 2) * Real.log (R x ^ (q / 2))
        rw [hpow x])
    have hMass : (∫ x, P x ^ 2 ∂μ) = ∫ x, R x ^ (q / 2) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change P x ^ 2 = R x ^ (q / 2)
        exact hpow x)
    rw [hDensity, hMass]
  calc
    _ = (∫ x, P x ^ 2 * Real.log (P x ^ 2) ∂μ) -
        (∫ x, P x ^ 2 ∂μ) * Real.log (∫ x, P x ^ 2 ∂μ) := by
          simpa [P, R] using hEntropyRewrite.symm
    _ ≤ 2 * C * ∫ x, ‖gradient P x‖ ^ 2 ∂μ := hBaseLSI
    _ ≤ 2 * C * ((q ^ 2 / 4) * ∫ x, W x ∂μ) :=
      mul_le_mul_of_nonneg_left hPowerEnergy (by positivity)
    _ = (C * q ^ 2 / 2) * ∫ x, W x ∂μ := by ring

#print axioms bounded_smooth_regularized_power_entropy_le

end LOOConcentration.Revision
