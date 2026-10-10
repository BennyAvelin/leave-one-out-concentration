import LOOConcentrationRevision.Concentration.NormCapGradient
import LOOConcentrationRevision.Concentration.NormEntropyDifferentialInequality
import LOOConcentrationRevision.Concentration.BoundedMgfCalculus
import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
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

/-- The actual norm-cap entropy inequality from the completed-pair LSI, with
the sharp source constant and no additional factor. -/
theorem norm_cap_entropy_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (N : ℝ) (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) :
    LOOConcentration.looconcentrationEntropy μ
        (fun x => Real.exp (s * (N * (1 - Real.exp (-‖x‖ ^ 2 / N)))) ) ≤
      2 * C * s ^ 2 * ∫ x,
        (N * (1 - Real.exp (-‖x‖ ^ 2 / N))) *
          Real.exp (s * (N * (1 - Real.exp (-‖x‖ ^ 2 / N)))) ∂μ := by
  let Q : EuclideanSpace ℝ ι → ℝ :=
    fun x => N * (1 - Real.exp (-‖x‖ ^ 2 / N))
  let a : ℝ := s / 2
  let G : EuclideanSpace ℝ ι → ℝ := fun x => Real.exp (a * Q x)
  let A : ℝ := Real.exp (a * N)
  let D : ℝ := s * Real.sqrt N * A
  let B : ℝ := A + D
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hA : 0 ≤ A := by positivity
  have hD : 0 ≤ D := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨hQsmooth', hQpoint', _⟩ := norm_cap_bounded_smooth
    (E := EuclideanSpace ℝ ι) N hN
  have hQsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q := by
    simpa only [Q] using hQsmooth'
  have hQpoint (x : EuclideanSpace ℝ ι) :
      0 ≤ Q x ∧ Q x ≤ N ∧ ‖gradient Q x‖ ^ 2 ≤ 4 * Q x := by
    simpa only [Q] using hQpoint' x
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    dsimp [G]
    exact Real.contDiff_exp.comp (contDiff_const.mul hQsmooth)
  have hgradQbound (x : EuclideanSpace ℝ ι) :
      ‖gradient Q x‖ ≤ 2 * Real.sqrt N := by
    have hsqrt : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
    have hsq : ‖gradient Q x‖ ^ 2 ≤ 4 * N :=
      (hQpoint x).2.2 |>.trans (mul_le_mul_of_nonneg_left
        (hQpoint x).2.1 (by norm_num))
    have hsq' : ‖gradient Q x‖ ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := by
      nlinarith [hsqrt]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq'
  have hGpair : ∀ x, |G x| ≤ B ∧ ‖gradient G x‖ ≤ B := by
    intro x
    have hExp : Real.exp (a * Q x) ≤ A := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (hQpoint x).2.1 ha
    have hGabs : |G x| ≤ A := by
      dsimp [G]
      rw [abs_of_pos (Real.exp_pos _)]
      exact hExp
    have hgradEq := gradient_exp_const_mul_eq hQsmooth a x
    have hgradNorm : ‖gradient G x‖ =
        a * Real.exp (a * Q x) * ‖gradient Q x‖ := by
      rw [hgradEq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ha (Real.exp_nonneg _))]
    have hgrad : ‖gradient G x‖ ≤ D := by
      rw [hgradNorm]
      calc
        a * Real.exp (a * Q x) * ‖gradient Q x‖ ≤
            a * Real.exp (a * Q x) * (2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (hgradQbound x)
            (mul_nonneg ha (Real.exp_nonneg _))
        _ ≤ a * A * (2 * Real.sqrt N) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hExp ha
        _ = D := by dsimp [D, a]; ring
    constructor
    · exact hGabs.trans (le_add_of_nonneg_right hD)
    · exact hgrad.trans (le_add_of_nonneg_left hA)
  have hBase := bounded_smooth_entropy_le_of_logSobolevConstant_le
    μ C hC hLC G hGsmooth B hB hGpair
  change LOOConcentration.looconcentrationEntropy μ
      (fun x => G x ^ 2) ≤ 2 * C * ∫ x, ‖gradient G x‖ ^ 2 ∂μ at hBase
  have hGsq : (fun x => G x ^ 2) = fun x => Real.exp (s * Q x) := by
    funext x
    dsimp [G, a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hGsq] at hBase
  have hMoment : Integrable
      (fun x : EuclideanSpace ℝ ι => Q x * Real.exp (s * Q x)) μ := by
    have hQmeas : Measurable Q := hQsmooth.continuous.measurable
    have hQbound : ∀ x, |Q x| ≤ N := by
      intro x
      rw [abs_of_nonneg (hQpoint x).1]
      exact (hQpoint x).2.1
    exact bounded_mgf_derivative_integrable Q hQmeas (B := N) (s := s)
      hN.le hQbound
  have hGradientIntegrable : Integrable
      (fun x : EuclideanSpace ℝ ι => ‖gradient G x‖ ^ 2) μ :=
    integrable_sq_gradient_of_bound μ G hGsmooth hB (fun x => (hGpair x).2)
  have hMajorIntegrable : Integrable
      (fun x : EuclideanSpace ℝ ι => s ^ 2 *
        (Q x * Real.exp (s * Q x))) μ := hMoment.const_mul (s ^ 2)
  have hEnergyPoint (x : EuclideanSpace ℝ ι) :
      ‖gradient G x‖ ^ 2 ≤ s ^ 2 * (Q x * Real.exp (s * Q x)) := by
    have hgradNorm : ‖gradient G x‖ =
        a * Real.exp (a * Q x) * ‖gradient Q x‖ := by
      rw [gradient_exp_const_mul_eq hQsmooth a x, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha (Real.exp_nonneg _))]
    have hExpSq : Real.exp (a * Q x) ^ 2 = Real.exp (s * Q x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    have hgradSquared :
        (a * Real.exp (a * Q x) * ‖gradient Q x‖) ^ 2 ≤
          s ^ 2 * (Q x * Real.exp (s * Q x)) := by
      calc
        (a * Real.exp (a * Q x) * ‖gradient Q x‖) ^ 2 =
            a ^ 2 * Real.exp (s * Q x) * ‖gradient Q x‖ ^ 2 := by
              rw [mul_pow, mul_pow, hExpSq]
        _ ≤ a ^ 2 * Real.exp (s * Q x) * (4 * Q x) :=
          mul_le_mul_of_nonneg_left (hQpoint x).2.2
            (mul_nonneg (sq_nonneg a) (Real.exp_nonneg _))
        _ = s ^ 2 * (Q x * Real.exp (s * Q x)) := by
          dsimp [a]
          ring
    rw [hgradNorm]
    exact hgradSquared
  have hEnergy :
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤
        s ^ 2 * ∫ x, Q x * Real.exp (s * Q x) ∂μ := by
    calc
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤
          ∫ x, s ^ 2 * (Q x * Real.exp (s * Q x)) ∂μ :=
        integral_mono hGradientIntegrable hMajorIntegrable hEnergyPoint
      _ = s ^ 2 * ∫ x, Q x * Real.exp (s * Q x) ∂μ := integral_const_mul _ _
  calc
    LOOConcentration.looconcentrationEntropy μ
        (fun x => Real.exp (s * Q x)) ≤ 2 * C * ∫ x, ‖gradient G x‖ ^ 2 ∂μ := hBase
    _ ≤ 2 * C * (s ^ 2 * ∫ x, Q x * Real.exp (s * Q x) ∂μ) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg (by norm_num) hC)
    _ = 2 * C * s ^ 2 * ∫ x, Q x * Real.exp (s * Q x) ∂μ := by ring

/-- The bounded log-MGF estimate for the actual norm cap, through the
source-faithful entropy producer above. -/
theorem bounded_norm_cap_log_mgf_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (N : ℝ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) (htCut : 2 * C * t < 1) :
    Integrable
        (fun x : EuclideanSpace ℝ ι => Real.exp
          (t * (N * (1 - Real.exp (-‖x‖ ^ 2 / N))))) μ ∧
      Real.log (∫ x, Real.exp
          (t * (N * (1 - Real.exp (-‖x‖ ^ 2 / N)))) ∂μ) ≤
        t * (∫ x, N * (1 - Real.exp (-‖x‖ ^ 2 / N)) ∂μ) /
          (1 - 2 * C * t) := by
  let Q : EuclideanSpace ℝ ι → ℝ :=
    fun x => N * (1 - Real.exp (-‖x‖ ^ 2 / N))
  obtain ⟨hQsmooth', hQpoint', _⟩ := norm_cap_bounded_smooth
    (E := EuclideanSpace ℝ ι) N hN
  have hQsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q := by
    simpa only [Q] using hQsmooth'
  have hQpoint (x : EuclideanSpace ℝ ι) :
      0 ≤ Q x ∧ Q x ≤ N ∧ ‖gradient Q x‖ ^ 2 ≤ 4 * Q x := by
    simpa only [Q] using hQpoint' x
  have hQmeas : Measurable Q := hQsmooth.continuous.measurable
  have hQbound : ∀ x, |Q x| ≤ N := by
    intro x
    rw [abs_of_nonneg (hQpoint x).1]
    exact (hQpoint x).2.1
  have hEntropy : ∀ s, 0 < s → 2 * C * s < 1 →
      LOOConcentration.looconcentrationEntropy μ
          (fun x => Real.exp (s * Q x)) ≤
        2 * C * s ^ 2 * ∫ x, Q x * Real.exp (s * Q x) ∂μ := by
    intro s hs hsCut
    have hs0 : 0 ≤ s := le_of_lt hs
    simpa only [Q] using norm_cap_entropy_bound μ C hC hLC N hN s hs0
  have hResult := bounded_log_mgf_le_of_norm_entropy_bound
    μ Q hQmeas N hN.le hQbound C hC hEntropy t ht htCut
  simpa only [Q] using hResult

end

end LOOConcentration.Revision
