import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

private theorem squarePlusEpsilon_contDiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Real.sqrt ((F x) ^ 2 + ε)) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have hbase : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => F y ^ 2 + ε) x :=
    (hF.contDiffAt.pow 2).add contDiffAt_const
  have hpos : 0 < F x ^ 2 + ε :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  exact hbase.sqrt (ne_of_gt hpos)

private theorem squarePlusEpsilon_fderiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y => Real.sqrt ((F y) ^ 2 + ε)) x =
      (F x / Real.sqrt ((F x) ^ 2 + ε)) • fderiv ℝ F x := by
  have hFx : DifferentiableAt ℝ F x :=
    hF.contDiffAt.differentiableAt (by simp)
  have hHx : DifferentiableAt ℝ (fun y => F y ^ 2 + ε) x :=
    hFx.pow 2 |>.add_const ε
  have hHderiv : fderiv ℝ (fun y => F y ^ 2 + ε) x =
      (2 * F x) • fderiv ℝ F x := by
    rw [fderiv_add_const, fderiv_fun_pow 2 hFx]
    norm_num [pow_one]
  have hHpos : 0 < (F x) ^ 2 + ε :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hSqrt : HasFDerivAt (fun y => Real.sqrt (F y ^ 2 + ε))
      ((1 / (2 * Real.sqrt (F x ^ 2 + ε))) • fderiv ℝ (fun y => F y ^ 2 + ε) x) x :=
    hHx.hasFDerivAt.sqrt (ne_of_gt hHpos)
  rw [hSqrt.fderiv, hHderiv, smul_smul]
  congr 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 hHpos)]

private theorem squarePlusEpsilon_gradient_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    gradient (fun y => Real.sqrt ((F y) ^ 2 + ε)) x =
      (F x / Real.sqrt ((F x) ^ 2 + ε)) • gradient F x := by
  rw [gradient, gradient, squarePlusEpsilon_fderiv F hF ε hε x]
  simp only [map_smul]

/-- The actual bounded square-plus-epsilon coordinate-section entropy producer.
It regularizes `F` by `sqrt (F^2 + epsilon)`, invokes the certified smooth
base-generator LSI at the same constant, and returns the literal entropy bound
for `F^2 + epsilon` with the gradient energy of `F`. -/
theorem bounded_square_add_epsilon_entropy_le_of_logSobolevConstant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ x, ((F x) ^ 2 + ε) * Real.log ((F x) ^ 2 + ε) ∂μ) -
      (∫ x, (F x) ^ 2 + ε ∂μ) *
        Real.log (∫ x, (F x) ^ 2 + ε ∂μ) ≤
      2 * C * ∫ x, ‖gradient F x‖ ^ 2 ∂μ := by
  let G : EuclideanSpace ℝ ι → ℝ := fun x => Real.sqrt ((F x) ^ 2 + ε)
  let B' : ℝ := Real.sqrt (B ^ 2 + ε)
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    simpa only [G] using squarePlusEpsilon_contDiff F hF ε hε
  have hB' : 0 ≤ B' := by
    dsimp [B']
    exact Real.sqrt_nonneg _
  have hB_le : B ≤ B' := by
    dsimp [B']
    apply (Real.le_sqrt hB (by positivity)).2
    nlinarith [sq_nonneg B]
  have hgradContract (x : EuclideanSpace ℝ ι) :
      ‖gradient G x‖ ≤ ‖gradient F x‖ := by
    have hGpos : 0 < G x := by
      dsimp [G]
      exact Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
    have hFG : |F x| ≤ G x := by
      apply Real.abs_le_sqrt
      linarith
    have hcoeff : |F x / G x| ≤ 1 := by
      rw [abs_div, abs_of_pos hGpos]
      exact (div_le_one hGpos).2 hFG
    rw [show G = (fun y => Real.sqrt ((F y) ^ 2 + ε)) by rfl,
      squarePlusEpsilon_gradient_formula F hF ε hε x]
    calc
      ‖(F x / G x) • gradient F x‖ = |F x / G x| * ‖gradient F x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖gradient F x‖ :=
        mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ = ‖gradient F x‖ := by ring
  have hGbound (x : EuclideanSpace ℝ ι) :
      |G x| ≤ B' ∧ ‖gradient G x‖ ≤ B' := by
    have hFabs : |F x| ≤ B := (hbound x).1
    have hFsq : (F x) ^ 2 ≤ B ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hB]
      exact hFabs
    have hGnonneg : 0 ≤ G x := by simp [G]
    have hGle : G x ≤ B' := by
      dsimp [G, B']
      apply Real.sqrt_le_sqrt
      linarith
    have hGpos : 0 < G x := by
      dsimp [G]
      exact Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
    have hcoeff : |F x / G x| ≤ 1 := by
      have hFG : |F x| ≤ G x := by
        apply Real.abs_le_sqrt
        linarith
      rw [abs_div, abs_of_pos hGpos]
      exact (div_le_one hGpos).2 hFG
    have hgrad : ‖gradient G x‖ ≤ ‖gradient F x‖ := by
      rw [show G = (fun y => Real.sqrt ((F y) ^ 2 + ε)) by rfl,
        squarePlusEpsilon_gradient_formula F hF ε hε x]
      calc
        ‖(F x / G x) • gradient F x‖ = |F x / G x| * ‖gradient F x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖gradient F x‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ = ‖gradient F x‖ := by ring
    exact ⟨by rw [abs_of_nonneg hGnonneg]; exact hGle,
      (hgrad.trans (hbound x).2).trans hB_le⟩
  have hbase := bounded_smooth_entropy_le_of_logSobolevConstant_le
    μ C hC hLC G hGsmooth B' hB' hGbound
  have hgradFContinuous : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hgradGContinuous : Continuous (gradient G) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hGsmooth.continuous_fderiv (by simp))
  have hgradFMemLp : MemLp (gradient F) 2 μ :=
    MemLp.of_bound hgradFContinuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => (hbound x).2)
  have hgradGMemLp : MemLp (gradient G) 2 μ :=
    MemLp.of_bound hgradGContinuous.aestronglyMeasurable B'
      (Filter.Eventually.of_forall fun x => (hGbound x).2)
  have hgradFInt : Integrable (fun x => ‖gradient F x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hgradFMemLp.aestronglyMeasurable).mp hgradFMemLp
  have hgradGInt : Integrable (fun x => ‖gradient G x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hgradGMemLp.aestronglyMeasurable).mp hgradGMemLp
  have henergy :
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤ ∫ x, ‖gradient F x‖ ^ 2 ∂μ :=
    integral_mono_ae hgradGInt hgradFInt <| Filter.Eventually.of_forall fun x => by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hgradContract x)
  have hEntropy :
      (∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂μ) -
        (∫ x, G x ^ 2 ∂μ) * Real.log (∫ x, G x ^ 2 ∂μ) =
      (∫ x, (F x ^ 2 + ε) * Real.log (F x ^ 2 + ε) ∂μ) -
        (∫ x, F x ^ 2 + ε ∂μ) * Real.log (∫ x, F x ^ 2 + ε ∂μ) := by
    have hsq (x : EuclideanSpace ℝ ι) : G x ^ 2 = F x ^ 2 + ε := by
      dsimp [G]
      exact Real.sq_sqrt (add_nonneg (sq_nonneg _) hε.le)
    have hDensity :
        (∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂μ) =
          ∫ x, (F x ^ 2 + ε) * Real.log (F x ^ 2 + ε) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change G x ^ 2 * Real.log (G x ^ 2) =
          (F x ^ 2 + ε) * Real.log (F x ^ 2 + ε)
        rw [hsq x])
    have hMean :
        (∫ x, G x ^ 2 ∂μ) = ∫ x, F x ^ 2 + ε ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change G x ^ 2 = F x ^ 2 + ε
        exact hsq x)
    rw [hDensity, hMean]
  rw [← hEntropy]
  exact hbase.trans (mul_le_mul_of_nonneg_left henergy (by positivity))

#print axioms LOOConcentration.Revision.bounded_square_add_epsilon_entropy_le_of_logSobolevConstant_le

end LOOConcentration.Revision
