import LOOConcentration.Examples.GaussianCompactCutoff
import LOOConcentration.Examples.GaussianVolumeDomination
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Actual bounded Gaussian cutoff energy and endpoints

For a bounded locally Lipschitz function, this module applies the accepted
smooth expanding cutoff to the function itself. It proves the product rule
almost everywhere, the derivative energy estimate from the actual full
derivative energy, and bounded square-mass and entropy endpoint convergence.
It does not assume or prove a log-Sobolev inequality.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LOOConcentration

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ν : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure ν]

noncomputable def boundedGaussianCutoffApproximation
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius) (B : ℝ)
    (hB : 0 ≤ B) : EuclideanSpace ℝ ι → ℝ :=
  boundedCompactCutoffApproximation u R (B + 1) (by linarith)

theorem boundedGaussianCutoffApproximation_clip_eq
    (u : EuclideanSpace ℝ ι → ℝ) (B : ℝ)
    (hu : ∀ x, |u x| ≤ B) (x : EuclideanSpace ℝ ι) :
    max (-(B + 1)) (min (u x) (B + 1)) = u x := by
  have huhi : u x ≤ B + 1 := ((abs_le.mp (hu x)).2).trans (by linarith)
  have hulo : -(B + 1) ≤ u x := by
    have h := (abs_le.mp (hu x)).1
    calc
      -(B + 1) = -B - 1 := by ring
      _ ≤ -B := by linarith
      _ ≤ u x := h
  calc
    max (-(B + 1)) (min (u x) (B + 1)) = max (-(B + 1)) (u x) := by
      rw [min_eq_left huhi]
    _ = u x := max_eq_right hulo

theorem boundedGaussianCutoffApproximation_eq_cutoff_mul
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius) (B : ℝ)
    (hB : 0 ≤ B) (hu : ∀ x, |u x| ≤ B) :
    boundedGaussianCutoffApproximation u R B hB =
      fun x => expandingGaussianCutoff R x * u x := by
  funext x
  simp only [boundedGaussianCutoffApproximation, boundedCompactCutoffApproximation]
  rw [boundedGaussianCutoffApproximation_clip_eq u B hu]
  ring

theorem boundedGaussianCutoffApproximation_abs_le
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius) (B : ℝ)
    (hB : 0 ≤ B) (hu : ∀ x, |u x| ≤ B) (x : EuclideanSpace ℝ ι) :
    |boundedGaussianCutoffApproximation u R B hB x| ≤ B := by
  rw [boundedGaussianCutoffApproximation_eq_cutoff_mul u R B hB hu]
  have hχ := expandingGaussianCutoff_mem_Icc R x
  rw [abs_mul]
  calc
    |expandingGaussianCutoff R x| * |u x| ≤ 1 * B :=
      mul_le_mul (abs_le.mpr ⟨by linarith [hχ.1], hχ.2⟩) (hu x)
        (abs_nonneg _) (by norm_num)
    _ = B := one_mul _

theorem boundedGaussianCutoffApproximation_hasCompactSupport
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius) (B : ℝ)
    (hB : 0 ≤ B) :
    HasCompactSupport (boundedGaussianCutoffApproximation u R B hB) := by
  exact boundedCompactCutoffApproximation_hasCompactSupport u R (B + 1) (by linarith)

theorem boundedGaussianCutoffApproximation_exists_globalLipschitz
    (u : EuclideanSpace ℝ ι → ℝ) (hu : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, LipschitzWith L (boundedGaussianCutoffApproximation u R B hB) := by
  exact boundedCompactCutoffApproximation_exists_globalLipschitz u hu R (B + 1)
    (by linarith)

private theorem smulRight_opNorm_bound
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (c : ℝ) :
    ‖A.smulRight c‖ ≤ ‖A‖ * |c| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (abs_nonneg _))
  intro v
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs]
  calc
    ‖A v‖ * |c| ≤ (‖A‖ * ‖v‖) * |c| :=
      mul_le_mul_of_nonneg_right (A.le_opNorm v) (abs_nonneg _)
    _ = (‖A‖ * |c|) * ‖v‖ := by ring

private theorem exists_gaussianCutoffDerivativeConstant :
    ∃ K : ℝ, ∀ (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι),
      ‖fderiv ℝ (expandingGaussianCutoff R) x‖ ≤ K / R.1 := by
  refine ⟨?_, ?_⟩
  swap
  · intro R x
    exact expandingGaussianCutoff_fderiv_norm_le R x

noncomputable def gaussianCutoffDerivativeConstant : ℝ :=
  Classical.choose (exists_gaussianCutoffDerivativeConstant (ι := ι))

theorem gaussianCutoffDerivativeConstant_spec
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (expandingGaussianCutoff R) x‖ ≤
      gaussianCutoffDerivativeConstant (ι := ι) / R.1 :=
  Classical.choose_spec (exists_gaussianCutoffDerivativeConstant (ι := ι)) R x

theorem gaussianCutoffDerivativeConstant_nonneg :
    0 ≤ gaussianCutoffDerivativeConstant (ι := ι) := by
  have h1 := gaussianCutoffDerivativeConstant_spec (ι := ι)
    ⟨1, by norm_num⟩ (0 : EuclideanSpace ℝ ι)
  dsimp [gaussianCutoffDerivativeConstant] at h1 ⊢
  exact (norm_nonneg _).trans (by simpa using h1)

theorem gaussianCutoffDerivativeConstant_bound
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (expandingGaussianCutoff R) x‖ ≤
      gaussianCutoffDerivativeConstant (ι := ι) / R.1 := by
  exact gaussianCutoffDerivativeConstant_spec (ι := ι) R x

theorem boundedGaussianCutoffApproximation_fderiv_eq_ae
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι))) :
    ∀ᵐ x ∂ν,
      fderiv ℝ (boundedGaussianCutoffApproximation u R B hB) x =
        expandingGaussianCutoff R x • fderiv ℝ u x +
          (fderiv ℝ (expandingGaussianCutoff R) x).smulRight (u x) := by
  have hdiff := locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
    u huLip hν
  filter_upwards [hdiff] with x hx
  rw [boundedGaussianCutoffApproximation_eq_cutoff_mul u R B hB hu]
  have hχ : DifferentiableAt ℝ (expandingGaussianCutoff R) x :=
    ((expandingGaussianCutoff_contDiff R).differentiable (by norm_num)).differentiableAt
  simpa only [smul_eq_mul] using fderiv_fun_smul hχ hx

theorem boundedGaussianCutoffApproximation_fderiv_norm_le_ae
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι))) :
    ∀ᵐ x ∂ν,
      ‖fderiv ℝ (boundedGaussianCutoffApproximation u R B hB) x‖ ≤
        ‖fderiv ℝ u x‖ + B * gaussianCutoffDerivativeConstant (ι := ι) / R.1 := by
  have hderiv := boundedGaussianCutoffApproximation_fderiv_eq_ae
    u huLip R B hB hu hν
  filter_upwards [hderiv] with x hx
  rw [hx]
  rcases expandingGaussianCutoff_mem_Icc R x with ⟨hχ0, hχ1⟩
  have hχnorm : |expandingGaussianCutoff R x| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hχ0], hχ1⟩
  have hcoeff : 0 ≤ gaussianCutoffDerivativeConstant (ι := ι) / R.1 :=
    div_nonneg gaussianCutoffDerivativeConstant_nonneg R.2.le
  calc
    ‖expandingGaussianCutoff R x • fderiv ℝ u x +
        (fderiv ℝ (expandingGaussianCutoff R) x).smulRight (u x)‖
        ≤ ‖expandingGaussianCutoff R x • fderiv ℝ u x‖ +
            ‖(fderiv ℝ (expandingGaussianCutoff R) x).smulRight (u x)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ u x‖ +
          ‖fderiv ℝ (expandingGaussianCutoff R) x‖ * |u x| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (calc
          |expandingGaussianCutoff R x| * ‖fderiv ℝ u x‖ ≤
              1 * ‖fderiv ℝ u x‖ := mul_le_mul_of_nonneg_right hχnorm (norm_nonneg _)
          _ = ‖fderiv ℝ u x‖ := one_mul _)
        (smulRight_opNorm_bound _ _)
    _ ≤ ‖fderiv ℝ u x‖ +
          (gaussianCutoffDerivativeConstant (ι := ι) / R.1) * B := by
      apply add_le_add le_rfl
      calc
        ‖fderiv ℝ (expandingGaussianCutoff R) x‖ * |u x| ≤
            (gaussianCutoffDerivativeConstant (ι := ι) / R.1) * |u x| :=
          mul_le_mul_of_nonneg_right (gaussianCutoffDerivativeConstant_bound R x)
            (abs_nonneg _)
        _ ≤ (gaussianCutoffDerivativeConstant (ι := ι) / R.1) * B :=
          mul_le_mul_of_nonneg_left (hu x) hcoeff
    _ = ‖fderiv ℝ u x‖ + B * gaussianCutoffDerivativeConstant (ι := ι) / R.1 := by ring

theorem boundedGaussianCutoffApproximation_memLp_two_fderiv
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι)))
    (henergy : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) ν) :
    MemLp (fderiv ℝ (boundedGaussianCutoffApproximation u R B hB)) 2 ν := by
  let d : EuclideanSpace ℝ ι → ℝ := fun x => ‖fderiv ℝ u x‖
  let c : ℝ := B * gaussianCutoffDerivativeConstant (ι := ι) / R.1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg hB gaussianCutoffDerivativeConstant_nonneg) R.2.le
  have hd : MemLp d 2 ν := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa [d] using henergy
  have hdc : MemLp (fun x => d x + c) 2 ν :=
    hd.add (memLp_const c)
  apply hdc.of_le (by fun_prop)
  filter_upwards [boundedGaussianCutoffApproximation_fderiv_norm_le_ae
    u huLip R B hB hu hν] with x hx
  simpa [d, c, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) hc)] using hx

theorem boundedGaussianCutoffApproximation_integrable_sq_fderiv
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι)))
    (henergy : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) ν) :
    Integrable
      (fun x => ‖fderiv ℝ (boundedGaussianCutoffApproximation u R B hB) x‖ ^ 2) ν := by
  exact (memLp_two_iff_integrable_sq_norm
    (boundedGaussianCutoffApproximation_memLp_two_fderiv
      u huLip R B hB hu hν henergy).aestronglyMeasurable).1
        (boundedGaussianCutoffApproximation_memLp_two_fderiv
          u huLip R B hB hu hν henergy)

theorem boundedGaussianCutoffApproximation_eLpNorm_fderiv_le
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι)))
    (henergy : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) ν) :
    eLpNorm (fderiv ℝ (boundedGaussianCutoffApproximation u R B hB)) 2 ν ≤
      eLpNorm (fderiv ℝ u) 2 ν +
        ENNReal.ofReal (B * gaussianCutoffDerivativeConstant (ι := ι) / R.1) := by
  let d : EuclideanSpace ℝ ι → ℝ := fun x => ‖fderiv ℝ u x‖
  let c : ℝ := B * gaussianCutoffDerivativeConstant (ι := ι) / R.1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg hB gaussianCutoffDerivativeConstant_nonneg) R.2.le
  have hd : MemLp d 2 ν := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa [d] using henergy
  have hconst : eLpNorm (fun _ : EuclideanSpace ℝ ι => c) 2 ν = ENNReal.ofReal c := by
    rw [eLpNorm_const c (by norm_num) (by
      intro h
      have hh := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ Set.univ) h
      simp [measure_univ] at hh)]
    rw [Real.enorm_eq_ofReal hc]
    simp [measure_univ]
  calc
    eLpNorm (fderiv ℝ (boundedGaussianCutoffApproximation u R B hB)) 2 ν
        ≤ eLpNorm (fun x => d x + c) 2 ν :=
          eLpNorm_mono_ae_real
            (boundedGaussianCutoffApproximation_fderiv_norm_le_ae
              u huLip R B hB hu hν)
    _ ≤ eLpNorm d 2 ν + eLpNorm (fun _ : EuclideanSpace ℝ ι => c) 2 ν :=
      eLpNorm_add_le hd.aestronglyMeasurable aestronglyMeasurable_const (by norm_num)
    _ = eLpNorm (fderiv ℝ u) 2 ν + ENNReal.ofReal c := by
      rw [eLpNorm_norm, hconst]

theorem boundedGaussianCutoffApproximation_sqrtEnergy_le
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι)))
    (henergy : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) ν) :
    Real.sqrt (∫ x, ‖fderiv ℝ
      (boundedGaussianCutoffApproximation u R B hB) x‖ ^ 2 ∂ν) ≤
      Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν) +
        B * gaussianCutoffDerivativeConstant (ι := ι) / R.1 := by
  let fcut : EuclideanSpace ℝ ι → ℝ :=
    boundedGaussianCutoffApproximation u R B hB
  let c : ℝ := B * gaussianCutoffDerivativeConstant (ι := ι) / R.1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg hB gaussianCutoffDerivativeConstant_nonneg) R.2.le
  have hduMeas : AEStronglyMeasurable (fderiv ℝ u) ν := by fun_prop
  have hduLp : MemLp (fderiv ℝ u) 2 ν :=
    (memLp_two_iff_integrable_sq_norm hduMeas).2 henergy
  have hcutLp : MemLp (fderiv ℝ fcut) 2 ν := by
    simpa [fcut] using boundedGaussianCutoffApproximation_memLp_two_fderiv
      u huLip R B hB hu hν henergy
  have hbound := boundedGaussianCutoffApproximation_eLpNorm_fderiv_le
    u huLip R B hB hu hν henergy
  have hsumTop :
      eLpNorm (fderiv ℝ u) 2 ν +
        ENNReal.ofReal (B * gaussianCutoffDerivativeConstant (ι := ι) / R.1) ≠ ∞ := by
    exact ENNReal.add_ne_top.2 ⟨hduLp.eLpNorm_ne_top, ENNReal.ofReal_ne_top⟩
  have htoReal := ENNReal.toReal_mono hsumTop hbound
  rw [ENNReal.toReal_add hduLp.eLpNorm_ne_top ENNReal.ofReal_ne_top,
    toReal_eLpNorm hcutLp.aestronglyMeasurable,
    toReal_eLpNorm hduLp.aestronglyMeasurable,
    ENNReal.toReal_ofReal hc] at htoReal
  have hcutEnergyLpNorm :
      lpNorm (fderiv ℝ fcut) 2 ν =
        Real.sqrt (∫ x, ‖fderiv ℝ fcut x‖ ^ 2 ∂ν) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hcutLp.aestronglyMeasurable]
    norm_num [Real.sqrt_eq_rpow]
  have huEnergyLpNorm :
      lpNorm (fderiv ℝ u) 2 ν =
        Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hduLp.aestronglyMeasurable]
    norm_num [Real.sqrt_eq_rpow]
  calc
    Real.sqrt (∫ x, ‖fderiv ℝ fcut x‖ ^ 2 ∂ν) = lpNorm (fderiv ℝ fcut) 2 ν :=
      hcutEnergyLpNorm.symm
    _ ≤ lpNorm (fderiv ℝ u) 2 ν + c := htoReal
    _ = Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν) + c := by rw [huEnergyLpNorm]

theorem boundedGaussianCutoffApproximation_energy_le
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (hν : ν ≪ (volume : Measure (EuclideanSpace ℝ ι)))
    (henergy : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) ν) :
    ∫ x, ‖fderiv ℝ (boundedGaussianCutoffApproximation u R B hB) x‖ ^ 2 ∂ν ≤
      (Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν) +
        B * gaussianCutoffDerivativeConstant (ι := ι) / R.1) ^ 2 := by
  let Ecut := ∫ x, ‖fderiv ℝ (boundedGaussianCutoffApproximation u R B hB) x‖ ^ 2 ∂ν
  let Efull := ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν
  have hcut0 : 0 ≤ Ecut := by
    exact integral_nonneg fun x => sq_nonneg _
  have hfull0 : 0 ≤ Efull := by
    exact integral_nonneg fun x => sq_nonneg _
  have herr : 0 ≤ B * gaussianCutoffDerivativeConstant (ι := ι) / R.1 :=
    div_nonneg (mul_nonneg hB gaussianCutoffDerivativeConstant_nonneg) R.2.le
  have hroot := boundedGaussianCutoffApproximation_sqrtEnergy_le
    u huLip R B hB hu hν henergy
  change Ecut ≤ (Real.sqrt Efull +
    B * gaussianCutoffDerivativeConstant (ι := ι) / R.1) ^ 2
  calc
    Ecut = (Real.sqrt Ecut) ^ 2 := (Real.sq_sqrt hcut0).symm
    _ ≤ (Real.sqrt Efull +
        B * gaussianCutoffDerivativeConstant (ι := ι) / R.1) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) herr)).2 hroot

private theorem gaussianPositiveRadius_coe_tendsto_atTop :
    Tendsto (fun R : GaussianPositiveRadius => R.1) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  refine Filter.eventually_atTop.2
    ⟨⟨max b 0 + 1, by positivity⟩, fun R hR => ?_⟩
  exact le_trans (le_trans (le_max_left b 0) (by linarith)) hR

theorem gaussianCutoffDerivativeError_tendsto_zero (B : ℝ) :
    Tendsto
      (fun R : GaussianPositiveRadius =>
        B * gaussianCutoffDerivativeConstant (ι := ι) / R.1)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_inv_atTop_zero.comp gaussianPositiveRadius_coe_tendsto_atTop).const_mul
      (B * gaussianCutoffDerivativeConstant (ι := ι))
  simpa [div_eq_mul_inv, mul_comm] using h

theorem boundedGaussianCutoffApproximation_sqrtEnergyBound_tendsto
    (u : EuclideanSpace ℝ ι → ℝ) (B : ℝ) :
    Tendsto
      (fun R : GaussianPositiveRadius =>
        Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν) +
          B * gaussianCutoffDerivativeConstant (ι := ι) / R.1)
      atTop (𝓝 (Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν))) := by
  simpa using
    (tendsto_const_nhds.add (gaussianCutoffDerivativeError_tendsto_zero B))

def gaussianIntegerRadius (n : ℕ) : GaussianPositiveRadius :=
  ⟨(n : ℝ) + 1, by positivity⟩

theorem gaussianIntegerRadius_tendsto_atTop :
    Tendsto gaussianIntegerRadius atTop atTop := by
  refine tendsto_atTop.2 fun R => ?_
  refine Filter.eventually_atTop.2 ⟨Nat.ceil R.1, fun n hn => ?_⟩
  change R.1 ≤ (n : ℝ) + 1
  have hcast : (Nat.ceil R.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact (Nat.le_ceil R.1).trans (hcast.trans (by linarith))

theorem boundedGaussianCutoffApproximation_tendsto_pointwise
    (u : EuclideanSpace ℝ ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) (x : EuclideanSpace ℝ ι) :
    Tendsto
      (fun n : ℕ => boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x)
      atTop (𝓝 (u x)) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards
    [gaussianIntegerRadius_tendsto_atTop.eventually
      (expandingGaussianCutoff_eventually_eq_one x)] with n hn
  rw [show boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x =
      expandingGaussianCutoff (gaussianIntegerRadius n) x * u x by
    exact congrFun (boundedGaussianCutoffApproximation_eq_cutoff_mul
      u (gaussianIntegerRadius n) B hB hu) x]
  rw [hn]
  exact one_mul _

def cutoffSquareLogSquare (z : ℝ) : ℝ := z ^ 2 * Real.log (z ^ 2)

private theorem exists_bound_cutoffSquareLogSquare (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |z| ≤ B → |cutoffSquareLogSquare z| ≤ C := by
  have hcont : Continuous (fun t : ℝ => t * Real.log t) := Real.continuous_mul_log
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (B ^ 2))).bddAbove_image
      hcont.continuousOn.norm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have htlo : 0 ≤ z ^ 2 := sq_nonneg _
  have hthi : z ^ 2 ≤ B ^ 2 := by
    have hzlo : -B ≤ z := (abs_le.mp hz).1
    have hzhi : z ≤ B := (abs_le.mp hz).2
    have hleft : 0 ≤ B - z := by linarith
    have hright : 0 ≤ B + z := by linarith
    have hp := mul_nonneg hleft hright
    nlinarith [hp]
  have ht : z ^ 2 ∈ Icc (0 : ℝ) (B ^ 2) := ⟨htlo, hthi⟩
  have himage : ‖z ^ 2 * Real.log (z ^ 2)‖ ∈
      (fun t : ℝ => ‖t * Real.log t‖) '' Icc (0 : ℝ) (B ^ 2) :=
    ⟨z ^ 2, ht, rfl⟩
  have hnorm : ‖z ^ 2 * Real.log (z ^ 2)‖ ≤ C := hC himage
  dsimp [cutoffSquareLogSquare]
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans (le_max_left _ _)

theorem boundedGaussianCutoffApproximation_tendsto_squareMass
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (B : ℝ) (hB : 0 ≤ B) (hu : ∀ x, |u x| ≤ B) :
    Tendsto
      (fun n : ℕ =>
        ∫ x, (boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x) ^ 2 ∂ν)
      atTop (𝓝 (∫ x, (u x) ^ 2 ∂ν)) := by
  let g : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x
  have hg_cont (n : ℕ) : Continuous (g n) := by
    obtain ⟨L, hL⟩ := boundedGaussianCutoffApproximation_exists_globalLipschitz
      u huLip (gaussianIntegerRadius n) B hB
    exact hL.continuous
  have hg_bound (n : ℕ) (x : EuclideanSpace ℝ ι) : |g n x| ≤ B := by
    exact boundedGaussianCutoffApproximation_abs_le u (gaussianIntegerRadius n) B hB hu x
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => B ^ 2)
  · intro n
    exact ((continuous_pow 2).comp (hg_cont n)).aestronglyMeasurable
  · exact integrable_const (B ^ 2)
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g n x))]
    have hleft : 0 ≤ B - |g n x| := by linarith [hg_bound n x]
    have hright : 0 ≤ B + |g n x| := by linarith [hB, abs_nonneg (g n x)]
    have hp := mul_nonneg hleft hright
    nlinarith [sq_abs (g n x), hp]
  · exact Filter.Eventually.of_forall fun x =>
      (boundedGaussianCutoffApproximation_tendsto_pointwise u B hB hu x).pow 2

theorem boundedGaussianCutoffApproximation_tendsto_entropy
    (u : EuclideanSpace ℝ ι → ℝ) (huLip : LocallyLipschitz u)
    (B : ℝ) (hB : 0 ≤ B) (hu : ∀ x, |u x| ≤ B) :
    Tendsto
      (fun n : ℕ =>
        ∫ x, cutoffSquareLogSquare
          (boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x) ∂ν)
      atTop (𝓝 (∫ x, cutoffSquareLogSquare (u x) ∂ν)) := by
  let g : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x
  have hg_cont (n : ℕ) : Continuous (g n) := by
    obtain ⟨L, hL⟩ := boundedGaussianCutoffApproximation_exists_globalLipschitz
      u huLip (gaussianIntegerRadius n) B hB
    exact hL.continuous
  have hg_bound (n : ℕ) (x : EuclideanSpace ℝ ι) : |g n x| ≤ B := by
    exact boundedGaussianCutoffApproximation_abs_le u (gaussianIntegerRadius n) B hB hu x
  rcases exists_bound_cutoffSquareLogSquare B hB with ⟨C, hC0, hC⟩
  have hcont : Continuous cutoffSquareLogSquare := by
    change Continuous (fun z : ℝ => z ^ 2 * Real.log (z ^ 2))
    exact Real.continuous_mul_log.comp ((continuous_pow 2).comp continuous_id)
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => C)
  · intro n
    exact (hcont.comp (hg_cont n)).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    filter_upwards with x
    have hx := hC (g n x) (hg_bound n x)
    simpa [Real.norm_eq_abs] using hx
  · exact Filter.Eventually.of_forall fun x =>
      (hcont.continuousAt.tendsto).comp
        (boundedGaussianCutoffApproximation_tendsto_pointwise u B hB hu x)

end

#print axioms boundedGaussianCutoffApproximation_hasCompactSupport
#print axioms boundedGaussianCutoffApproximation_exists_globalLipschitz
#print axioms boundedGaussianCutoffApproximation_fderiv_eq_ae
#print axioms boundedGaussianCutoffApproximation_integrable_sq_fderiv
#print axioms boundedGaussianCutoffApproximation_eLpNorm_fderiv_le
#print axioms boundedGaussianCutoffApproximation_sqrtEnergy_le
#print axioms boundedGaussianCutoffApproximation_energy_le
#print axioms boundedGaussianCutoffApproximation_sqrtEnergyBound_tendsto
#print axioms boundedGaussianCutoffApproximation_tendsto_pointwise
#print axioms boundedGaussianCutoffApproximation_tendsto_squareMass
#print axioms boundedGaussianCutoffApproximation_tendsto_entropy

end LOOConcentration
