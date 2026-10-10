import LOOConcentration.Analysis.ClipMollify
import LOOConcentration.Analysis.ClipLimit
import BoundedCenteredLpSourceAssembly
import LOOConcentrationRevision.FunctionalInequalities.MollifiedScalarLimit
import LOOConcentrationRevision.FunctionalInequalities.MollifiedGradientGrowth
import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology

private theorem integral_rpow_two_eq_lpNorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ} {p : ℝ}
    (hp : 2 ≤ p) (hf : AEStronglyMeasurable f μ) :
    (∫ x, |f x| ^ p ∂μ) ^ (2 / p) =
      (lpNorm f (ENNReal.ofReal p) μ) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop hf, hqreal]
  have hI : (∫ x, ‖f x‖ ^ p ∂μ) = ∫ x, |f x| ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
  rw [← hI]
  rw [show (2 / p : ℝ) = p⁻¹ * 2 by field_simp]
  rw [Real.rpow_mul (integral_nonneg fun x => by positivity)]
  rw [← Real.rpow_natCast]
  rfl

private theorem lpNorm_affine_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : 1 ≤ q)
    (hNorm : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) q μ)
    (c b : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    lpNorm (fun x => c + b * ‖x‖) q μ ≤ c + b * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) q μ := by
  have hμ0 : μ ≠ 0 := by
    intro h
    have hUniv : μ Set.univ = 1 := measure_univ
    rw [h] at hUniv
    simp at hUniv
  have hcMem : MemLp (fun _ : EuclideanSpace ℝ ι => c) q μ := memLp_const c
  have hbMem : MemLp (fun x : EuclideanSpace ℝ ι => b * ‖x‖) q μ := hNorm.const_mul b
  have hfun : (fun x : EuclideanSpace ℝ ι => c + b * ‖x‖) =
      (fun _ => c) + fun x => b * ‖x‖ := by
    funext x
    rfl
  have hscale : (fun x : EuclideanSpace ℝ ι => b * ‖x‖) =
      b • fun x => ‖x‖ := by
    funext x
    simp [smul_eq_mul]
  rw [hfun]
  calc
    lpNorm ((fun _ : EuclideanSpace ℝ ι => c) + fun x => b * ‖x‖) q μ ≤
        lpNorm (fun _ : EuclideanSpace ℝ ι => c) q μ +
          lpNorm (fun x : EuclideanSpace ℝ ι => b * ‖x‖) q μ := lpNorm_add_le hcMem hq1
    _ = c + b * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) q μ := by
      rw [lpNorm_const hq0 hμ0 c, hscale, lpNorm_const_smul]
      simp [Measure.real, measure_univ, Real.norm_eq_abs, abs_of_nonneg hc,
        abs_of_nonneg hb]

private theorem integrable_of_quadratic_segment_growth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F)
    (a b : NNReal)
    (hseg : LOOConcentration.HasLinearGrowthSegmentBound F (a : ℝ) (b : ℝ)) :
    Integrable F μ := by
  have hnormInt : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) μ := by
    have hmajor : Integrable (fun x : EuclideanSpace ℝ ι => (1 : ℝ) + ‖x‖ ^ 2) μ :=
      (integrable_const (1 : ℝ)).add hmoment
    apply hmajor.mono' continuous_norm.aestronglyMeasurable
    filter_upwards [] with x
    change |‖x‖| ≤ 1 + ‖x‖ ^ 2
    rw [abs_of_nonneg (norm_nonneg x)]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hmajor : Integrable (fun x : EuclideanSpace ℝ ι =>
      |F 0| + (a : ℝ) * ‖x‖ + (b : ℝ) / 2 * ‖x‖ ^ 2) μ := by
    have ha : Integrable (fun x : EuclideanSpace ℝ ι => (a : ℝ) * ‖x‖) μ :=
      hnormInt.const_mul (a : ℝ)
    have hb : Integrable (fun x : EuclideanSpace ℝ ι => (b : ℝ) / 2 * ‖x‖ ^ 2) μ :=
      hmoment.const_mul ((b : ℝ) / 2)
    have hEq : (fun x : EuclideanSpace ℝ ι =>
        |F 0| + (a : ℝ) * ‖x‖ + (b : ℝ) / 2 * ‖x‖ ^ 2) =
        (fun x => |F 0| + ((a : ℝ) * ‖x‖ + (b : ℝ) / 2 * ‖x‖ ^ 2)) := by
      funext x
      ring
    rw [hEq]
    exact (integrable_const |F 0|).add (ha.add hb)
  apply hmajor.mono' hF.continuous.aestronglyMeasurable
  filter_upwards [] with x
  have hs := hseg 0 x
  have hxnorm : dist (0 : EuclideanSpace ℝ ι) x = ‖x‖ := by simp
  have hzero : ‖(0 : EuclideanSpace ℝ ι)‖ = 0 := norm_zero
  have hbound : |F x - F 0| ≤ ‖x‖ * ((a : ℝ) + (b : ℝ) / 2 * ‖x‖) := by
    rw [abs_sub_comm]
    simpa only [hxnorm, norm_zero, zero_add] using hs
  calc
    ‖F x‖ = ‖(F x - F 0) + F 0‖ := by congr 1; ring
    _ ≤ ‖F x - F 0‖ + ‖F 0‖ := norm_add_le _ _
    _ = |F x - F 0| + |F 0| := by simp only [Real.norm_eq_abs]
    _ = |F 0| + |F x - F 0| := by ring
    _ = |F x - F 0| + |F 0| := by ring
    _ ≤ ‖x‖ * ((a : ℝ) + (b : ℝ) / 2 * ‖x‖) + |F 0| := by
      simpa only [add_comm] using (add_le_add_left hbound |F 0|)
    _ = |F 0| + ‖x‖ * ((a : ℝ) + (b : ℝ) / 2 * ‖x‖) := by ring
    _ = |F 0| + (a : ℝ) * ‖x‖ + (b : ℝ) / 2 * ‖x‖ ^ 2 := by ring

private theorem mollified_centered_lp_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F)
    (a b : NNReal) (R : NNReal) (η : ℝ) (hη : 0 < η)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)))
    {p : ℝ} (hp : 2 ≤ p)
    (hNorm : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => LOOConcentration.clipThenMollify F (R : ℝ) η x -
      ∫ y, LOOConcentration.clipThenMollify F (R : ℝ) η y ∂μ)
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
        ((a : ℝ) + (b : ℝ) * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
          (ENNReal.ofReal p) μ + (b : ℝ) * η)) := by
  let G : EuclideanSpace ℝ ι → ℝ :=
    fun x => LOOConcentration.clipThenMollify F (R : ℝ) η x
  let H : EuclideanSpace ℝ ι → ℝ :=
    fun x => (a : ℝ) + (b : ℝ) * η + (b : ℝ) * ‖x‖
  have hq0 : ENNReal.ofReal p ≠ 0 := by
    have hp0 : 0 < p := by linarith
    simp [hp0]
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : 1 ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
  obtain ⟨hsmooth, B, hB, hbound⟩ :=
    LOOConcentration.Revision.clipThenMollify_bounded_smooth F hF R η hη
  have hGmem : MemLp G (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound (μ := μ) hsmooth.continuous.aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun x => by
      simpa [G, Real.norm_eq_abs] using (hbound x).1
  let m : ℝ := ∫ y, G y ∂μ
  have hmMem : MemLp (fun _ : EuclideanSpace ℝ ι => m) (ENNReal.ofReal p) μ :=
    memLp_const m
  have hcenterMem : MemLp (fun x => G x - m) (ENNReal.ofReal p) μ := hGmem.sub hmMem
  have hcenterAEStrong : AEStronglyMeasurable (fun x => G x - m) μ :=
    hcenterMem.aestronglyMeasurable
  have hgradCont : Continuous (fun x : EuclideanSpace ℝ ι =>
      ‖gradient G x‖) :=
    ((toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hsmooth.continuous_fderiv (by simp))).norm
  have hgradAEStrong : AEStronglyMeasurable (fun x => ‖gradient G x‖) μ :=
    hgradCont.aestronglyMeasurable
  have hHmem : MemLp H (ENNReal.ofReal p) μ := by
    have hbase : MemLp (fun x : EuclideanSpace ℝ ι =>
        (a : ℝ) + (b : ℝ) * η + (b : ℝ) * ‖x‖)
        (ENNReal.ofReal p) μ := by
      have hconst : MemLp (fun _ : EuclideanSpace ℝ ι =>
          (a : ℝ) + (b : ℝ) * η) (ENNReal.ofReal p) μ := by
        exact memLp_const ((a : ℝ) + (b : ℝ) * η)
      have hscale := hNorm.const_mul (b : ℝ)
      have heq : (fun x : EuclideanSpace ℝ ι =>
          (a : ℝ) + (b : ℝ) * η + (b : ℝ) * ‖x‖) =
          (fun _ => (a : ℝ) + (b : ℝ) * η) + fun x => (b : ℝ) * ‖x‖ := by
        funext x
        rfl
      rw [heq]
      exact hconst.add hscale
    exact hbase
  have hHlp : lpNorm H (ENNReal.ofReal p) μ ≤
      (a : ℝ) + (b : ℝ) * η + (b : ℝ) *
        lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ := by
    simpa [H, add_assoc, add_left_comm, add_comm] using
      (lpNorm_affine_norm_le μ hq0 hq1 hNorm
        ((a : ℝ) + (b : ℝ) * η) (b : ℝ)
        (by positivity) b.property)
  have hpointGrad (x : EuclideanSpace ℝ ι) :
      ‖gradient G x‖ ≤ H x := by
    simpa [G, H, add_assoc, add_left_comm, add_comm] using
      LOOConcentration.Revision.clipThenMollify_gradient_growth
        F hF a b (R : ℝ) η hη hseg x
  have hpointGradScalar (x : EuclideanSpace ℝ ι) :
      ‖‖gradient G x‖‖ ≤ H x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpointGrad x
  have hgradLp : lpNorm (fun x => ‖gradient G x‖) (ENNReal.ofReal p) μ ≤
      lpNorm H (ENNReal.ofReal p) μ := lpNorm_mono_real hHmem hpointGradScalar
  have hsrc := LOOConcentration.Revision.boundedSmoothCenteredLp
    μ C hC hLC G hsmooth B hB hbound hp
  have hIcenter := integral_rpow_two_eq_lpNorm_sq (μ := μ)
    (f := fun x => G x - m) hp hcenterAEStrong
  have hIgrad := integral_rpow_two_eq_lpNorm_sq (μ := μ)
    (f := fun x => ‖gradient G x‖) hp hgradAEStrong
  have hpow : lpNorm (fun x => G x - m) (ENNReal.ofReal p) μ ^ 2 ≤
      C * (p - 1) *
        lpNorm (fun x => ‖gradient G x‖) (ENNReal.ofReal p) μ ^ 2 := by
    have hs : (∫ x, |G x - ∫ y, G y ∂μ| ^ p ∂μ) ^ (2 / p) ≤
        C * (p - 1) * (∫ x, ‖gradient G x‖ ^ p ∂μ) ^ (2 / p) := hsrc
    have hgradInt : (∫ x, |‖gradient G x‖| ^ p ∂μ) =
        ∫ x, ‖gradient G x‖ ^ p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_of_nonneg (norm_nonneg _)]
    rw [hIcenter] at hs
    rw [← hgradInt, hIgrad] at hs
    simpa [G, m] using hs
  have hcoef : 0 ≤ C * (p - 1) := mul_nonneg hC (by linarith)
  have hCenterLpNonneg : 0 ≤ lpNorm (fun x => G x - m) (ENNReal.ofReal p) μ :=
    lpNorm_nonneg
  have hGradLpNonneg : 0 ≤ lpNorm (fun x => ‖gradient G x‖) (ENNReal.ofReal p) μ :=
    lpNorm_nonneg
  have hHLpNonneg : 0 ≤ lpNorm H (ENNReal.ofReal p) μ := lpNorm_nonneg
  have hNormLpNonneg : 0 ≤ lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
      (ENNReal.ofReal p) μ := lpNorm_nonneg
  have hS : 0 ≤ (a : ℝ) + (b : ℝ) * η + (b : ℝ) *
      lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ := by
    positivity
  have hboundLp : lpNorm (fun x => G x - m) (ENNReal.ofReal p) μ ≤
      Real.sqrt (C * (p - 1)) *
        ((a : ℝ) + (b : ℝ) * η + (b : ℝ) *
          lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) := by
    apply (sq_le_sq₀ hCenterLpNonneg (mul_nonneg (Real.sqrt_nonneg _) hS)).mp
    have hgradSq : lpNorm (fun x => ‖gradient G x‖) (ENNReal.ofReal p) μ ^ 2 ≤
        lpNorm H (ENNReal.ofReal p) μ ^ 2 :=
      (sq_le_sq₀ hGradLpNonneg hHLpNonneg).2 hgradLp
    have hHSq : lpNorm H (ENNReal.ofReal p) μ ^ 2 ≤
        ((a : ℝ) + (b : ℝ) * η + (b : ℝ) *
          lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) ^ 2 :=
      (sq_le_sq₀ hHLpNonneg hS).2 hHlp
    calc
      lpNorm (fun x => G x - m) (ENNReal.ofReal p) μ ^ 2 ≤
          C * (p - 1) * lpNorm H (ENNReal.ofReal p) μ ^ 2 :=
            le_trans hpow (mul_le_mul_of_nonneg_left hgradSq hcoef)
      _ ≤ C * (p - 1) *
          ((a : ℝ) + (b : ℝ) * η + (b : ℝ) *
            lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hHSq hcoef
      _ = (Real.sqrt (C * (p - 1)) *
          ((a : ℝ) + (b : ℝ) * η + (b : ℝ) *
            lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hcoef]
  have htop := hcenterMem.eLpNorm_ne_top
  change eLpNorm (fun x => G x - m) (ENNReal.ofReal p) μ ≤ _
  rw [← ENNReal.ofReal_toReal htop, toReal_eLpNorm hcenterMem.aestronglyMeasurable]
  apply ENNReal.ofReal_le_ofReal
  simpa [m, add_assoc, add_left_comm, add_comm] using hboundLp

private theorem eLpNorm_le_of_pointwise_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ≥0∞}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (B : ℝ≥0∞) (hbound : ∀ n, eLpNorm (f n) q μ ≤ B) :
    eLpNorm g q μ ≤ B := by
  calc
    eLpNorm g q μ ≤ Filter.liminf (fun n => eLpNorm (f n) q μ) atTop :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm hf g hpoint
    _ ≤ B := Filter.liminf_le_of_frequently_le
      ((Filter.Eventually.of_forall hbound).frequently)

private theorem clip_mollification_centered_limit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F)
    (a b R : NNReal)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)))
    {p : ℝ} (hp : 2 ≤ p)
    (hNorm : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => LOOConcentration.clipFunction (R : ℝ) F x -
      ∫ y, LOOConcentration.clipFunction (R : ℝ) F y ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
        ((a : ℝ) + (b : ℝ) * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
          (ENNReal.ofReal p) μ)) := by
  let η : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let G : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    LOOConcentration.clipThenMollify F (R : ℝ) (η n) x
  let Gc : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    G n x - ∫ y, G n y ∂μ
  let Fc : EuclideanSpace ℝ ι → ℝ :=
    fun x => LOOConcentration.clipFunction (R : ℝ) F x
  let Fcc : EuclideanSpace ℝ ι → ℝ := fun x => Fc x - ∫ y, Fc y ∂μ
  have hηpos (n : ℕ) : 0 < η n := by
    dsimp [η]
    positivity
  have hηle (n : ℕ) : η n ≤ 1 := by
    dsimp [η]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    rw [inv_le_one₀ (by positivity)]
    exact hn
  have hηtendsto : Tendsto η atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hden
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
    exact hinv
  have hsegF : LOOConcentration.HasLinearGrowthSegmentBound F (a : ℝ) (b : ℝ) := by
    intro x y
    simpa only [dist_eq_norm] using hseg x y
  have hsegClip : LOOConcentration.HasLinearGrowthSegmentBound Fc (a : ℝ) (b : ℝ) := by
    exact LOOConcentration.clipFunction_segmentBound hsegF
  have hpoint (x : EuclideanSpace ℝ ι) : Tendsto (fun n => G n x) atTop (𝓝 (Fc x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let K : ℝ := (a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ)
    have hK : 0 ≤ K := by positivity
    have hηK : Tendsto (fun n => η n * K) atTop (𝓝 0) := by
      simpa using hηtendsto.mul_const K
    have hsmall := hηK.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with n hn
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hc := LOOConcentration.clipThenMollify_close hF (hηpos n) hsegClip
      a.property b.property x
    have hfac : (a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ) * η n / 2 ≤ K := by
      dsimp [K]
      have hb0 : 0 ≤ (b : ℝ) := b.property
      nlinarith [mul_le_mul_of_nonneg_left (hηle n) hb0]
    calc
      |G n x - Fc x| ≤ η n * ((a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ) * η n / 2) := by
        simpa [G, Fc] using hc
      _ ≤ η n * K := mul_le_mul_of_nonneg_left hfac (le_of_lt (hηpos n))
      _ < ε := hn
  have hmeans : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, Fc x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (R : ℝ))
    · exact Filter.Eventually.of_forall fun n => by
        change AEStronglyMeasurable (LOOConcentration.clipThenMollify F (R : ℝ) (η n)) μ
        exact ((LOOConcentration.Revision.clipThenMollify_bounded_smooth F hF R
          (η n) (hηpos n)).1).continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        have hr := LOOConcentration.clipThenMollify_range hF R.property (hηpos n) x
        exact abs_le.mpr hr
    · exact integrable_const (R : ℝ)
    · exact Filter.Eventually.of_forall fun x => hpoint x
  have hGcMeas (n : ℕ) : AEStronglyMeasurable (Gc n) μ := by
    dsimp [Gc, G]
    exact ((LOOConcentration.Revision.clipThenMollify_bounded_smooth F hF R
      (η n) (hηpos n)).1.continuous.sub continuous_const).aestronglyMeasurable
  have hcenterPoint : ∀ᵐ x ∂μ, Tendsto (fun n => Gc n x) atTop (𝓝 (Fcc x)) := by
    filter_upwards [] with x
    dsimp [Gc, Fcc]
    exact (hpoint x).sub hmeans
  let V : ℝ := lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
    (ENNReal.ofReal p) μ
  let A : ℝ := Real.sqrt (C * (p - 1))
  let Bseq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (A * ((a : ℝ) + (b : ℝ) * V + (b : ℝ) * η n))
  have hBseq : Tendsto Bseq atTop
      (𝓝 (ENNReal.ofReal (A * ((a : ℝ) + (b : ℝ) * V)))) := by
    have hreal : Tendsto (fun n => A * ((a : ℝ) + (b : ℝ) * V + (b : ℝ) * η n))
        atTop (𝓝 (A * ((a : ℝ) + (b : ℝ) * V))) := by
      have hlin : Tendsto (fun n => (b : ℝ) * η n) atTop (𝓝 0) := by
        simpa [mul_comm] using hηtendsto.mul_const (b : ℝ)
      have hsum : Tendsto (fun n : ℕ =>
          ((a : ℝ) + (b : ℝ) * V) + (b : ℝ) * η n) atTop
          (𝓝 ((a : ℝ) + (b : ℝ) * V)) := by
        simpa using tendsto_const_nhds.add hlin
      simpa [mul_comm] using hsum.const_mul A
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hbound (n : ℕ) : eLpNorm (Gc n) (ENNReal.ofReal p) μ ≤ Bseq n := by
    simpa [Gc, G, Bseq, A, V] using
      mollified_centered_lp_bound μ C hC hLC F hF a b R (η n) (hηpos n)
        hseg hp hNorm
  have hlim : eLpNorm Fcc (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (A * ((a : ℝ) + (b : ℝ) * V)) := by
    have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
      (p := ENNReal.ofReal p) hGcMeas Fcc hcenterPoint
    calc
      eLpNorm Fcc (ENNReal.ofReal p) μ ≤ Filter.liminf (fun n => eLpNorm (Gc n) (ENNReal.ofReal p) μ) atTop := hfatou
      _ ≤ Filter.liminf Bseq atTop := Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
      _ = ENNReal.ofReal (A * ((a : ℝ) + (b : ℝ) * V)) := hBseq.liminf_eq
  simpa [Fcc, A, V] using hlim

/-- Conditional internal unbounded centered-Lp passage. The sole conditional
ambient-moment parent is `hNormP`; the function integrability and centered
Lp conclusion are both produced here by clipping, actual mollification, and
the two pointwise-limit/Fatou steps. -/
theorem unbounded_centered_lp_of_norm_memLp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F)
    (a b : NNReal)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)))
    {p : ℝ} (hp : 2 ≤ p)
    (hNormP : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) (ENNReal.ofReal p) μ) :
    Integrable F μ ∧
      MemLp (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
          ((a : ℝ) + (b : ℝ) *
            (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
              (ENNReal.ofReal p) μ).toReal)) := by
  have hFint := integrable_of_quadratic_segment_growth μ hmoment F hF a b (by
    intro x y
    simpa only [dist_eq_norm] using hseg x y)
  let U : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    LOOConcentration.clipValueSequence F n x
  let Uc : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    U n x - ∫ y, U n y ∂μ
  let Fc : EuclideanSpace ℝ ι → ℝ := fun x => F x - ∫ y, F y ∂μ
  have hUmeas (n : ℕ) : AEStronglyMeasurable (Uc n) μ := by
    dsimp [Uc, U]
    have hclip : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ ι =>
          LOOConcentration.clipValue ((n : ℝ) + 1) (F x)) μ :=
      (LOOConcentration.continuous_clipValue ((n : ℝ) + 1)).comp_aestronglyMeasurable
        hF.continuous.aestronglyMeasurable
    exact hclip.sub aestronglyMeasurable_const
  have hpointU (x : EuclideanSpace ℝ ι) : Tendsto (fun n => U n x) atTop (𝓝 (F x)) := by
    simpa [U] using LOOConcentration.clipValueSequence_tendsto F x
  have hmeansU : Tendsto (fun n => ∫ x, U n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
    simpa [U] using LOOConcentration.clipValueSequence_integral_tendsto hFint
  have hpointUc : ∀ᵐ x ∂μ, Tendsto (fun n => Uc n x) atTop (𝓝 (Fc x)) := by
    filter_upwards [] with x
    dsimp [Uc, Fc]
    exact (hpointU x).sub hmeansU
  have hsegF : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)) := hseg
  have hBoundU (n : ℕ) : eLpNorm (Uc n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
        ((a : ℝ) + (b : ℝ) * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
          (ENNReal.ofReal p) μ)) := by
    let R : NNReal := ⟨(n : ℝ) + 1, by positivity⟩
    have hR : (R : ℝ) = (n : ℝ) + 1 := by
      change R.val = (n : ℝ) + 1
      rfl
    have h := clip_mollification_centered_limit μ C hC hLC F hF.continuous
      a b R hsegF hp hNormP
    simpa [Uc, U, R, hR, LOOConcentration.clipFunction,
      LOOConcentration.clipValueSequence] using h
  have hOuter := eLpNorm_le_of_pointwise_limit hUmeas hpointUc
    (ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
      ((a : ℝ) + (b : ℝ) * lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
        (ENNReal.ofReal p) μ))) hBoundU
  have hFcMeas : AEStronglyMeasurable Fc μ :=
    (hF.continuous.sub continuous_const).aestronglyMeasurable
  have hFcMem : MemLp Fc (ENNReal.ofReal p) μ := by
    refine ⟨hFcMeas, ?_⟩
    exact lt_of_le_of_lt hOuter ENNReal.ofReal_lt_top
  have hnormEq : lpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
      (ENNReal.ofReal p) μ =
      (eLpNorm (fun x : EuclideanSpace ℝ ι => ‖x‖)
        (ENNReal.ofReal p) μ).toReal :=
    (toReal_eLpNorm hNormP.aestronglyMeasurable).symm
  rw [hnormEq] at hOuter
  exact ⟨hFint, hFcMem, hOuter⟩

end LOOConcentration.Revision
