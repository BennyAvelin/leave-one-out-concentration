import LOOConcentration.Geometry.LocalSlopeTruncation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Clipping and smooth approximation for linear-growth slopes

The finite-dimensional mollifier below is Mathlib's normalized compactly
supported smooth bump. The slope-dependent estimates take the source segment
bound as an input; its planned provider is `lemma:quadratic#segment`.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open ContinuousLinearMap
open scoped Topology ContDiff
open scoped Convolution

namespace LOOConcentration

/-- Clipping to the interval `[-N,N]`. -/
def clipValue (N u : ℝ) : ℝ := max (-N) (min u N)

/-- Pointwise clipping of a real-valued function. -/
def clipFunction {E : Type*} (N : ℝ) (f : E → ℝ) : E → ℝ :=
  fun x => clipValue N (f x)

theorem abs_clipValue_sub_le (N u v : ℝ) :
    |clipValue N u - clipValue N v| ≤ |u - v| := by
  unfold clipValue
  calc
    |max (-N) (min u N) - max (-N) (min v N)| =
        |max (min u N) (-N) - max (min v N) (-N)| := by
          simp only [max_comm]
    _ ≤ |min u N - min v N| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |u - v| := by simpa using abs_min_sub_min_le_max u N v N

theorem clipValue_bounds {N u : ℝ} (hN : 0 ≤ N) :
    -N ≤ clipValue N u ∧ clipValue N u ≤ N := by
  unfold clipValue
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem continuous_clipFunction {E : Type*} [TopologicalSpace E]
    {N : ℝ} {f : E → ℝ} (hf : Continuous f) :
    Continuous (clipFunction N f) := by
  unfold clipFunction clipValue
  exact continuous_const.max (hf.min continuous_const)

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

local notation "vol" => Measure.addHaar

/-- The source-style segment estimate for a function with linear-growth local
slope. -/
def HasLinearGrowthSegmentBound (f : E → ℝ) (a b : ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ dist x y * (a + b / 2 * (‖x‖ + ‖y‖))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem clipFunction_segmentBound {f : E → ℝ} {N a b : ℝ}
    (hf : HasLinearGrowthSegmentBound f a b) :
    HasLinearGrowthSegmentBound (clipFunction N f) a b := by
  intro x y
  exact (abs_clipValue_sub_le N (f x) (f y)).trans (hf x y)

/-- A smooth approximation obtained by convolving the clipped function with
Mathlib's normalized finite-dimensional bump of radius `η`. -/
noncomputable def clipThenMollify (f : E → ℝ) (N η : ℝ) : E → ℝ :=
  (ExistsContDiffBumpBase.w η) ⋆[lsmul ℝ ℝ, vol] clipFunction N f

omit [SecondCountableTopology E] in
theorem contDiff_contDiffBump_w (η : ℝ) :
    ContDiff ℝ ∞ (ExistsContDiffBumpBase.w η : E → ℝ) := by
  rw [ExistsContDiffBumpBase.w_def]
  apply ContDiff.const_smul
  exact (ExistsContDiffBumpBase.u_smooth E).comp (contDiff_const.smul contDiff_id)

omit [SecondCountableTopology E] in
theorem continuous_contDiffBump_w (η : ℝ) :
    Continuous (ExistsContDiffBumpBase.w η : E → ℝ) :=
  (contDiff_contDiffBump_w η).continuous

omit [SecondCountableTopology E] in
theorem integrable_contDiffBump_w {η : ℝ} (hη : 0 < η) :
    Integrable (ExistsContDiffBumpBase.w η : E → ℝ) vol := by
  exact (continuous_contDiffBump_w η).integrable_of_hasCompactSupport
    (ExistsContDiffBumpBase.w_compact_support E hη)

theorem contDiff_clipThenMollify {f : E → ℝ} {N η : ℝ}
    (hf : Continuous f) (hη : 0 < η) :
    ContDiff ℝ ∞ (clipThenMollify f N η) := by
  unfold clipThenMollify
  apply (ExistsContDiffBumpBase.w_compact_support E hη).contDiff_convolution_left
    (lsmul ℝ ℝ) (contDiff_contDiffBump_w η)
  exact (continuous_clipFunction hf).locallyIntegrable

omit [SecondCountableTopology E] in
theorem contDiffBump_w_integral {η : ℝ} (hη : 0 < η) :
    ∫ x : E, ExistsContDiffBumpBase.w η x ∂vol = 1 :=
  ExistsContDiffBumpBase.w_integral E hη

omit [SecondCountableTopology E] in
theorem contDiffBump_w_nonneg (η : ℝ) (x : E) :
    0 ≤ ExistsContDiffBumpBase.w η x :=
  ExistsContDiffBumpBase.w_nonneg η x

omit [SecondCountableTopology E] in
theorem contDiffBump_w_support {η : ℝ} (hη : 0 < η) :
    Function.support (ExistsContDiffBumpBase.w η : E → ℝ) = Metric.ball 0 η :=
  ExistsContDiffBumpBase.w_support E hη

theorem clipThenMollify_exists {f : E → ℝ} {N η : ℝ}
    (hf : Continuous f) (hη : 0 < η) (x : E) :
    MeasureTheory.ConvolutionExistsAt (ExistsContDiffBumpBase.w η) (clipFunction N f) x
      (lsmul ℝ ℝ) vol := by
  exact (ExistsContDiffBumpBase.w_compact_support E hη).convolutionExists_left
    (lsmul ℝ ℝ) (continuous_contDiffBump_w η) (continuous_clipFunction hf).locallyIntegrable x

theorem clipThenMollify_range {f : E → ℝ} {N η : ℝ}
    (hf : Continuous f) (hN : 0 ≤ N) (hη : 0 < η) (x : E) :
    -N ≤ clipThenMollify f N η x ∧ clipThenMollify f N η x ≤ N := by
  have hconv := clipThenMollify_exists (N := N) hf hη x
  have hlowconv : MeasureTheory.ConvolutionExistsAt (ExistsContDiffBumpBase.w η)
      (fun _ : E => -N) x (lsmul ℝ ℝ) vol := by
    exact (ExistsContDiffBumpBase.w_compact_support E hη).convolutionExists_left
      (lsmul ℝ ℝ) (continuous_contDiffBump_w η) (locallyIntegrable_const (-N)) x
  have huppconv : MeasureTheory.ConvolutionExistsAt (ExistsContDiffBumpBase.w η)
      (fun _ : E => N) x (lsmul ℝ ℝ) vol := by
    exact (ExistsContDiffBumpBase.w_compact_support E hη).convolutionExists_left
      (lsmul ℝ ℝ) (continuous_contDiffBump_w η) (locallyIntegrable_const N) x
  have hlow : (ExistsContDiffBumpBase.w η ⋆[lsmul ℝ ℝ, vol] (fun _ => -N)) x ≤
      clipThenMollify f N η x := by
    unfold clipThenMollify
    exact MeasureTheory.convolution_mono_right hlowconv hconv
      (fun t => contDiffBump_w_nonneg η t)
      (fun t => (clipValue_bounds hN).1)
  have hupp : clipThenMollify f N η x ≤
      (ExistsContDiffBumpBase.w η ⋆[lsmul ℝ ℝ, vol] (fun _ => N)) x := by
    unfold clipThenMollify
    exact MeasureTheory.convolution_mono_right hconv huppconv
      (fun t => contDiffBump_w_nonneg η t)
      (fun t => (clipValue_bounds hN).2)
  constructor
  · calc
      -N = (ExistsContDiffBumpBase.w η ⋆[lsmul ℝ ℝ, vol] (fun _ => -N)) x := by
        simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
          smul_eq_mul, integral_mul_const]
        rw [contDiffBump_w_integral hη]
        ring
      _ ≤ clipThenMollify f N η x := hlow
  · calc
      clipThenMollify f N η x ≤
          (ExistsContDiffBumpBase.w η ⋆[lsmul ℝ ℝ, vol] (fun _ => N)) x := hupp
      _ = N := by
        simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
          smul_eq_mul, integral_mul_const]
        rw [contDiffBump_w_integral hη]
        ring

omit [SecondCountableTopology E] in
theorem contDiffBump_w_integral_abs {η : ℝ} (hη : 0 < η) :
    ∫ x : E, |ExistsContDiffBumpBase.w η x| ∂vol = 1 := by
  calc
    ∫ x : E, |ExistsContDiffBumpBase.w η x| ∂vol =
        ∫ x : E, ExistsContDiffBumpBase.w η x ∂vol := by
          apply integral_congr_ae
          filter_upwards with x
          exact abs_of_nonneg (contDiffBump_w_nonneg η x)
    _ = 1 := contDiffBump_w_integral hη

theorem clipThenMollify_close {f : E → ℝ} {N η a b : ℝ}
    (hf : Continuous f) (hη : 0 < η)
    (hseg : HasLinearGrowthSegmentBound (clipFunction N f) a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : E) :
    |clipThenMollify f N η x - clipFunction N f x| ≤
      η * (a + b * ‖x‖ + b * η / 2) := by
  let ε : ℝ := η * (a + b * ‖x‖ + b * η / 2)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hnear : ∀ z ∈ Metric.ball x η,
      dist (clipFunction N f z) (clipFunction N f x) ≤ ε := by
    intro z hz
    have hdist : dist z x < η := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hdist
    have hnorm : ‖z‖ ≤ ‖x‖ + η := by
      calc
        ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + η := by linarith
    have hsum : ‖z‖ + ‖x‖ ≤ 2 * ‖x‖ + η := by linarith
    have hgrowth : a + b / 2 * (‖z‖ + ‖x‖) ≤
        a + b * ‖x‖ + b * η / 2 := by
      nlinarith [ha, hb]
    have hclip := hseg z x
    rw [dist_eq_norm] at hclip
    have hfactor : 0 ≤ a + b / 2 * (‖z‖ + ‖x‖) := by positivity
    have hfactor' : 0 ≤ a + b * ‖x‖ + b * η / 2 := by positivity
    calc
      dist (clipFunction N f z) (clipFunction N f x) =
          |clipFunction N f z - clipFunction N f x| := Real.dist_eq _ _
      _ ≤ ‖z - x‖ * (a + b / 2 * (‖z‖ + ‖x‖)) := hclip
      _ ≤ η * (a + b * ‖x‖ + b * η / 2) :=
        mul_le_mul (le_of_lt hdist) hgrowth hfactor hη.le
      _ = ε := rfl
  have hconv := MeasureTheory.dist_convolution_le'
    (L := (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) hε
    (integrable_contDiffBump_w hη)
    (by rw [contDiffBump_w_support hη])
    (continuous_clipFunction hf).aestronglyMeasurable hnear
  have hconst :
      (∫ t : E, lsmul ℝ ℝ (ExistsContDiffBumpBase.w η t)
        (clipFunction N f x) ∂vol) = clipFunction N f x := by
    change (∫ t : E, ExistsContDiffBumpBase.w η t * clipFunction N f x ∂vol) = _
    rw [integral_mul_const, contDiffBump_w_integral hη]
    ring
  have hkernelAbs : ∫ t : E, |ExistsContDiffBumpBase.w η t| ∂vol = 1 :=
    contDiffBump_w_integral_abs hη
  have hkernelNorm : ∫ t : E, ‖ExistsContDiffBumpBase.w η t‖ ∂vol = 1 := by
    calc
      ∫ t : E, ‖ExistsContDiffBumpBase.w η t‖ ∂vol =
          ∫ t : E, |ExistsContDiffBumpBase.w η t| ∂vol := by
            apply integral_congr_ae
            filter_upwards with t
            rw [Real.norm_eq_abs]
      _ = 1 := hkernelAbs
  have hL : ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have hbound :
      (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
        ∫ t : E, ‖ExistsContDiffBumpBase.w η t‖ ∂vol) * ε ≤ ε := by
    rw [hkernelNorm]
    nlinarith [hL, hε]
  have hconv' := hconv
  rw [hconst] at hconv'
  have hdist : dist (clipThenMollify f N η x) (clipFunction N f x) ≤ ε := by
    calc
      dist (clipThenMollify f N η x) (clipFunction N f x) ≤
          (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
            ∫ t : E, ‖ExistsContDiffBumpBase.w η t‖ ∂vol) * ε := by
          simpa only [clipThenMollify] using hconv'
      _ ≤ ε := hbound
  simpa only [Real.dist_eq] using hdist

theorem clipThenMollify_segmentBound {f : E → ℝ} {N η a b : ℝ}
    (hf : Continuous f) (hη : 0 < η)
    (hseg : HasLinearGrowthSegmentBound (clipFunction N f) a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasLinearGrowthSegmentBound (clipThenMollify f N η) (a + b * η) b := by
  intro x y
  have hcx := clipThenMollify_exists (N := N) hf hη x
  have hcy := clipThenMollify_exists (N := N) hf hη y
  have hix : Integrable (fun t : E => ExistsContDiffBumpBase.w η t *
      clipFunction N f (x - t)) vol := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hcx.integrable
  have hiy : Integrable (fun t : E => ExistsContDiffBumpBase.w η t *
      clipFunction N f (y - t)) vol := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hcy.integrable
  have hdiffInt : Integrable (fun t : E => ExistsContDiffBumpBase.w η t *
      (clipFunction N f (x - t) - clipFunction N f (y - t))) vol := by
    apply (hix.sub hiy).congr
    filter_upwards with t
    change ExistsContDiffBumpBase.w η t * clipFunction N f (x - t) -
      ExistsContDiffBumpBase.w η t * clipFunction N f (y - t) = _
    ring
  have hdiffAbsInt : Integrable (fun t : E =>
      |ExistsContDiffBumpBase.w η t *
        (clipFunction N f (x - t) - clipFunction N f (y - t))|) vol := by
    simpa only [Real.norm_eq_abs] using hdiffInt.norm
  let c : ℝ := a + b * η + b / 2 * (‖x‖ + ‖y‖)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hrhsInt : Integrable (fun t : E =>
      ExistsContDiffBumpBase.w η t * (dist x y * c)) vol :=
    (integrable_contDiffBump_w hη).mul_const (dist x y * c)
  have hpoint : ∀ t : E,
      |ExistsContDiffBumpBase.w η t *
        (clipFunction N f (x - t) - clipFunction N f (y - t))| ≤
      ExistsContDiffBumpBase.w η t * (dist x y * c) := by
    intro t
    by_cases ht : ExistsContDiffBumpBase.w η t = 0
    · simp [ht]
    · have htsupport : t ∈ Function.support (ExistsContDiffBumpBase.w η : E → ℝ) := by
        simpa only [Function.mem_support, ne_eq] using ht
      have htball : t ∈ Metric.ball (0 : E) η := by
        rw [contDiffBump_w_support hη] at htsupport
        exact htsupport
      have htnorm : ‖t‖ < η := by
        simpa only [mem_ball_zero_iff] using htball
      have hnx : ‖x - t‖ ≤ ‖x‖ + η := by
        calc
          ‖x - t‖ ≤ ‖x‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ ‖x‖ + η := by linarith
      have hny : ‖y - t‖ ≤ ‖y‖ + η := by
        calc
          ‖y - t‖ ≤ ‖y‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ ‖y‖ + η := by linarith
      have hsum : ‖x - t‖ + ‖y - t‖ ≤ ‖x‖ + ‖y‖ + 2 * η := by
        linarith
      have hfactor :
          a + b / 2 * (‖x - t‖ + ‖y - t‖) ≤ c := by
        have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ b / 2)
        dsimp [c]
        nlinarith
      have hdist : dist (x - t) (y - t) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      have hlocal := hseg (x - t) (y - t)
      rw [hdist] at hlocal
      have hfactorNonneg : 0 ≤ a + b / 2 * (‖x - t‖ + ‖y - t‖) := by
        positivity
      calc
        |ExistsContDiffBumpBase.w η t *
            (clipFunction N f (x - t) - clipFunction N f (y - t))| =
            ExistsContDiffBumpBase.w η t *
              |clipFunction N f (x - t) - clipFunction N f (y - t)| := by
                rw [abs_mul, abs_of_nonneg (contDiffBump_w_nonneg η t)]
        _ ≤ ExistsContDiffBumpBase.w η t *
            (dist x y * (a + b / 2 * (‖x - t‖ + ‖y - t‖))) := by
              exact mul_le_mul_of_nonneg_left hlocal
                (contDiffBump_w_nonneg η t)
        _ ≤ ExistsContDiffBumpBase.w η t * (dist x y * c) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hfactor (dist_nonneg)
              · exact contDiffBump_w_nonneg η t
  have hdiff :
      clipThenMollify f N η x - clipThenMollify f N η y =
        ∫ t : E, ExistsContDiffBumpBase.w η t *
          (clipFunction N f (x - t) - clipFunction N f (y - t)) ∂vol := by
    change
      (∫ t : E, ExistsContDiffBumpBase.w η t * clipFunction N f (x - t) ∂vol) -
        (∫ t : E, ExistsContDiffBumpBase.w η t * clipFunction N f (y - t) ∂vol) = _
    rw [← integral_sub hix hiy]
    congr 1
    funext t
    ring
  calc
    |clipThenMollify f N η x - clipThenMollify f N η y| =
        |∫ t : E, ExistsContDiffBumpBase.w η t *
          (clipFunction N f (x - t) - clipFunction N f (y - t)) ∂vol| := by
          rw [hdiff]
    _ ≤ ∫ t : E, |ExistsContDiffBumpBase.w η t *
        (clipFunction N f (x - t) - clipFunction N f (y - t))| ∂vol :=
          abs_integral_le_integral_abs
    _ ≤ ∫ t : E, ExistsContDiffBumpBase.w η t * (dist x y * c) ∂vol :=
          integral_mono hdiffAbsInt hrhsInt hpoint
    _ = dist x y * c := by
          rw [integral_mul_const, contDiffBump_w_integral hη]
          ring
    _ = dist x y * (a + b * η + b / 2 * (‖x‖ + ‖y‖)) := by
          simp only [c]

theorem clipThenMollify_fderiv_bound {f : E → ℝ} {N η a b : ℝ}
    (hf : Continuous f) (hη : 0 < η)
    (hseg : HasLinearGrowthSegmentBound (clipFunction N f) a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : E) :
    ‖fderiv ℝ (clipThenMollify f N η) x‖ ≤ a + b * η + b * ‖x‖ := by
  let C : ℝ := a + b * η + b * ‖x‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsegM := clipThenMollify_segmentBound hf hη hseg ha hb
  have hlocal : ∀ δ : ℝ, 0 < δ →
      ‖fderiv ℝ (clipThenMollify f N η) x‖ ≤ C + b * δ := by
    intro δ hδ
    let K : NNReal := ⟨C + b * δ, by positivity⟩
    have hLip : LipschitzOnWith K (clipThenMollify f N η) (Metric.ball x δ) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro u hu v hv
      have hud : dist u x < δ := Metric.mem_ball.mp hu
      have hvd : dist v x < δ := Metric.mem_ball.mp hv
      rw [dist_eq_norm] at hud hvd
      have hunorm : ‖u‖ ≤ ‖x‖ + δ := by
        calc
          ‖u‖ = ‖(u - x) + x‖ := by congr 1; abel
          _ ≤ ‖u - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + δ := by linarith
      have hvnorm : ‖v‖ ≤ ‖x‖ + δ := by
        calc
          ‖v‖ = ‖(v - x) + x‖ := by congr 1; abel
          _ ≤ ‖v - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + δ := by linarith
      have hcoeff : a + b * η + b / 2 * (‖u‖ + ‖v‖) ≤ C + b * δ := by
        dsimp [C]
        have hsum : ‖u‖ + ‖v‖ ≤ 2 * ‖x‖ + 2 * δ := by linarith
        have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ b / 2)
        nlinarith
      have hM := hsegM u v
      calc
        dist (clipThenMollify f N η u) (clipThenMollify f N η v) =
            |clipThenMollify f N η u - clipThenMollify f N η v| := Real.dist_eq _ _
        _ ≤ dist u v * (a + b * η + b / 2 * (‖u‖ + ‖v‖)) := hM
        _ ≤ dist u v * (C + b * δ) :=
          mul_le_mul_of_nonneg_left hcoeff (dist_nonneg)
        _ = (K : ℝ) * dist u v := by
          change dist u v * (C + b * δ) = (C + b * δ) * dist u v
          ring
    have hderiv := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds x hδ) hLip
    change ‖fderiv ℝ (clipThenMollify f N η) x‖ ≤ C + b * δ at hderiv
    exact hderiv
  by_cases hb0 : b = 0
  · have h := hlocal 1 zero_lt_one
    simpa [C, hb0] using h
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_contra hnot
    have hlt : C < ‖fderiv ℝ (clipThenMollify f N η) x‖ := lt_of_not_ge hnot
    let δ : ℝ :=
      (‖fderiv ℝ (clipThenMollify f N η) x‖ - C) / (2 * b)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact div_pos (by linarith) (by positivity)
    have h := hlocal δ hδ
    have hbd : b * δ =
        (‖fderiv ℝ (clipThenMollify f N η) x‖ - C) / 2 := by
      dsimp [δ]
      field_simp [ne_of_gt hbpos]
    nlinarith

end FiniteDimensional

/-- The frozen observation-local-slope clipping result, re-exported next to
the mollification construction that consumes clipping. -/
theorem observationLocalSlope_clipped_le {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (N : ℝ) (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope (clippedObservationFunction f N) z ≤
      observationLocalSlope f z :=
  observationLocalSlope_clip_le f N z

/-- Clipping a dataset-dependent function preserves its frozen local-slope
bound, using the project truncation result. -/
theorem datasetLocalSlope_clipped_le {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)})
    (N : ℝ) (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    datasetLocalSlope (clippedDatasetFunction f N) D ≤
      datasetLocalSlope f D :=
  datasetLocalSlope_clip_le f N D

end LOOConcentration
