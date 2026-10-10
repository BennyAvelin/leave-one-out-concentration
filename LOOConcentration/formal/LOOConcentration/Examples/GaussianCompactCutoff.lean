import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Expanding smooth cutoffs for locally Lipschitz functions

A fixed Mathlib `ContDiffBump` is rescaled by each strictly positive radius.
Compactly supported locally Lipschitz products are upgraded to globally
Lipschitz functions by applying the compact-domain Lipschitz theorem on a ball
around the support and using the value bound for distant pairs.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology NNReal

namespace LOOConcentration

abbrev GaussianPositiveRadius := {R : ℝ // 0 < R}

private noncomputable def gaussianCutoffBumpFun {ι : Type*} [Fintype ι]
    {c : EuclideanSpace ℝ ι} (b : ContDiffBump c) : EuclideanSpace ℝ ι → ℝ :=
  ContDiffBump.toFun b

private noncomputable def unitGaussianCutoffBump {ι : Type*} [Fintype ι] :
    ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def expandingGaussianCutoffBump {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) : ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨R.1, 2 * R.1, R.2, by nlinarith [R.2]⟩

noncomputable def expandingGaussianCutoff {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) : EuclideanSpace ℝ ι → ℝ :=
  gaussianCutoffBumpFun (expandingGaussianCutoffBump R)

private noncomputable def unitGaussianCutoff {ι : Type*} [Fintype ι] :
    EuclideanSpace ℝ ι → ℝ := gaussianCutoffBumpFun (unitGaussianCutoffBump (ι := ι))

private theorem unitGaussianCutoff_contDiff {ι : Type*} [Fintype ι] :
    ContDiff ℝ 1 (unitGaussianCutoff (ι := ι)) := by
  change ContDiff ℝ 1 (ContDiffBump.toFun (unitGaussianCutoffBump (ι := ι)))
  exact (unitGaussianCutoffBump (ι := ι)).contDiff (n := 1)

private noncomputable def unitGaussianCutoffLipschitzConstant
    {ι : Type*} [Fintype ι] : ℝ≥0 :=
  Classical.choose (show ∃ C : ℝ≥0,
    LipschitzWith C (gaussianCutoffBumpFun (unitGaussianCutoffBump (ι := ι))) from
      ContDiff.lipschitzWith_of_hasCompactSupport
        (unitGaussianCutoffBump (ι := ι)).hasCompactSupport
        (unitGaussianCutoff_contDiff (ι := ι))
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0))

private theorem unitGaussianCutoff_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith (unitGaussianCutoffLipschitzConstant (ι := ι))
      (unitGaussianCutoff (ι := ι)) :=
  Classical.choose_spec (show ∃ C : ℝ≥0,
    LipschitzWith C (gaussianCutoffBumpFun (unitGaussianCutoffBump (ι := ι))) from
      ContDiff.lipschitzWith_of_hasCompactSupport
        (unitGaussianCutoffBump (ι := ι)).hasCompactSupport
        (unitGaussianCutoff_contDiff (ι := ι))
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0))

private theorem expandingGaussianCutoff_eq_scaled_unit {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) :
    expandingGaussianCutoff (ι := ι) R x = unitGaussianCutoff (R.1⁻¹ • x) := by
  simp only [expandingGaussianCutoff, unitGaussianCutoff, gaussianCutoffBumpFun,
    ContDiffBump.toFun, Function.comp_apply, expandingGaussianCutoffBump,
    unitGaussianCutoffBump]
  congr 1
  · field_simp [R.2.ne']
  · simp [smul_smul]

theorem expandingGaussianCutoff_mem_Icc {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) :
    expandingGaussianCutoff (ι := ι) R x ∈ Set.Icc 0 1 := by
  change 0 ≤ gaussianCutoffBumpFun (expandingGaussianCutoffBump (ι := ι) R) x ∧
    gaussianCutoffBumpFun (expandingGaussianCutoffBump (ι := ι) R) x ≤ 1
  exact ⟨(expandingGaussianCutoffBump (ι := ι) R).nonneg' x,
    (expandingGaussianCutoffBump (ι := ι) R).le_one⟩

theorem expandingGaussianCutoff_eq_one_of_norm_le {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) (hx : ‖x‖ ≤ R.1) :
    expandingGaussianCutoff (ι := ι) R x = 1 := by
  change gaussianCutoffBumpFun (expandingGaussianCutoffBump (ι := ι) R) x = 1
  apply (expandingGaussianCutoffBump (ι := ι) R).one_of_mem_closedBall
  rw [mem_closedBall_iff_norm]
  simpa [expandingGaussianCutoffBump] using hx

theorem expandingGaussianCutoff_support_eq {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) :
    Function.support (expandingGaussianCutoff (ι := ι) R) =
      Metric.ball (0 : EuclideanSpace ℝ ι) (2 * R.1) := by
  change Function.support (gaussianCutoffBumpFun (expandingGaussianCutoffBump (ι := ι) R)) = _
  exact (expandingGaussianCutoffBump (ι := ι) R).support_eq

theorem expandingGaussianCutoff_hasCompactSupport {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) : HasCompactSupport (expandingGaussianCutoff (ι := ι) R) := by
  change HasCompactSupport (gaussianCutoffBumpFun (expandingGaussianCutoffBump (ι := ι) R))
  exact (expandingGaussianCutoffBump (ι := ι) R).hasCompactSupport

theorem expandingGaussianCutoff_contDiff {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) : ContDiff ℝ 1 (expandingGaussianCutoff (ι := ι) R) := by
  change ContDiff ℝ 1 (ContDiffBump.toFun (expandingGaussianCutoffBump (ι := ι) R))
  exact (expandingGaussianCutoffBump (ι := ι) R).contDiff (n := 1)

private theorem expandingGaussianCutoff_lipschitz {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) :
    LipschitzWith
      (Real.toNNReal ((unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) / R.1))
      (expandingGaussianCutoff (ι := ι) R) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq]
  rw [expandingGaussianCutoff_eq_scaled_unit (ι := ι), expandingGaussianCutoff_eq_scaled_unit (ι := ι)]
  let c : ℝ := R.1⁻¹
  have hc : 0 < c := by dsimp [c]; exact inv_pos.mpr R.2
  calc
    |unitGaussianCutoff (c • x) - unitGaussianCutoff (c • y)| =
        dist (unitGaussianCutoff (c • x)) (unitGaussianCutoff (c • y)) :=
          (Real.dist_eq _ _).symm
    _ ≤ (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) * dist (c • x) (c • y) :=
      (unitGaussianCutoff_lipschitz (ι := ι)).dist_le_mul _ _
    _ ≤ (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) *
          (‖c‖ * dist x y) :=
      mul_le_mul_of_nonneg_left (dist_smul_le c x y)
        (unitGaussianCutoffLipschitzConstant (ι := ι)).coe_nonneg
    _ = (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) / R.1 * dist x y := by
      rw [Real.norm_eq_abs, abs_of_pos hc]
      dsimp [c]
      ring

theorem expandingGaussianCutoff_fderiv_norm_le {ι : Type*} [Fintype ι]
    (R : GaussianPositiveRadius) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (expandingGaussianCutoff (ι := ι) R) x‖ ≤
      (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) / R.1 := by
  have h := norm_fderiv_le_of_lipschitz ℝ
    (expandingGaussianCutoff_lipschitz (ι := ι) R) (x₀ := x)
  rw [Real.coe_toNNReal _ (div_nonneg
    (unitGaussianCutoffLipschitzConstant (ι := ι)).coe_nonneg R.2.le)] at h
  exact h

private theorem gaussianPositiveRadius_tendsto_coe :
    Tendsto (fun R : GaussianPositiveRadius => R.1) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  refine Filter.eventually_atTop.2
    ⟨⟨max b 0 + 1, by positivity⟩, fun R hR => ?_⟩
  exact le_trans (le_trans (le_max_left b 0) (by linarith)) hR

theorem expandingGaussianCutoff_eventually_eq_one {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    ∀ᶠ R : GaussianPositiveRadius in atTop, expandingGaussianCutoff (ι := ι) R x = 1 := by
  filter_upwards
    [gaussianPositiveRadius_tendsto_coe.eventually (eventually_gt_atTop ‖x‖)] with R hR
  exact expandingGaussianCutoff_eq_one_of_norm_le R x (le_of_lt hR)

theorem expandingGaussianCutoff_tendsto_one {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun R : GaussianPositiveRadius => expandingGaussianCutoff (ι := ι) R x)
      atTop (𝓝 1) :=
  tendsto_nhds_of_eventually_eq (expandingGaussianCutoff_eventually_eq_one x)

theorem expandingGaussianCutoff_fderiv_norm_tendsto_zero {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun R : GaussianPositiveRadius =>
      ‖fderiv ℝ (expandingGaussianCutoff (ι := ι) R) x‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun R => norm_nonneg _) (fun R => expandingGaussianCutoff_fderiv_norm_le R x) ?_
  have hlim : Tendsto
      (fun R : GaussianPositiveRadius =>
        (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ) / R.1)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.comp gaussianPositiveRadius_tendsto_coe).const_mul
        (unitGaussianCutoffLipschitzConstant (ι := ι) : ℝ)
  exact hlim

noncomputable def boundedCompactCutoffApproximation {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius)
    (A : ℝ) (_hA : 0 < A) : EuclideanSpace ℝ ι → ℝ :=
  fun x => max (-A) (min (u x) A) * expandingGaussianCutoff (ι := ι) R x

private theorem locallyLipschitz_valueClip {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (hu : LocallyLipschitz u) (A : ℝ) :
    LocallyLipschitz (fun x => max (-A) (min (u x) A)) :=
  LocallyLipschitz.const_max (hu.min_const A) (-A)

private theorem valueClip_abs_le {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (A : ℝ) (hA : 0 < A)
    (x : EuclideanSpace ℝ ι) : |max (-A) (min (u x) A)| ≤ A := by
  rw [abs_le]
  constructor
  · exact (le_max_left _ _).trans (by linarith)
  · exact (max_le_iff.mpr ⟨by linarith, min_le_right _ _⟩)

theorem boundedCompactCutoffApproximation_abs_le {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius)
    (A : ℝ) (hA : 0 < A) (x : EuclideanSpace ℝ ι) :
    |boundedCompactCutoffApproximation u R A hA x| ≤ A := by
  have hu : |max (-A) (min (u x) A)| ≤ A := by
    rw [abs_le]
    constructor
    · exact (le_max_left _ _).trans (by linarith)
    · exact (max_le_iff.mpr ⟨by linarith, min_le_right _ _⟩)
  obtain ⟨hχ₀, hχ₁⟩ := expandingGaussianCutoff_mem_Icc (ι := ι) R x
  have hχabs : |expandingGaussianCutoff (ι := ι) R x| ≤ 1 :=
    abs_le.mpr ⟨by linarith, hχ₁⟩
  rw [boundedCompactCutoffApproximation, abs_mul]
  calc
    |max (-A) (min (u x) A)| * |expandingGaussianCutoff (ι := ι) R x| ≤ A * 1 :=
      mul_le_mul hu hχabs (abs_nonneg _) hA.le
    _ = A := mul_one _

private theorem boundedCompactCutoffApproximation_locallyLipschitz {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (hu : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (A : ℝ) (hA : 0 < A) :
    LocallyLipschitz (boundedCompactCutoffApproximation u R A hA) := by
  change LocallyLipschitz (fun x => max (-A) (min (u x) A) *
    expandingGaussianCutoff (ι := ι) R x)
  have hclip : LocallyLipschitz
      (fun x : EuclideanSpace ℝ ι => max (-A) (min (u x) A)) :=
    locallyLipschitz_valueClip u hu A
  have hcut : LocallyLipschitz
      (fun x : EuclideanSpace ℝ ι => expandingGaussianCutoff (ι := ι) R x) :=
    (expandingGaussianCutoff_lipschitz (ι := ι) R).locallyLipschitz
  intro x
  obtain ⟨Kf, t, ht, hKf⟩ := hclip x
  obtain ⟨Kχ, s, hs, hKχ⟩ := hcut x
  let V : Set (EuclideanSpace ℝ ι) := t ∩ s
  refine ⟨Real.toNNReal (A * (Kχ : ℝ) + (Kf : ℝ)), V, inter_mem ht hs, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro a ha b hb
  have hclipdiff : |max (-A) (min (u a) A) - max (-A) (min (u b) A)| ≤
      (Kf : ℝ) * dist a b := by
    rw [← Real.dist_eq]
    exact hKf.dist_le_mul a ha.1 b hb.1
  have hcutdiff : |expandingGaussianCutoff (ι := ι) R a -
      expandingGaussianCutoff (ι := ι) R b| ≤ (Kχ : ℝ) * dist a b := by
    rw [← Real.dist_eq]
    exact hKχ.dist_le_mul a ha.2 b hb.2
  have hclipa := valueClip_abs_le u A hA a
  obtain ⟨hχa0, hχa1⟩ := expandingGaussianCutoff_mem_Icc (ι := ι) R a
  obtain ⟨hχb0, hχb1⟩ := expandingGaussianCutoff_mem_Icc (ι := ι) R b
  have hχaabs : |expandingGaussianCutoff (ι := ι) R a| ≤ 1 :=
    abs_le.mpr ⟨by linarith, hχa1⟩
  have hχbabs : |expandingGaussianCutoff (ι := ι) R b| ≤ 1 :=
    abs_le.mpr ⟨by linarith, hχb1⟩
  have hiden :
      max (-A) (min (u a) A) * expandingGaussianCutoff (ι := ι) R a -
        max (-A) (min (u b) A) * expandingGaussianCutoff (ι := ι) R b =
      max (-A) (min (u a) A) *
          (expandingGaussianCutoff (ι := ι) R a - expandingGaussianCutoff (ι := ι) R b) +
        (max (-A) (min (u a) A) - max (-A) (min (u b) A)) *
          expandingGaussianCutoff (ι := ι) R b := by ring
  rw [Real.dist_eq, hiden]
  calc
    |max (-A) (min (u a) A) *
        (expandingGaussianCutoff (ι := ι) R a - expandingGaussianCutoff (ι := ι) R b) +
      (max (-A) (min (u a) A) - max (-A) (min (u b) A)) *
        expandingGaussianCutoff (ι := ι) R b|
        ≤ |max (-A) (min (u a) A) *
            (expandingGaussianCutoff (ι := ι) R a - expandingGaussianCutoff (ι := ι) R b)| +
          |(max (-A) (min (u a) A) - max (-A) (min (u b) A)) *
            expandingGaussianCutoff (ι := ι) R b| := abs_add_le _ _
    _ = |max (-A) (min (u a) A)| *
        |expandingGaussianCutoff (ι := ι) R a - expandingGaussianCutoff (ι := ι) R b| +
      |max (-A) (min (u a) A) - max (-A) (min (u b) A)| *
        |expandingGaussianCutoff (ι := ι) R b| := by rw [abs_mul, abs_mul]
    _ ≤ A * ((Kχ : ℝ) * dist a b) + ((Kf : ℝ) * dist a b) * 1 := by
          exact add_le_add
            (mul_le_mul hclipa hcutdiff (abs_nonneg _) (by positivity))
            (mul_le_mul hclipdiff hχbabs (abs_nonneg _) (by positivity))
    _ = (A * (Kχ : ℝ) + (Kf : ℝ)) * dist a b := by ring

theorem boundedCompactCutoffApproximation_hasCompactSupport {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius)
    (A : ℝ) (hA : 0 < A) :
    HasCompactSupport (boundedCompactCutoffApproximation u R A hA) := by
  change HasCompactSupport (fun x => max (-A) (min (u x) A) *
    expandingGaussianCutoff (ι := ι) R x)
  exact HasCompactSupport.mul_left
    (f' := expandingGaussianCutoff (ι := ι) R)
    (expandingGaussianCutoff_hasCompactSupport (ι := ι) R)

private theorem boundedCompactCutoffApproximation_support_ball_subset {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius)
    (A : ℝ) (hA : 0 < A) {x : EuclideanSpace ℝ ι}
    (hx : boundedCompactCutoffApproximation u R A hA x ≠ 0) :
    x ∈ Metric.ball 0 (2 * R.1) := by
  have hχ : expandingGaussianCutoff (ι := ι) R x ≠ 0 := by
    intro hzero
    apply hx
    simp [boundedCompactCutoffApproximation, hzero]
  rw [← expandingGaussianCutoff_support_eq (ι := ι)]
  exact Function.mem_support.mpr hχ

private theorem boundedCompactCutoffApproximation_mem_large_closedBall {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (R : GaussianPositiveRadius)
    (A : ℝ) (hA : 0 < A) {x : EuclideanSpace ℝ ι}
    (hx : boundedCompactCutoffApproximation u R A hA x ≠ 0) :
    x ∈ Metric.closedBall 0 (2 * R.1) := by
  have hxball := boundedCompactCutoffApproximation_support_ball_subset u R A hA hx
  rw [Metric.mem_ball, dist_zero_right] at hxball
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hxball.le

private theorem norm_le_of_dist_le_one_of_mem_ball {ι : Type*} [Fintype ι]
    {x y : EuclideanSpace ℝ ι} {r : ℝ}
    (hx : ‖x‖ < r) (hxy : dist x y ≤ 1) : ‖y‖ ≤ r + 1 := by
  calc
    ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel
    _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    _ = dist x y + ‖x‖ := by rw [dist_eq_norm]; simp [norm_sub_rev]
    _ ≤ 1 + r := add_le_add hxy hx.le
    _ = r + 1 := by ring

private theorem boundedCompactCutoffApproximation_norm_le_large_closedBall_of_ne_zero
    {ι : Type*} [Fintype ι] (u : EuclideanSpace ℝ ι → ℝ)
    (R : GaussianPositiveRadius) (A : ℝ) (hA : 0 < A)
    {x y : EuclideanSpace ℝ ι}
    (hx : boundedCompactCutoffApproximation u R A hA x ≠ 0)
    (hxy : dist x y ≤ 1) :
    y ∈ Metric.closedBall 0 (2 * R.1 + 1) := by
  have hxball := boundedCompactCutoffApproximation_support_ball_subset u R A hA hx
  rw [Metric.mem_ball, dist_zero_right] at hxball
  have hynorm := norm_le_of_dist_le_one_of_mem_ball hxball hxy
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith

theorem boundedCompactCutoffApproximation_exists_globalLipschitz
    {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι → ℝ) (hu : LocallyLipschitz u)
    (R : GaussianPositiveRadius) (A : ℝ) (hA : 0 < A) :
    ∃ L : ℝ≥0, LipschitzWith L (boundedCompactCutoffApproximation u R A hA) := by
  let f := boundedCompactCutoffApproximation u R A hA
  let S : Set (EuclideanSpace ℝ ι) := Metric.closedBall 0 (2 * R.1 + 1)
  have hcompact : IsCompact S := by
    dsimp [S]
    exact isCompact_closedBall _ _
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact
    ((boundedCompactCutoffApproximation_locallyLipschitz u hu R A hA).locallyLipschitzOn)
  refine ⟨Real.toNNReal ((K : ℝ) + 2 * A), ?_⟩
  apply LipschitzWith.of_dist_le' (K := (K : ℝ) + 2 * A)
  intro x y
  by_cases hdist : dist x y ≤ 1
  · by_cases hfx : f x = 0
    · by_cases hfy : f y = 0
      · change dist (f x) (f y) ≤ ((K : ℝ) + 2 * A) * dist x y
        rw [hfx, hfy]
        simp only [dist_self]
        exact mul_nonneg (by linarith [K.coe_nonneg, hA]) dist_nonneg
      · have hyS : y ∈ S := by
          have hysmall := boundedCompactCutoffApproximation_mem_large_closedBall
            u R A hA hfy
          rw [Metric.mem_closedBall, dist_zero_right] at hysmall
          change dist y 0 ≤ 2 * R.1 + 1
          rw [dist_zero_right]
          exact le_trans hysmall (by linarith)
        have hxS : x ∈ S := by
          have hdist' : dist y x ≤ 1 := by simpa [dist_comm] using hdist
          exact boundedCompactCutoffApproximation_norm_le_large_closedBall_of_ne_zero
            u R A hA (x := y) (y := x) hfy hdist'
        change dist (f x) (f y) ≤ ((K : ℝ) + 2 * A) * dist x y
        calc
          dist (f x) (f y) ≤ (K : ℝ) * dist x y := hK.dist_le_mul x hxS y hyS
          _ ≤ ((K : ℝ) + 2 * A) * dist x y := by
            exact mul_le_mul_of_nonneg_right (by linarith [K.coe_nonneg, hA]) dist_nonneg
    · have hxS : x ∈ S := by
        have hxsmall := boundedCompactCutoffApproximation_mem_large_closedBall
          u R A hA hfx
        rw [Metric.mem_closedBall, dist_zero_right] at hxsmall
        change dist x 0 ≤ 2 * R.1 + 1
        rw [dist_zero_right]
        exact le_trans hxsmall (by linarith)
      have hyS : y ∈ S := by
        exact boundedCompactCutoffApproximation_norm_le_large_closedBall_of_ne_zero
          u R A hA hfx hdist
      change dist (f x) (f y) ≤ ((K : ℝ) + 2 * A) * dist x y
      calc
        dist (f x) (f y) ≤ (K : ℝ) * dist x y := hK.dist_le_mul x hxS y hyS
        _ ≤ ((K : ℝ) + 2 * A) * dist x y := by
          exact mul_le_mul_of_nonneg_right (by linarith [K.coe_nonneg, hA]) dist_nonneg
  · have habs : |f x - f y| ≤ 2 * A := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ A + A := add_le_add
          (boundedCompactCutoffApproximation_abs_le u R A hA x)
          (boundedCompactCutoffApproximation_abs_le u R A hA y)
        _ = 2 * A := by ring
    change dist (f x) (f y) ≤ ((K : ℝ) + 2 * A) * dist x y
    rw [Real.dist_eq]
    calc
      |f x - f y| ≤ 2 * A := habs
      _ ≤ ((K : ℝ) + 2 * A) * dist x y := by
        have hdist' : 1 < dist x y := lt_of_not_ge hdist
        have hcoeff : 2 * A ≤ (K : ℝ) + 2 * A := by
          linarith [K.coe_nonneg]
        calc
          2 * A ≤ (2 * A) * dist x y := by nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * A) (sub_nonneg.mpr (le_of_lt hdist'))]
          _ ≤ ((K : ℝ) + 2 * A) * dist x y :=
            mul_le_mul_of_nonneg_right hcoeff (dist_nonneg)

#print axioms expandingGaussianCutoff_mem_Icc
#print axioms expandingGaussianCutoff_eq_one_of_norm_le
#print axioms expandingGaussianCutoff_fderiv_norm_le
#print axioms expandingGaussianCutoff_tendsto_one
#print axioms expandingGaussianCutoff_fderiv_norm_tendsto_zero
#print axioms boundedCompactCutoffApproximation_abs_le
#print axioms boundedCompactCutoffApproximation_hasCompactSupport
#print axioms boundedCompactCutoffApproximation_exists_globalLipschitz

end LOOConcentration
