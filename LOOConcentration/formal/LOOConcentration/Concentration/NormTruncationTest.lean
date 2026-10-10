import LOOConcentration.Concentration.NormTruncationEnergy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Exponential tests of the bounded squared-norm truncation

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version),
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem realExp_lipschitzOn_Icc (r : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp r)) Real.exp (Set.Icc (-r) r) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact Real.differentiableAt_exp
  · intro x hx
    rw [Real.deriv_exp]
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg x),
      Real.coe_toNNReal (Real.exp r) (Real.exp_nonneg r)]
    exact Real.exp_le_exp.mpr hx.2
  · exact convex_Icc (-r) r

private theorem realExp_abs_diff_le {r x y : ℝ}
    (hx : |x| ≤ r) (hy : |y| ≤ r) :
    |Real.exp x - Real.exp y| ≤ Real.exp r * |x - y| := by
  have hx' : x ∈ Set.Icc (-r) r := by
    rw [abs_le] at hx
    exact hx
  have hy' : y ∈ Set.Icc (-r) r := by
    rw [abs_le] at hy
    exact hy
  have h := (realExp_lipschitzOn_Icc r).dist_le_mul x hx' y hy'
  simpa only [Real.dist_eq, Real.norm_eq_abs, Real.coe_toNNReal
    (Real.exp r) (Real.exp_nonneg r)] using h

private theorem realExp_abs_diff_le_exp_max (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ Real.exp (max x y) * |x - y| := by
  rcases le_total x y with hxy | hyx
  · have hderiv : ∀ z ∈ interior (Set.Icc x y),
        deriv Real.exp z ≤ Real.exp y := by
      intro z hz
      rw [Real.deriv_exp]
      exact Real.exp_le_exp.mpr (interior_subset hz).2
    have hmean := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le
      Real.continuous_exp.continuousOn Real.differentiable_exp.differentiableOn
      hderiv x (Set.left_mem_Icc.2 hxy) y (Set.right_mem_Icc.2 hxy) hxy
    rw [max_eq_right hxy]
    have hexp : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
    calc
      |Real.exp x - Real.exp y| = Real.exp y - Real.exp x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hexp)]
        ring
      _ ≤ Real.exp y * |x - y| := by
        simpa [abs_of_nonpos (sub_nonpos.mpr hxy)] using hmean
  · have hderiv : ∀ z ∈ interior (Set.Icc y x),
        deriv Real.exp z ≤ Real.exp x := by
      intro z hz
      rw [Real.deriv_exp]
      exact Real.exp_le_exp.mpr (interior_subset hz).2
    have hmean := (convex_Icc y x).image_sub_le_mul_sub_of_deriv_le
      Real.continuous_exp.continuousOn Real.differentiable_exp.differentiableOn
      hderiv y (Set.left_mem_Icc.2 hyx) x (Set.right_mem_Icc.2 hyx) hyx
    rw [max_eq_left hyx]
    have hexp : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr hyx
    calc
      |Real.exp x - Real.exp y| = Real.exp x - Real.exp y :=
        abs_of_nonneg (sub_nonneg.mpr hexp)
      _ ≤ Real.exp x * |x - y| := by
        simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using hmean

/-- The frozen locally Lipschitz test `D ↦ exp (s Q_A(D) / 2)`. -/
noncomputable def normTruncationExpTest {k m n : ℕ} {A : ℝ}
    (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s) :
    {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)} := by
  let Q := normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA
  let c : ℝ := s / 2
  let R : ℝ := c * A
  refine ⟨fun D => Real.exp (c * Q.1 D), ?_⟩
  intro D
  obtain ⟨U, hU, C, hC, hLip⟩ := Q.2 D
  refine ⟨U, hU, Real.exp R * (c * C), ?_, ?_⟩
  · dsimp [R, c]
    positivity
  · intro E hE F hF
    have hc : 0 ≤ c := by dsimp [c]; linarith
    have hQE : 0 ≤ Q.1 E := normTruncation_nonneg hA E
    have hQF : 0 ≤ Q.1 F := normTruncation_nonneg hA F
    have hQEu : Q.1 E ≤ A := normTruncation_le hA E
    have hQFu : Q.1 F ≤ A := normTruncation_le hA F
    have hargE : |c * Q.1 E| ≤ R := by
      rw [abs_of_nonneg (mul_nonneg hc hQE)]
      dsimp [R]
      exact mul_le_mul_of_nonneg_left hQEu hc
    have hargF : |c * Q.1 F| ≤ R := by
      rw [abs_of_nonneg (mul_nonneg hc hQF)]
      dsimp [R]
      exact mul_le_mul_of_nonneg_left hQFu hc
    have hexp := realExp_abs_diff_le (r := R) hargE hargF
    have hQ := hLip E hE F hF
    calc
      |Real.exp (c * Q.1 E) - Real.exp (c * Q.1 F)|
          ≤ Real.exp R * |c * Q.1 E - c * Q.1 F| := hexp
      _ = Real.exp R * (c * |Q.1 E - Q.1 F|) := by
        rw [show c * Q.1 E - c * Q.1 F = c * (Q.1 E - Q.1 F) by ring,
          abs_mul, abs_of_nonneg hc]
      _ ≤ Real.exp R * (c * (C * datasetNorm (E - F))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hQ hc) (Real.exp_nonneg _)
      _ = (Real.exp R * (c * C)) * datasetNorm (E - F) := by ring

/-- The local slope of the exponential test obeys the pointwise chain rule. -/
theorem normTruncationExpTest_slope_le {k m n : ℕ} {A : ℝ}
    (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    datasetLocalSlope (normTruncationExpTest hA s hs) D ≤
      (s / 2 * Real.exp (s * normTruncation A hA D / 2)) *
        datasetLocalSlope (normTruncation_locallyLipschitz hA) D := by
  let F := normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA
  let U := normTruncationExpTest (k := k) (m := m) (n := n) hA s hs
  let c : ℝ := s / 2
  let p : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ := fun E =>
    c * Real.exp (max (c * F.1 E) (c * F.1 D))
  let q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ := fun E =>
    |F.1 E - F.1 D| / datasetNorm (E - D)
  have hcontF : Continuous F.1 := (normTruncation_contDiff A hA).continuous
  have hcF : Tendsto (fun E : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
      c * F.1 E) (𝓝 D) (𝓝 (c * F.1 D)) := by
    exact (continuous_const.mul hcontF).continuousAt.tendsto
  have hmax : Tendsto (fun E : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
      max (c * F.1 E) (c * F.1 D)) (𝓝 D) (𝓝 (c * F.1 D)) := by
    simpa using hcF.max (tendsto_const_nhds :
      Tendsto (fun _ : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        c * F.1 D) (𝓝 D) (𝓝 (c * F.1 D)))
  have hp : Tendsto p (𝓝 D) (𝓝 (c * Real.exp (c * F.1 D)) : Filter ℝ) := by
    dsimp [p]
    exact tendsto_const_nhds.mul
      (Real.continuous_exp.continuousAt.tendsto.comp hmax)
  have hp' : Tendsto p (𝓝[≠] D) (𝓝 (c * Real.exp (c * F.1 D))) :=
    hp.mono_left nhdsWithin_le_nhds
  have hpLimsup : limsup p (𝓝[≠] D) = c * Real.exp (c * F.1 D) := hp'.limsup_eq
  have hquot : ∀ E,
      |U.1 E - U.1 D| / datasetNorm (E - D) ≤ p E * q E := by
    intro E
    by_cases hED : E = D
    · subst E
      simp [q]
    · have hden : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hED
      have hnum := realExp_abs_diff_le_exp_max (c * F.1 E) (c * F.1 D)
      have hscale : |c * F.1 E - c * F.1 D| = c * |F.1 E - F.1 D| := by
        rw [show c * F.1 E - c * F.1 D = c * (F.1 E - F.1 D) by ring,
          abs_mul, abs_of_nonneg (by dsimp [c]; linarith : 0 ≤ c)]
      rw [← mul_div_assoc, div_le_div_iff₀ hden hden]
      simpa [U, normTruncationExpTest, p, q, hscale, c, mul_assoc,
        mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hnum hden.le
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hpNonneg : ∃ᶠ E in 𝓝[≠] D, 0 ≤ p E :=
    Filter.Frequently.of_forall fun E => by dsimp [p]; positivity
  have hpBound := hp'.isBoundedUnder_le
  have hqNonneg : 0 ≤ᶠ[𝓝[≠] D] q :=
    Filter.Eventually.of_forall fun E => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hqBound : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) q := by
    simpa [q] using datasetSlope_bounded F D
  have hprodBound := isBoundedUnder_le_mul_of_nonneg hpNonneg hpBound hqNonneg hqBound
  have hUlower := datasetSlope_cobounded U D
  have hlim := limsup_le_limsup (Filter.Eventually.of_forall hquot) hUlower hprodBound
  have hmul := limsup_mul_le hpNonneg hpBound hqNonneg hqBound
  have hpoint : (fun E : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
      p E * q E) = p * q := by
    funext E
    rfl
  rw [hpoint] at hlim
  rw [hpLimsup] at hmul
  have hfinal : limsup
      (fun E => |U.1 E - U.1 D| / datasetNorm (E - D)) (𝓝[≠] D) ≤
        (c * Real.exp (c * F.1 D)) *
          limsup q (𝓝[≠] D) := hlim.trans hmul
  have harg : c * F.1 D = s * normTruncation A hA D / 2 := by
    dsimp [c, F, normTruncation_locallyLipschitz]
    ring
  rw [harg] at hfinal
  simpa [datasetLocalSlope, U, F, q, c, mul_assoc] using hfinal

/-- The squared local slope has the exact truncation energy majorant. -/
theorem normTruncationExpTest_slope_sq_le {k m n : ℕ} {A : ℝ}
    (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    (datasetLocalSlope (normTruncationExpTest hA s hs) D) ^ 2 ≤
      s ^ 2 * Real.exp (s * normTruncation A hA D) * normTruncation A hA D := by
  let Q := normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA
  let U := normTruncationExpTest (k := k) (m := m) (n := n) hA s hs
  have hSlopeNonneg := datasetLocalSlope_nonneg U D
  have hQSlopeNonneg := datasetLocalSlope_nonneg Q D
  have hchain := normTruncationExpTest_slope_le hA s hs D
  have hQbound := normTruncation_localSlope_sq_le hA D
  have hc : 0 ≤ s / 2 := by positivity
  have hexp : Real.exp (s * normTruncation A hA D / 2) ^ 2 =
      Real.exp (s * normTruncation A hA D) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq := (sq_le_sq₀ hSlopeNonneg
    (mul_nonneg (mul_nonneg hc (Real.exp_nonneg _)) hQSlopeNonneg)).2 hchain
  calc
    (datasetLocalSlope U D) ^ 2 ≤
        ((s / 2 * Real.exp (s * normTruncation A hA D / 2)) *
          datasetLocalSlope Q D) ^ 2 := hsq
    _ = (s / 2) ^ 2 * Real.exp (s * normTruncation A hA D / 2) ^ 2 *
          (datasetLocalSlope Q D) ^ 2 := by ring
    _ = (s / 2) ^ 2 * Real.exp (s * normTruncation A hA D) *
          (datasetLocalSlope Q D) ^ 2 := by rw [hexp]
    _ ≤ (s / 2) ^ 2 * Real.exp (s * normTruncation A hA D) *
          (4 * normTruncation A hA D) := by
      exact mul_le_mul_of_nonneg_left hQbound
        (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    _ = s ^ 2 * Real.exp (s * normTruncation A hA D) *
          normTruncation A hA D := by ring

/-- Conditional finite-energy admission for the actual product law. The only
remaining premise is strong measurability of the limsup-defined squared slope. -/
theorem integrable_normTruncationExpTest_slope_sq_of_aestronglyMeasurable
    {k m n : ℕ} {A : ℝ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s)
    (hMeas : AEStronglyMeasurable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        datasetLocalSlope (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        datasetLocalSlope (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let K : ℝ := s ^ 2 * Real.exp (s * A) * A
  apply Integrable.of_bound hMeas K
  filter_upwards with D
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hQ0 := normTruncation_nonneg hA D
  have hQA := normTruncation_le hA D
  have hexp : Real.exp (s * normTruncation A hA D) ≤ Real.exp (s * A) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hQA hs)
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  calc
    datasetLocalSlope
        (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2 ≤
        s ^ 2 * Real.exp (s * normTruncation A hA D) * normTruncation A hA D :=
        normTruncationExpTest_slope_sq_le hA s hs D
    _ ≤ s ^ 2 * Real.exp (s * A) * normTruncation A hA D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hs2) hQ0
    _ ≤ K := by
      dsimp [K]
      exact mul_le_mul_of_nonneg_left hQA
        (mul_nonneg hs2 (Real.exp_nonneg _))

end LOOConcentration
