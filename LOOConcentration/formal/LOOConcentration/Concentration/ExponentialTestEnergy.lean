import LOOConcentration.Concentration.SegmentIntegrability
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Finite-energy estimates for exponential dataset tests

For a bounded locally Lipschitz dataset function, exponentiation preserves
local Lipschitzness. The bounded range gives a global comparison of frozen
local slopes and a square-integrable pointwise majorant under the product
sample law.
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

/-- The exponential is Lipschitz on any symmetric bounded interval, with the
endpoint exponential as constant. -/
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

/-- The exponential test function, equipped with its local Lipschitz proof. -/
noncomputable def expTiltedTestFunction {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B : ℝ)
    (_hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) :
    LocallyLipschitzDataFunction k m n := by
  let c : ℝ := lam / 2
  let R : ℝ := |c| * B
  refine ⟨fun D => Real.exp (c * F.1 D), ?_⟩
  intro D
  obtain ⟨U, hU, C, hC, hLip⟩ := F.2 D
  let K : ℝ := |c| * Real.exp R * C
  refine ⟨U, hU, K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro E hE G hG
    have hED : |c * F.1 E| ≤ R := by
      dsimp [R, c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hBound E) (abs_nonneg _)
    have hGD : |c * F.1 G| ≤ R := by
      dsimp [R, c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hBound G) (abs_nonneg _)
    have hexp := realExp_abs_diff_le (r := R) hED hGD
    have hF := hLip E hE G hG
    calc
      |Real.exp (c * F.1 E) - Real.exp (c * F.1 G)|
          ≤ Real.exp R * |c * F.1 E - c * F.1 G| := hexp
      _ = Real.exp R * (|c| * |F.1 E - F.1 G|) := by rw [show
          c * F.1 E - c * F.1 G = c * (F.1 E - F.1 G) by ring, abs_mul]
      _ ≤ Real.exp R * (|c| * (C * datasetNorm (E - G))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hF (abs_nonneg c)) (Real.exp_nonneg R)
      _ = K * datasetNorm (E - G) := by dsimp [K]; ring

private theorem expTiltedTestFunction_abs_diff_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) (E D : DataCarrier k m n) :
    |(expTiltedTestFunction F lam B hB hBound).1 E -
      (expTiltedTestFunction F lam B hB hBound).1 D| ≤
      (|lam / 2| * Real.exp (|lam / 2| * B)) * |F.1 E - F.1 D| := by
  let c : ℝ := lam / 2
  let R : ℝ := |c| * B
  have hE : |c * F.1 E| ≤ R := by
    dsimp [R, c]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hBound E) (abs_nonneg _)
  have hD : |c * F.1 D| ≤ R := by
    dsimp [R, c]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hBound D) (abs_nonneg _)
  have h := realExp_abs_diff_le hE hD
  simpa [expTiltedTestFunction, c, R, Real.coe_toNNReal (Real.exp R)
    (Real.exp_nonneg R), mul_assoc, mul_left_comm, mul_comm,
    show c * F.1 E - c * F.1 D = c * (F.1 E - F.1 D) by ring, abs_mul] using h

private theorem continuous_datasetToEuclidean_expEnergy {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation k m) N →
      EuclideanSpace ℝ (DatasetCoordinate k m N)) := by
  change Continuous (fun D : Dataset (Observation k m) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

private theorem continuousAt_datasetNorm_sub_expEnergy {k m N : ℕ}
    (D : Dataset (Observation k m) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation k m) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean_expEnergy.comp (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    exact datasetNorm_eq_euclidean (E - D)
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

private theorem locallyLipschitzDataFunction_continuous_expEnergy {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) : Continuous F.1 := by
  rw [continuous_iff_continuousAt]
  intro D
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨U, hU, K, hK, hLip⟩ := F.2 D
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hzero : datasetNorm (D - D) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
    (continuousAt_datasetNorm_sub_expEnergy D) (ε / (K + 1)) (by positivity)
  let δ := min ρ η
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hdist
  have hEU : E ∈ U := hρU (by
    dsimp [δ] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _))
  have hnorm : datasetNorm (E - D) < ε / (K + 1) := by
    have hdist' := hηbound (by
      dsimp [δ] at hdist
      exact lt_of_lt_of_le hdist (min_le_right _ _))
    have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hdist'
    exact hdist'
  have hbound := hLip E hEU D (mem_of_mem_nhds hU)
  rw [Real.dist_eq]
  change |F.1 E - F.1 D| < ε
  calc
    |F.1 E - F.1 D| ≤ K * datasetNorm (E - D) := hbound
    _ < ε := by
      have hnormNonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      have hKmul : K * datasetNorm (E - D) ≤
          (K + 1) * datasetNorm (E - D) := by nlinarith [hnormNonneg]
      have hkp : 0 < K + 1 := by linarith
      have hlt : (K + 1) * datasetNorm (E - D) <
          (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hnorm hkp
      have heq : (K + 1) * (ε / (K + 1)) = ε := by field_simp
      rw [heq] at hlt
      exact hKmul.trans_lt hlt

private theorem expTiltedTestFunction_weighted_abs_diff_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) (E D : DataCarrier k m n) :
    |(expTiltedTestFunction F lam B hB hBound).1 E -
      (expTiltedTestFunction F lam B hB hBound).1 D| ≤
      (|lam / 2| * Real.exp (max ((lam / 2) * F.1 E) ((lam / 2) * F.1 D))) *
        |F.1 E - F.1 D| := by
  have h := realExp_abs_diff_le_exp_max ((lam / 2) * F.1 E) ((lam / 2) * F.1 D)
  have hmul : |(lam / 2) * F.1 E - (lam / 2) * F.1 D| =
      |lam / 2| * |F.1 E - F.1 D| := by
    rw [show (lam / 2) * F.1 E - (lam / 2) * F.1 D =
      (lam / 2) * (F.1 E - F.1 D) by ring, abs_mul]
  simpa [expTiltedTestFunction, hmul, mul_assoc, mul_left_comm, mul_comm] using h

/-- The local-slope chain rule keeps the exponential evaluated at the current
dataset. This is the weight needed before integrating against the tilted
density. -/
theorem datasetLocalSlope_expTiltedTestFunction_chain_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) (D : DataCarrier k m n) :
    datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ≤
      (|lam / 2| * Real.exp ((lam / 2) * F.1 D)) * datasetLocalSlope F D := by
  let c : ℝ := lam / 2
  let p : DataCarrier k m n → ℝ := fun E =>
    |c| * Real.exp (max (c * F.1 E) (c * F.1 D))
  let q : DataCarrier k m n → ℝ := fun E =>
    |F.1 E - F.1 D| / datasetNorm (E - D)
  have hcontF : Continuous F.1 := locallyLipschitzDataFunction_continuous_expEnergy F
  have hcF : Tendsto (fun E : DataCarrier k m n => c * F.1 E) (𝓝 D)
      (𝓝 (c * F.1 D)) := by
    exact (continuous_const.mul hcontF).continuousAt.tendsto
  have hmax : Tendsto (fun E : DataCarrier k m n =>
      max (c * F.1 E) (c * F.1 D)) (𝓝 D) (𝓝 (c * F.1 D)) := by
    simpa using hcF.max (tendsto_const_nhds :
      Tendsto (fun _ : DataCarrier k m n => c * F.1 D) (𝓝 D) (𝓝 (c * F.1 D)))
  have hp : Tendsto p (𝓝 D)
      (𝓝 (|c| * Real.exp (c * F.1 D))) := by
    dsimp [p]
    exact tendsto_const_nhds.mul
      (Real.continuous_exp.continuousAt.tendsto.comp hmax)
  have hp' : Tendsto p (𝓝[≠] D) (𝓝 (|c| * Real.exp (c * F.1 D))) :=
    hp.mono_left nhdsWithin_le_nhds
  have hpLimsup : limsup p (𝓝[≠] D) = |c| * Real.exp (c * F.1 D) := hp'.limsup_eq
  have hquot : ∀ E, |(expTiltedTestFunction F lam B hB hBound).1 E -
      (expTiltedTestFunction F lam B hB hBound).1 D| / datasetNorm (E - D) ≤
      p E * q E := by
    intro E
    by_cases hED : E = D
    · subst E
      simp [q]
    · have hden : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hED
      have hnum := expTiltedTestFunction_weighted_abs_diff_le F lam B hB hBound E D
      rw [← mul_div_assoc, div_le_div_iff₀ hden hden]
      simpa [p, q, mul_assoc] using
        mul_le_mul_of_nonneg_right hnum hden.le
  have hpNonneg : ∃ᶠ E in 𝓝[≠] D, 0 ≤ p E :=
    Filter.Frequently.of_forall fun E => by
      dsimp [p]
      positivity
  have hpBound := hp'.isBoundedUnder_le
  have hqNonneg : 0 ≤ᶠ[𝓝[≠] D] q :=
    Filter.Eventually.of_forall fun E => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hqBound : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) q := by
    simpa [q] using datasetSlope_bounded F D
  have hprodBound := isBoundedUnder_le_mul_of_nonneg hpNonneg hpBound hqNonneg hqBound
  have hUlower := datasetSlope_cobounded (expTiltedTestFunction F lam B hB hBound) D
  have hlim := limsup_le_limsup (Filter.Eventually.of_forall hquot) hUlower hprodBound
  have hmul := limsup_mul_le hpNonneg hpBound hqNonneg hqBound
  have hpoint : (fun E : DataCarrier k m n => p E * q E) = p * q := by
    funext E
    rfl
  rw [hpoint] at hlim
  rw [hpLimsup] at hmul
  have hfinal : limsup
      (fun E => |(expTiltedTestFunction F lam B hB hBound).1 E -
        (expTiltedTestFunction F lam B hB hBound).1 D| / datasetNorm (E - D))
      (𝓝[≠] D) ≤ (|c| * Real.exp (c * F.1 D)) * limsup q (𝓝[≠] D) := by
    exact hlim.trans hmul
  simp only [datasetLocalSlope]
  simpa [q, c, mul_assoc] using hfinal

/-- A coarse local-slope chain bound. Boundedness of `F` gives a global
exponential Lipschitz constant on its range. -/
theorem datasetLocalSlope_expTiltedTestFunction_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) (D : DataCarrier k m n) :
    datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ≤
      (|lam / 2| * Real.exp (|lam / 2| * B)) * datasetLocalSlope F D := by
  let K : ℝ := |lam / 2| * Real.exp (|lam / 2| * B)
  rw [datasetLocalSlope]
  change limsup
      (fun E => |(expTiltedTestFunction F lam B hB hBound).1 E -
        (expTiltedTestFunction F lam B hB hBound).1 D| / datasetNorm (E - D)) (𝓝[≠] D) ≤
      K * limsup (fun E => |F.1 E - F.1 D| / datasetNorm (E - D)) (𝓝[≠] D)
  have hmul := limsup_mul_le
      (f := 𝓝[≠] D)
      (u := fun _ : DataCarrier k m n => K)
      (v := fun E => |F.1 E - F.1 D| / datasetNorm (E - D))
      (Filter.Frequently.of_forall fun _ => by dsimp [K]; positivity)
      Filter.isBoundedUnder_const
      (Filter.Eventually.of_forall fun E =>
        div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (datasetSlope_bounded F D)
  have hquot : ∀ E, |(expTiltedTestFunction F lam B hB hBound).1 E -
      (expTiltedTestFunction F lam B hB hBound).1 D| / datasetNorm (E - D) ≤
        K * (|F.1 E - F.1 D| / datasetNorm (E - D)) := by
    intro E
    by_cases hED : E = D
    · subst E
      simp [K]
    · have hden : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hED
      have hnum := expTiltedTestFunction_abs_diff_le F lam B hB hBound E D
      dsimp [K]
      rw [← mul_div_assoc]
      rw [div_le_div_iff₀ hden hden]
      nlinarith [mul_le_mul_of_nonneg_right hnum hden.le,
        abs_nonneg (F.1 E - F.1 D)]
  have hprodBound : (𝓝[≠] D).IsBoundedUnder (· ≤ ·)
      (fun E : DataCarrier k m n => K *
        (|F.1 E - F.1 D| / datasetNorm (E - D))) :=
    isBoundedUnder_le_mul_of_nonneg
      (Filter.Frequently.of_forall fun _ => show 0 ≤ K by dsimp [K]; positivity)
      Filter.isBoundedUnder_const
      (Filter.Eventually.of_forall fun E =>
        div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (datasetSlope_bounded F D)
  have hle := limsup_le_limsup (Filter.Eventually.of_forall hquot)
      (datasetSlope_cobounded (expTiltedTestFunction F lam B hB hBound) D)
      hprodBound
  have hmul' : limsup
      (fun E : DataCarrier k m n => K * (|F.1 E - F.1 D| / datasetNorm (E - D)))
      (𝓝[≠] D) ≤ K * limsup
        (fun E => |F.1 E - F.1 D| / datasetNorm (E - D)) (𝓝[≠] D) := by
    have hpoint : (fun E : DataCarrier k m n =>
        K * (|F.1 E - F.1 D| / datasetNorm (E - D))) =
        (fun _ => K) * (fun E => |F.1 E - F.1 D| / datasetNorm (E - D)) := by
      funext E
      rfl
    rw [hpoint]
    simpa only [limsup_const] using hmul
  exact hle.trans hmul'

private theorem linearGrowth_sq_le {a b x : ℝ} :
    (a + b * x) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 * x ^ 2 := by
  nlinarith [sq_nonneg (a - b * x)]

/-- Pointwise quadratic energy bound with the exact exponential tilt. -/
theorem datasetLocalSlope_expTiltedTestFunction_sq_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (D : DataCarrier k m n) :
    datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2 ≤
      (|lam| / 2) ^ 2 * Real.exp (lam * F.1 D) *
        (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D) := by
  let c : ℝ := lam / 2
  let K : ℝ := |c| * Real.exp (c * F.1 D)
  have hslope := datasetLocalSlope_expTiltedTestFunction_chain_le F lam B hB hBound D
  have hsource : datasetLocalSlope F D ≤ a + b * datasetNorm D := hSlope D
  have hnU := datasetLocalSlope_nonneg (expTiltedTestFunction F lam B hB hBound) D
  have hnorm : 0 ≤ datasetNorm D := Real.sqrt_nonneg _
  have hupper : 0 ≤ a + b * datasetNorm D := add_nonneg ha (mul_nonneg hb hnorm)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hupper' : datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ≤
      K * (a + b * datasetNorm D) := by
    dsimp [K, c] at hslope ⊢
    exact hslope.trans (mul_le_mul_of_nonneg_left hsource
      (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)))
  have hsq : datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2 ≤
      (K * (a + b * datasetNorm D)) ^ 2 :=
    (sq_le_sq₀ hnU (mul_nonneg hK hupper)).2 hupper'
  have hhalf : |lam / 2| = |lam| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.exp (c * F.1 D) ^ 2 = Real.exp (lam * F.1 D) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  calc
    datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2 ≤
        (K * (a + b * datasetNorm D)) ^ 2 := hsq
    _ = K ^ 2 * (a + b * datasetNorm D) ^ 2 := by ring
    _ ≤ K ^ 2 * (2 * a ^ 2 + 2 * b ^ 2 * datasetNorm D ^ 2) :=
      mul_le_mul_of_nonneg_left (linearGrowth_sq_le) (sq_nonneg K)
    _ = K ^ 2 * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D) := by
      rw [datasetNorm_sq]
    _ = (|lam| / 2) ^ 2 * Real.exp (lam * F.1 D) *
        (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D) := by
      dsimp [K]
      rw [mul_pow, hhalf, hexp]

/-- The exact exponentially weighted quadratic energy majorant is integrable
under the actual ordered product law from boundedness and the frozen finite
second moment. -/
theorem integrable_expTiltedTestFunction_weighted_energy_majorant {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (_hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) :
    Integrable
      (fun D : DataCarrier k m n =>
        (|lam| / 2) ^ 2 * Real.exp (lam * F.1 D) *
          (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D))
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let ν := Measure.pi fun _ : Fin (n + 1) => μ
  let w : DataCarrier k m n → ℝ := fun D => Real.exp (lam * F.1 D)
  have hcontF : Continuous F.1 := locallyLipschitzDataFunction_continuous_expEnergy F
  have hwmeas : Measurable w := by
    dsimp [w]
    exact (Real.continuous_exp.comp (continuous_const.mul hcontF)).measurable
  have hwbound : ∀ᵐ D ∂ν, ‖w D‖ ≤ Real.exp (|lam| * B) := by
    filter_upwards with D
    have harg : lam * F.1 D ≤ |lam| * B := by
      calc
        lam * F.1 D ≤ |lam * F.1 D| := le_abs_self _
        _ = |lam| * |F.1 D| := abs_mul _ _
        _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hBound D) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr harg
  have hwInt : Integrable w ν :=
    Integrable.of_bound hwmeas.aestronglyMeasurable (Real.exp (|lam| * B)) hwbound
  have hnormSq : Integrable
      (datasetNormSq (k := k + 1) (m := m + 1) (n := n + 1)) ν :=
    integrable_datasetNormSq μ hM2
  have hweightedNormSq : Integrable (fun D : DataCarrier k m n =>
      w D * datasetNormSq D) ν := hnormSq.bdd_mul hwmeas.aestronglyMeasurable hwbound
  have hweightedBase : Integrable (fun D : DataCarrier k m n =>
      w D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) ν := by
    have hfirst : Integrable (fun D : DataCarrier k m n => w D * (2 * a ^ 2)) ν :=
      hwInt.mul_const (2 * a ^ 2)
    have hsecond : Integrable (fun D : DataCarrier k m n =>
        w D * (2 * b ^ 2 * datasetNormSq D)) ν := by
      convert hweightedNormSq.const_mul (2 * b ^ 2) using 1
      ext D
      ring
    have hsplit : (fun D : DataCarrier k m n =>
        w D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) =
        (fun D => w D * (2 * a ^ 2)) +
        (fun D => w D * (2 * b ^ 2 * datasetNormSq D)) := by
      funext D
      simp only [Pi.add_apply]
      rw [mul_add]
    rw [hsplit]
    exact hfirst.add hsecond
  simpa [ν, w, mul_assoc, mul_left_comm, mul_comm] using
    hweightedBase.const_mul ((|lam| / 2) ^ 2)

/-- Conditional admission of the squared local slope. The remaining premise
is only its strong measurability; the pointwise domination and the integrable
majorant are provided above. -/
theorem integrable_expTiltedTestFunction_energy_of_aestronglyMeasurable
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hMeas : AEStronglyMeasurable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  apply Integrable.mono'
    (integrable_expTiltedTestFunction_weighted_energy_majorant μ hM2 F lam B a b hB hBound)
    hMeas
  filter_upwards with D
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact datasetLocalSlope_expTiltedTestFunction_sq_le F lam B a b
    hB hBound ha hb hSlope D

/-- Integrated weighted energy estimate. Its only additional premise is the
measurability bridge isolated in the preceding conditional admission theorem. -/
theorem integral_expTiltedTestFunction_energy_le_weighted_majorant
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hMeas : AEStronglyMeasurable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    (∫ D : DataCarrier k m n,
      datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2
        ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
    ∫ D : DataCarrier k m n,
      (|lam| / 2) ^ 2 * Real.exp (lam * F.1 D) *
        (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)
        ∂Measure.pi fun _ : Fin (n + 1) => μ := by
  let ν := Measure.pi fun _ : Fin (n + 1) => μ
  have hEnergy : Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2) ν :=
    integrable_expTiltedTestFunction_energy_of_aestronglyMeasurable μ hM2 F lam B a b
      hB hBound ha hb hSlope hMeas
  have hMajor : Integrable
      (fun D : DataCarrier k m n =>
        (|lam| / 2) ^ 2 * Real.exp (lam * F.1 D) *
          (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) ν :=
    integrable_expTiltedTestFunction_weighted_energy_majorant μ hM2 F lam B a b hB hBound
  apply integral_mono_ae hEnergy hMajor
  filter_upwards with D
  exact datasetLocalSlope_expTiltedTestFunction_sq_le F lam B a b
    hB hBound ha hb hSlope D

end LOOConcentration
