import LOOConcentration.Concentration.SegmentEstimate
import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FunProp

/-!
# Regularized power tests for moment interpolation

The scalar regularization is smooth because its base is strictly positive.
This file proves its locally Lipschitz composition and the exact frozen
local-slope chain bound. The energy-integrability step is recorded in the
wave report.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

private noncomputable def regularizedPowerScalar (q ε x : ℝ) : ℝ :=
  (((id ^ 2) x) + ε) ^ (q / 4)

private theorem regularizedPowerScalar_contDiff (q ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ⊤ (regularizedPowerScalar q ε) := by
  unfold regularizedPowerScalar
  have hbase : ContDiff ℝ ⊤ (fun x : ℝ => ((id ^ 2) x) + ε) := by
    simpa [Pi.pow_apply] using (contDiff_id.pow 2).add contDiff_const
  exact hbase.rpow_const_of_ne (fun x =>
    ne_of_gt (by simpa [id] using (show 0 < x ^ 2 + ε by positivity)))

private theorem hasDerivAt_regularizedPowerScalar (q ε x : ℝ) (hε : 0 < ε) :
    HasDerivAt (regularizedPowerScalar q ε)
      (q / 2 * x * (x ^ 2 + ε) ^ (q / 4 - 1)) x := by
  have hsquare : HasDerivAt (id ^ 2) (2 * x) x := by
    simpa [id] using (hasDerivAt_id x).pow 2
  have hbase : HasDerivAt (fun y : ℝ => (id ^ 2) y + ε) (2 * x) x :=
    hsquare.add_const ε
  have hpos : 0 < (id ^ 2) x + ε := by
    simpa [id] using (show 0 < x ^ 2 + ε by positivity)
  have h := hbase.rpow_const (p := q / 4) (Or.inl hpos.ne')
  change HasDerivAt (fun y : ℝ => ((id ^ 2) y + ε) ^ (q / 4))
    (q / 2 * x * ((id ^ 2) x + ε) ^ (q / 4 - 1)) x
  rw [show q / 2 * x * ((id ^ 2) x + ε) ^ (q / 4 - 1) =
    2 * x * (q / 4) * ((id ^ 2) x + ε) ^ (q / 4 - 1) by ring]
  exact h

private theorem regularizedPowerScalar_lipschitzOn_Icc (q ε B : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      LipschitzOnWith (Real.toNNReal K) (regularizedPowerScalar q ε)
        (Set.Icc (-B) B) := by
  let f := regularizedPowerScalar q ε
  have hf : ContDiff ℝ ⊤ f := by
    simpa [f] using regularizedPowerScalar_contDiff q ε hε
  have hderiv : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hnorm : Continuous fun x : ℝ => ‖deriv f x‖ := continuous_norm.comp hderiv
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-B) B) hnorm.continuousOn
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hderivBound : ∀ x ∈ Set.Icc (-B) B, ‖deriv f x‖ ≤ K := by
    intro x hx
    have hCx : ‖deriv f x‖ ≤ C := by
      simpa only [norm_norm] using hC x hx
    exact hCx.trans (le_max_left C 0)
  refine ⟨K, hK, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal K hK]
    exact hderivBound x hx
  · exact convex_Icc (-B) B

private theorem regularizedPowerScalar_abs_diff_le (q ε B K : ℝ)
    (hK : 0 ≤ K)
    (hLip : LipschitzOnWith (Real.toNNReal K) (regularizedPowerScalar q ε)
      (Set.Icc (-B) B))
    {x y : ℝ} (hx : x ∈ Set.Icc (-B) B) (hy : y ∈ Set.Icc (-B) B) :
    |regularizedPowerScalar q ε x - regularizedPowerScalar q ε y| ≤ K * |x - y| := by
  have h := hLip.dist_le_mul x hx y hy
  simpa only [Real.dist_eq, Real.norm_eq_abs, Real.coe_toNNReal K hK] using h

noncomputable def regularizedPowerTestFunction {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) (q ε B : ℝ)
    (_hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B) (hε : 0 < ε) :
    LocallyLipschitzDataFunction k m n := by
  classical
  let hExists := regularizedPowerScalar_lipschitzOn_Icc q ε B hε
  let K := Classical.choose hExists
  have hK := (Classical.choose_spec hExists).1
  have hLip := (Classical.choose_spec hExists).2
  refine ⟨fun D => regularizedPowerScalar q ε (g.1 D), ?_⟩
  intro D
  obtain ⟨U, hU, C, hC, hlocal⟩ := g.2 D
  refine ⟨U, hU, K * C, mul_nonneg hK hC, ?_⟩
  intro E hEU F hFU
  have hE : g.1 E ∈ Set.Icc (-B) B := by
    rw [Set.mem_Icc, ← abs_le]
    exact hBound E
  have hF : g.1 F ∈ Set.Icc (-B) B := by
    rw [Set.mem_Icc, ← abs_le]
    exact hBound F
  have hscalar := regularizedPowerScalar_abs_diff_le q ε B K hK hLip hE hF
  have hbase := hlocal E hEU F hFU
  calc
    |regularizedPowerScalar q ε (g.1 E) -
        regularizedPowerScalar q ε (g.1 F)| ≤ K * |g.1 E - g.1 F| := hscalar
    _ ≤ K * (C * datasetNorm (E - F)) :=
      mul_le_mul_of_nonneg_left hbase hK
    _ = (K * C) * datasetNorm (E - F) := by ring

/-- Pointwise formula for the owned regularized power test. -/
@[simp] theorem regularizedPowerTestFunction_apply {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) (q ε B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B) (hε : 0 < ε)
    (D : DataCarrier k m n) :
    (regularizedPowerTestFunction g q ε B hB hBound hε).1 D =
      (g.1 D ^ 2 + ε) ^ (q / 4) := by
  simp [regularizedPowerTestFunction, regularizedPowerScalar, Pi.pow_apply, id]

private theorem continuous_datasetToEuclidean_powerEnergy {k m N : ℕ} :
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

private theorem continuousAt_datasetNorm_sub_powerEnergy {k m N : ℕ}
    (D : Dataset (Observation k m) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation k m) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean_powerEnergy.comp (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    exact datasetNorm_eq_euclidean _
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

private theorem locallyLipschitzDataFunction_continuous_powerEnergy {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) : Continuous g.1 := by
  rw [continuous_iff_continuousAt]
  intro D
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨U, hU, C, hC, hlocal⟩ := g.2 D
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hzero : datasetNorm (D - D) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
    (continuousAt_datasetNorm_sub_powerEnergy D) (ε / (C + 1)) (by positivity)
  let δ := min ρ η
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hdist
  have hEU : E ∈ U := hρU (by
    dsimp [δ] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _))
  have hnorm : datasetNorm (E - D) < ε / (C + 1) := by
    have hdist' := hηbound (by
      dsimp [δ] at hdist
      exact lt_of_lt_of_le hdist (min_le_right _ _))
    have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hdist'
    exact hdist'
  have hbound := hlocal E hEU D (mem_of_mem_nhds hU)
  rw [Real.dist_eq]
  change |g.1 E - g.1 D| < ε
  calc
    |g.1 E - g.1 D| ≤ C * datasetNorm (E - D) := hbound
    _ < ε := by
      have hnormNonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      have hCmul : C * datasetNorm (E - D) ≤
          (C + 1) * datasetNorm (E - D) := by nlinarith [hnormNonneg]
      have hCp : 0 < C + 1 := by linarith
      have hlt : (C + 1) * datasetNorm (E - D) <
          (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hnorm hCp
      have heq : (C + 1) * (ε / (C + 1)) = ε := by field_simp
      rw [heq] at hlt
      exact hCmul.trans_lt hlt

private theorem datasetLocalSlope_scalarComp_le {k m n : ℕ}
    (g u : LocallyLipschitzDataFunction k m n) (f : ℝ → ℝ) (f' : ℝ)
    (D : DataCarrier k m n)
    (hf : HasDerivAt f f' (g.1 D))
    (hu : ∀ E, u.1 E = f (g.1 E)) :
    datasetLocalSlope u D ≤ |f'| * datasetLocalSlope g D := by
  let secant : ℝ → ℝ := Function.update
    (fun y => (f y - f (g.1 D)) / (y - g.1 D)) (g.1 D) f'
  let p : DataCarrier k m n → ℝ := fun E => |secant (g.1 E)|
  let q : DataCarrier k m n → ℝ := fun E =>
    |g.1 E - g.1 D| / datasetNorm (E - D)
  have hsec : ContinuousAt secant (g.1 D) := by
    dsimp [secant]
    exact hf.continuousAt_div
  have hcontg : Continuous g.1 := locallyLipschitzDataFunction_continuous_powerEnergy g
  have hsecValue : secant (g.1 D) = f' := by simp [secant]
  have hsecComp : Tendsto (fun E => secant (g.1 E)) (𝓝 D) (𝓝 (secant (g.1 D))) :=
    hsec.tendsto.comp hcontg.continuousAt.tendsto
  have habsComp : Tendsto (abs ∘ (fun E => secant (g.1 E)))
      (𝓝 D) (𝓝 |f'|) := by
    simpa [hsecValue] using continuous_abs.continuousAt.tendsto.comp hsecComp
  have hp : Tendsto p (𝓝 D) (𝓝 |f'|) := by
    exact habsComp
  have hp' : Tendsto p (𝓝[≠] D) (𝓝 |f'|) :=
    hp.mono_left nhdsWithin_le_nhds
  have hpLimsup : limsup p (𝓝[≠] D) = |f'| := hp'.limsup_eq
  have hquot : ∀ E,
      |u.1 E - u.1 D| / datasetNorm (E - D) = p E * q E := by
    intro E
    rw [hu E, hu D]
    by_cases hED : E = D
    · subst E
      simp [p, q]
    · by_cases hvalue : g.1 E = g.1 D
      · simp [p, q, hvalue]
      · have hden : datasetNorm (E - D) ≠ 0 :=
          (datasetNorm_sub_pos hED).ne'
        have hsecval : secant (g.1 E) =
            (f (g.1 E) - f (g.1 D)) / (g.1 E - g.1 D) := by
          simp [secant, hvalue]
        have hfactor : f (g.1 E) - f (g.1 D) =
            (g.1 E - g.1 D) * secant (g.1 E) := by
          rw [hsecval]
          field_simp
        rw [hfactor, abs_mul]
        simp only [p, q]
        field_simp [hden]
  have hpNonneg : ∃ᶠ E in 𝓝[≠] D, 0 ≤ p E :=
    Filter.Frequently.of_forall fun E => by simp [p]
  have hpBound := hp'.isBoundedUnder_le
  have hqNonneg : 0 ≤ᶠ[𝓝[≠] D] q :=
    Filter.Eventually.of_forall fun E =>
      div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hqBound : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) q := by
    simpa [q] using datasetSlope_bounded g D
  have hprodBound :=
    isBoundedUnder_le_mul_of_nonneg hpNonneg hpBound hqNonneg hqBound
  have huLower := datasetSlope_cobounded u D
  have hlim := limsup_le_limsup
    (Filter.Eventually.of_forall fun E => (hquot E).le) huLower hprodBound
  have hmul := limsup_mul_le hpNonneg hpBound hqNonneg hqBound
  calc
    datasetLocalSlope u D =
        limsup (fun E => |u.1 E - u.1 D| / datasetNorm (E - D)) (𝓝[≠] D) := rfl
    _ ≤ limsup (fun E => p E * q E) (𝓝[≠] D) := hlim
    _ ≤ limsup p (𝓝[≠] D) * limsup q (𝓝[≠] D) := hmul
    _ = |f'| * datasetLocalSlope g D := by
      rw [hpLimsup]
      rfl

/-- The regularized power test has the exact scalar derivative factor in its
frozen local-slope chain bound. The regularization keeps the derivative
well-defined when `g D = 0`, including at `q = 2`. -/
theorem datasetLocalSlope_regularizedPowerTestFunction_le {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) (q ε B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B) (hε : 0 < ε)
    (hq : 2 ≤ q) (D : DataCarrier k m n) :
    datasetLocalSlope (regularizedPowerTestFunction g q ε B hB hBound hε) D ≤
      (q / 2 * |g.1 D| * (g.1 D ^ 2 + ε) ^ (q / 4 - 1)) *
        datasetLocalSlope g D := by
  let f : ℝ → ℝ := regularizedPowerScalar q ε
  let u := regularizedPowerTestFunction g q ε B hB hBound hε
  have hu : ∀ E, u.1 E = f (g.1 E) := by
    intro E
    simp [u, f, regularizedPowerTestFunction]
  have hderiv := hasDerivAt_regularizedPowerScalar q ε (g.1 D) hε
  have hchain := datasetLocalSlope_scalarComp_le g u f
    (q / 2 * g.1 D * (g.1 D ^ 2 + ε) ^ (q / 4 - 1)) D hderiv hu
  have hqnonneg : 0 ≤ q / 2 := by linarith
  have hpow : 0 ≤ (g.1 D ^ 2 + ε) ^ (q / 4 - 1) :=
    Real.rpow_nonneg (by positivity) _
  have habs :
      |q / 2 * g.1 D * (g.1 D ^ 2 + ε) ^ (q / 4 - 1)| =
        q / 2 * |g.1 D| * (g.1 D ^ 2 + ε) ^ (q / 4 - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hqnonneg, abs_of_nonneg hpow]
  simpa [u, f, regularizedPowerTestFunction, regularizedPowerScalar, habs] using hchain

/-- At a zero of `g`, the regularized scalar derivative vanishes. This holds
for every `q ≥ 2`, in particular at the endpoint `q = 2`. -/
theorem deriv_regularizedPowerScalar_at_zero (q ε : ℝ) (hε : 0 < ε) :
    deriv (regularizedPowerScalar q ε) 0 = 0 := by
  rw [(hasDerivAt_regularizedPowerScalar q ε 0 hε).deriv]
  simp

/-- At a dataset where `g` vanishes, the regularized power test has zero
frozen local slope. This includes `q = 2`; positive `ε` removes the singular
unregularized derivative at zero. -/
theorem datasetLocalSlope_regularizedPowerTestFunction_eq_zero_of {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) (q ε B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B) (hε : 0 < ε)
    (hq : 2 ≤ q) (D : DataCarrier k m n) (hzero : g.1 D = 0) :
    datasetLocalSlope (regularizedPowerTestFunction g q ε B hB hBound hε) D = 0 := by
  have hupper := datasetLocalSlope_regularizedPowerTestFunction_le
    g q ε B hB hBound hε hq D
  have hnonneg := datasetLocalSlope_nonneg
    (regularizedPowerTestFunction g q ε B hB hBound hε) D
  rw [hzero] at hupper
  simp at hupper
  linarith

/-- The endpoint `q = 2` is admitted by the same exact chain rule, with no
division by `q - 2` or exclusion of zero values. -/
theorem datasetLocalSlope_regularizedPowerTestFunction_two_le {k m n : ℕ}
    (g : LocallyLipschitzDataFunction k m n) (ε B : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B) (hε : 0 < ε)
    (D : DataCarrier k m n) :
    datasetLocalSlope (regularizedPowerTestFunction g (2 : ℝ) ε B hB hBound hε) D ≤
      ((2 : ℝ) / 2 * |g.1 D| * (g.1 D ^ 2 + ε) ^ ((2 : ℝ) / 4 - 1)) *
        datasetLocalSlope g D := by
  exact datasetLocalSlope_regularizedPowerTestFunction_le
    g (2 : ℝ) ε B hB hBound hε (by norm_num) D

#print axioms datasetLocalSlope_regularizedPowerTestFunction_le
#print axioms datasetLocalSlope_regularizedPowerTestFunction_eq_zero_of
#print axioms datasetLocalSlope_regularizedPowerTestFunction_two_le

end LOOConcentration
