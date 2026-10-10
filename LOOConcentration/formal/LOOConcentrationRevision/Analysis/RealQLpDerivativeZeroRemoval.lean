import LOOConcentrationRevision.Analysis.RealQLpDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace LOOConcentrationRevision

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exponent differentiation of the absolute real power, including at a zero base. -/
theorem hasDerivAt_abs_rpow_exp {x q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun p : ℝ => |x| ^ p) (|x| ^ q * Real.log |x|) q := by
  by_cases hx : x = 0
  · subst x
    have hlocal : (fun p : ℝ => (0 : ℝ) ^ p) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds hq] with p hp
      simp [Real.zero_rpow hp.ne']
    have hconst := (hasDerivAt_const q (0 : ℝ)).congr_of_eventuallyEq hlocal
    simpa [Real.zero_rpow hq.ne', Real.log_zero] using hconst
  · have hxabs : 0 < |x| := abs_pos.mpr hx
    have hlin : HasDerivAt (fun p : ℝ => Real.log |x| * p) (Real.log |x|) q := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id q).const_mul (Real.log |x|)
    have hexp := hlin.exp
    simpa only [Real.rpow_def_of_pos hxabs, mul_comm] using hexp

private theorem abs_rpow_log_bound {x p q B : ℝ} (hx : 0 ≤ x) (hxB : x ≤ B)
    (hq : 2 ≤ q) (hp : |p - q| < 1) :
    |x ^ p * Real.log x| ≤ 1 + (max B 1) ^ (q + 2) := by
  have hpq := abs_lt.mp hp
  have hpone : 1 < p := by linarith
  have hpexp : p + 1 ≤ q + 2 := by linarith
  have hC1 : 1 ≤ max B 1 := le_max_right _ _
  have hxC : x ≤ max B 1 := le_trans hxB (le_max_left _ _)
  by_cases hx0 : x = 0
  · subst x
    simp only [Real.zero_rpow (ne_of_gt (by linarith : 0 < p)), zero_mul, abs_zero]
    positivity
  by_cases hxone : x ≤ 1
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hpow : x ^ p ≤ x := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge (x := x) (y := p) (z := 1)
          hxpos hxone (by linarith))
    have hpow0 : 0 ≤ x ^ p := Real.rpow_nonneg hx p
    have hlog := Real.abs_log_mul_self_lt x hxpos hxone
    have hmul : x ^ p * |Real.log x| ≤ x * |Real.log x| :=
      mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    have hmul' : x * |Real.log x| = |Real.log x * x| := by
      rw [abs_mul, abs_of_nonneg hx, mul_comm]
    calc
      |x ^ p * Real.log x| = x ^ p * |Real.log x| := by
        rw [abs_mul, abs_of_nonneg hpow0]
      _ ≤ x * |Real.log x| := hmul
      _ ≤ 1 := by rw [hmul']; exact le_of_lt hlog
      _ ≤ 1 + (max B 1) ^ (q + 2) := by
        have hpowC := Real.rpow_nonneg (show 0 ≤ max B 1 by linarith) (q + 2)
        linarith
  · have hxlarge : 1 ≤ x := le_of_not_ge hxone
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxlarge
    have hlog0 : 0 ≤ Real.log x := (Real.log_nonneg_iff hxpos).2 hxlarge
    have hlogx : Real.log x ≤ x := Real.log_le_self hx
    have hpow0 : 0 ≤ x ^ p := Real.rpow_nonneg hx p
    have hprod0 : 0 ≤ x ^ p * Real.log x := mul_nonneg hpow0 hlog0
    rw [abs_of_nonneg hprod0]
    calc
      x ^ p * Real.log x ≤ x ^ p * x := mul_le_mul_of_nonneg_left hlogx hpow0
      _ = x ^ (p + 1) := by rw [Real.rpow_add hxpos]; simp
      _ ≤ (max B 1) ^ (p + 1) := Real.rpow_le_rpow hx hxC (by linarith)
      _ ≤ (max B 1) ^ (q + 2) := Real.rpow_le_rpow_of_exponent_le hC1 hpexp
      _ ≤ 1 + (max B 1) ^ (q + 2) := by
        have hpowC := Real.rpow_nonneg (show 0 ≤ max B 1 by linarith) (q + 2)
        linarith

private theorem rpow_bound {x q B : ℝ} (hx : 0 ≤ x) (hxB : x ≤ B) (hq : 2 ≤ q) :
    x ^ q ≤ 1 + (max B 1) ^ (q + 2) := by
  have hC1 : 1 ≤ max B 1 := le_max_right _ _
  have hxC : x ≤ max B 1 := le_trans hxB (le_max_left _ _)
  by_cases hx0 : x = 0
  · subst x
    simp only [Real.zero_rpow (by linarith : q ≠ 0)]
    have hpowC := Real.rpow_nonneg (show 0 ≤ max B 1 by linarith) (q + 2)
    linarith
  by_cases hxone : x ≤ 1
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hpow : x ^ q ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := x) (y := q) (z := 0)
        hxpos hxone (by linarith)
      simpa only [Real.rpow_zero] using h
    have hpowC := Real.rpow_nonneg (show 0 ≤ max B 1 by linarith) (q + 2)
    linarith
  · have hxlarge : 1 ≤ x := le_of_not_ge hxone
    have hpow : x ^ q ≤ (max B 1) ^ q := Real.rpow_le_rpow hx hxC (by linarith)
    have hpow' : (max B 1) ^ q ≤ (max B 1) ^ (q + 2) :=
      Real.rpow_le_rpow_of_exponent_le hC1 (by linarith)
    have hpowC := Real.rpow_nonneg (show 0 ≤ max B 1 by linarith) (q + 2)
    linarith

/-- Differentiation of the bounded absolute-power moment; domination is proved locally
from the pointwise logarithmic bound, including the zero-base case. -/
theorem hasDerivAt_bounded_abs_moment
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {B q : ℝ}
    (hmeas : Measurable g) (_hB : 0 ≤ B) (hbound : ∀ ω, |g ω| ≤ B) (hq : 2 ≤ q) :
    HasRealDerivAt (fun p : ℝ => ∫ ω, |g ω| ^ p ∂μ)
      (∫ ω, |g ω| ^ q * Real.log |g ω| ∂μ) q := by
  let K : ℝ := 1 + (max B 1) ^ (q + 2)
  let s : Set ℝ := Metric.ball q 1
  have hqnonneg : 0 ≤ q := by linarith [hq]
  have hAbs : Measurable (fun ω => |g ω|) := by fun_prop
  have hKint : Integrable (fun _ : Ω => K) μ := by exact integrable_const K
  have hpowerInt : Integrable (fun ω => |g ω| ^ q) μ := by
    apply Integrable.of_bound (C := K) ?_ ?_
    · have hpowc : Continuous (fun x : ℝ => x ^ q) := Real.continuous_rpow_const hqnonneg
      exact (hpowc.measurable.comp hAbs).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (g ω)) q)]
      exact rpow_bound (abs_nonneg _) (hbound ω) hq
  have hFmeas : ∀ᶠ p in 𝓝 q, AEStronglyMeasurable (fun ω => |g ω| ^ p) μ := by
    filter_upwards [eventually_gt_nhds (by linarith [hq] : 0 < q)] with p hp
    have hpcont : Continuous (fun x : ℝ => x ^ p) := Real.continuous_rpow_const hp.le
    exact (hpcont.measurable.comp hAbs).aestronglyMeasurable
  have hF'derivmeas : AEStronglyMeasurable
      (fun ω => |g ω| ^ q * Real.log |g ω|) μ := by
    have hpowc : Continuous (fun x : ℝ => x ^ q) := Real.continuous_rpow_const hqnonneg
    have hmPow := hpowc.measurable.comp hAbs
    have hmLog := Real.measurable_log.comp hAbs
    exact (hmPow.mul hmLog).aestronglyMeasurable
  have hs : s ∈ 𝓝 q := by dsimp [s]; exact Metric.ball_mem_nhds q zero_lt_one
  have hboundDeriv : ∀ᵐ ω ∂μ, ∀ p ∈ s,
      ‖|g ω| ^ p * Real.log |g ω|‖ ≤ K := by
    apply ae_of_all
    intro ω p hp
    have hp' : |p - q| < 1 := by simpa [s, Metric.mem_ball, Real.dist_eq] using hp
    have h := abs_rpow_log_bound (abs_nonneg _) (hbound ω) hq hp'
    simpa [Real.norm_eq_abs, K] using h
  have hdiff : ∀ᵐ ω ∂μ, ∀ p ∈ s,
      HasDerivAt (fun r : ℝ => |g ω| ^ r) (|g ω| ^ p * Real.log |g ω|) p := by
    apply ae_of_all
    intro ω p hp
    have hp' : |p - q| < 1 := by simpa [s, Metric.mem_ball, Real.dist_eq] using hp
    have hp0 : 0 < p := by have := abs_lt.mp hp'; linarith [hq]
    exact hasDerivAt_abs_rpow_exp hp0
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := q) (s := s) (F := fun p ω => |g ω| ^ p)
    hs hFmeas hpowerInt hF'derivmeas hboundDeriv hKint hdiff
  exact hmain.2

/-- The exact real-q squared-norm derivative, including the zero-moment case.
The entropy is kept in its literal unnormalized integral form. -/
theorem bounded_abs_realQLp_normSq_hasDerivAt
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {B q : ℝ}
    (hmeas : Measurable g) (_hB : 0 ≤ B) (hbound : ∀ ω, |g ω| ≤ B) (hq : 2 ≤ q) :
    HasRealDerivAt (fun p : ℝ => (∫ ω, |g ω| ^ p ∂μ) ^ (2 / p))
      ((2 / q ^ 2) * (∫ ω, |g ω| ^ q ∂μ) ^ (2 / q - 1) *
        ((∫ ω, |g ω| ^ q * Real.log (|g ω| ^ q) ∂μ) -
          (∫ ω, |g ω| ^ q ∂μ) * Real.log (∫ ω, |g ω| ^ q ∂μ))) q := by
  let M : ℝ → ℝ := fun p => ∫ ω, |g ω| ^ p ∂μ
  have hMder : HasRealDerivAt (fun p : ℝ => M p)
      (∫ ω, |g ω| ^ q * Real.log |g ω| ∂μ) q :=
    hasDerivAt_bounded_abs_moment (μ := μ) (g := g) (B := B) (q := q)
      hmeas _hB hbound hq
  have hqpos : 0 < q := by linarith [hq]
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hExp : HasRealDerivAt (fun p : ℝ => 2 / p) (-2 / q ^ 2) q := by
    have h := (hasDerivAt_const q (2 : ℝ)).mul (hasDerivAt_inv hqne)
    convert h using 1
    · funext p
      simp [div_eq_mul_inv]
    · ring
  by_cases hApos : 0 < M q
  · have hpow := hMder.rpow hExp hApos
    have hactual :
        (∫ ω, |g ω| ^ q * Real.log (|g ω| ^ q) ∂μ) =
          q * (∫ ω, |g ω| ^ q * Real.log |g ω| ∂μ) := by
      calc
        _ = ∫ ω, q * (|g ω| ^ q * Real.log |g ω|) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          by_cases hx : |g ω| = 0
          · simp [hx, Real.zero_rpow hqne]
          · have hxpos : 0 < |g ω| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hx)
            rw [Real.log_rpow hxpos q]
            ring
        _ = q * (∫ ω, |g ω| ^ q * Real.log |g ω| ∂μ) := integral_const_mul q _
    have hA : M q = ∫ ω, |g ω| ^ q ∂μ := rfl
    have hpowA : M q ^ (2 / q) = M q ^ (2 / q - 1) * M q := by
      calc
        M q ^ (2 / q) = M q ^ ((2 / q - 1) + 1) := by congr 1; ring
        _ = M q ^ (2 / q - 1) * M q ^ (1 : ℝ) := Real.rpow_add hApos _ _
        _ = M q ^ (2 / q - 1) * M q := by rw [Real.rpow_one]
    have hpow' : HasRealDerivAt (fun p : ℝ => M p ^ (2 / p))
        ((∫ ω, |g ω| ^ q * Real.log |g ω| ∂μ) * (2 / q) * M q ^ (2 / q - 1) +
          (-2 / q ^ 2) * M q ^ (2 / q) * Real.log (M q)) q := hpow
    convert hpow' using 1
    rw [hactual, ← hA, hpowA]
    field_simp [hqne]
    ring
  · have hA0 : M q = 0 := le_antisymm (le_of_not_gt hApos) (by
      have hnonneg : 0 ≤ M q := by
        dsimp [M]
        exact integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg (g ω)) q)
      exact hnonneg)
    have hqnonneg : 0 ≤ q := le_of_lt hqpos
    have hAbs : Measurable (fun ω => |g ω|) := by fun_prop
    have hpowInt : Integrable (fun ω => |g ω| ^ q) μ := by
      apply Integrable.of_bound (C := 1 + (max B 1) ^ (q + 2)) ?_ ?_
      · have hpowc : Continuous (fun x : ℝ => x ^ q) := Real.continuous_rpow_const hqnonneg
        exact (hpowc.measurable.comp hAbs).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (g ω)) q)]
        exact rpow_bound (abs_nonneg _) (hbound ω) hq
    have hgpower_nn : 0 ≤ᵐ[μ] fun ω => |g ω| ^ q := by
      filter_upwards with ω
      exact Real.rpow_nonneg (abs_nonneg (g ω)) q
    have hGpower0 : ∀ᵐ ω ∂μ, |g ω| ^ q = 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae hgpower_nn hpowInt).1
      simpa [M] using hA0
    have hGzero : ∀ᵐ ω ∂μ, |g ω| = 0 := by
      filter_upwards [hGpower0] with ω hω
      by_contra hx
      have hxpos : 0 < |g ω| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hx)
      exact (ne_of_gt (Real.rpow_pos_of_pos hxpos q)) hω
    have hEnt0 :
        (∫ ω, |g ω| ^ q * Real.log (|g ω| ^ q) ∂μ) -
          (∫ ω, |g ω| ^ q ∂μ) * Real.log (∫ ω, |g ω| ^ q ∂μ) = 0 := by
      have hInt0 : (∫ ω, |g ω| ^ q ∂μ) = 0 := by simpa [M] using hA0
      have hEntInt0 : (∫ ω, |g ω| ^ q * Real.log (|g ω| ^ q) ∂μ) = 0 := by
        calc
          _ = ∫ _ : Ω, (0 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hGzero] with ω hω
            simp [hω, Real.zero_rpow hqne, Real.log_zero]
          _ = 0 := by simp
      simp [hInt0, hEntInt0]
    have hMzero : ∀ᶠ p in 𝓝 q, M p = 0 := by
      filter_upwards [eventually_gt_nhds hqpos] with p hp
      calc
        M p = ∫ _ : Ω, (0 : ℝ) ∂μ := by
          dsimp [M]
          apply integral_congr_ae
          filter_upwards [hGzero] with ω hω
          simp [hω, Real.zero_rpow hp.ne']
        _ = 0 := by simp
    have hpowzero : (fun p : ℝ => M p ^ (2 / p)) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hMzero, eventually_gt_nhds hqpos] with p hMp hp
      rw [hMp]
      exact Real.zero_rpow (ne_of_gt (by positivity))
    have hzeroDer : HasRealDerivAt (fun p : ℝ => M p ^ (2 / p)) 0 q := by
      simpa [HasRealDerivAt, LOOConcentration.instAddCommGroupReal_lOOConcentration,
        LOOConcentration.instModuleReal_lOOConcentration] using
          (hasDerivAt_const q (0 : ℝ)).congr_of_eventuallyEq hpowzero
    simpa [M, hEnt0] using hzeroDer

/-- Actual application to the earlier bounded regularization `sqrt (g^2 + ε)`;
the unregularized theorem above is also valid when the source function vanishes. -/
theorem regularized_abs_realQLp_normSq_consumer
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {B ε q : ℝ}
    (hmeas : Measurable g) (hB : 0 ≤ B) (hbound : ∀ ω, |g ω| ≤ B)
    (hε : 0 < ε) (hq : 2 ≤ q) :
    let gε : Ω → ℝ := fun ω => Real.sqrt (g ω ^ 2 + ε)
    HasRealDerivAt (fun p : ℝ => (∫ ω, |gε ω| ^ p ∂μ) ^ (2 / p))
      ((2 / q ^ 2) * (∫ ω, |gε ω| ^ q ∂μ) ^ (2 / q - 1) *
        ((∫ ω, |gε ω| ^ q * Real.log (|gε ω| ^ q) ∂μ) -
          (∫ ω, |gε ω| ^ q ∂μ) * Real.log (∫ ω, |gε ω| ^ q ∂μ))) q := by
  dsimp
  let gε : Ω → ℝ := fun ω => Real.sqrt (g ω ^ 2 + ε)
  have hgεmeas : Measurable gε := by dsimp [gε]; fun_prop
  have hBε : 0 ≤ Real.sqrt (B ^ 2 + ε) := Real.sqrt_nonneg _
  have hgεbound : ∀ ω, |gε ω| ≤ Real.sqrt (B ^ 2 + ε) := by
    intro ω
    have hrad : 0 < g ω ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
    rw [abs_of_nonneg (le_of_lt (Real.sqrt_pos.2 hrad))]
    apply Real.sqrt_le_sqrt
    have hsquare : g ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (g ω)) hB).2 (hbound ω)
    nlinarith
  exact bounded_abs_realQLp_normSq_hasDerivAt hgεmeas hBε hgεbound hq

end

end LOOConcentrationRevision
