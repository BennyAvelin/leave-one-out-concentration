import LOOConcentration.FunctionalInequalities.EntropyCoordinateTransport
import LOOConcentrationRevision.FunctionalInequalities.FiniteEntropyTensorization
import LOOConcentrationRevision.FunctionalInequalities.SquareEntropy
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite entropy tensorization for nonnegative finite-entropy functions

Truncation with a vanishing positive offset lets the bounded-positive
coefficient-one tensorization pass to nonnegative functions with finite literal
entropy. The raw function and its `x * log x` density supply every section
integrability condition through Fubini.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration.Revision

open LOOConcentration

private noncomputable def entropyDensity (x : ℝ) : ℝ := x * Real.log x

private noncomputable def entropyApproximationEpsilon (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private noncomputable def entropyApproximation (n : ℕ) (x : ℝ) : ℝ :=
  min (x + entropyApproximationEpsilon n) ((n : ℝ) + 1)

private theorem entropyApproximationEpsilon_pos (n : ℕ) :
    0 < entropyApproximationEpsilon n := by
  dsimp [entropyApproximationEpsilon]
  positivity

private theorem entropyApproximationEpsilon_le_one (n : ℕ) :
    entropyApproximationEpsilon n ≤ 1 := by
  dsimp [entropyApproximationEpsilon]
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 (by linarith)

private theorem entropyApproximationEpsilon_tendsto_zero :
    Tendsto entropyApproximationEpsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private theorem entropyApproximation_bounds {x : ℝ} (n : ℕ) (hx : 0 ≤ x) :
    0 ≤ entropyApproximation n x ∧
      entropyApproximationEpsilon n ≤ entropyApproximation n x ∧
      entropyApproximation n x ≤ x + 1 := by
  have hε := entropyApproximationEpsilon_pos n
  have hε1 := entropyApproximationEpsilon_le_one n
  have hcap : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  dsimp [entropyApproximation]
  refine ⟨le_min (by positivity) (by linarith) , le_min (by linarith) (by linarith), ?_⟩
  exact (min_le_left _ _).trans (by linarith)

private theorem entropyApproximation_tendsto (x : ℝ) :
    Tendsto (fun n => entropyApproximation n x) atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have heq : (fun n => entropyApproximation n x) =ᶠ[atTop]
      fun n => x + entropyApproximationEpsilon n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNx : x < (N : ℝ) := by exact_mod_cast hN
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcap : x + entropyApproximationEpsilon n ≤ (n : ℝ) + 1 := by
      have hε := entropyApproximationEpsilon_le_one n
      linarith
    simp [entropyApproximation, min_eq_left hcap]
  have hlim : Tendsto (fun n => x + entropyApproximationEpsilon n) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds.add entropyApproximationEpsilon_tendsto_zero)
  exact hlim.congr' heq.symm

private theorem exists_mul_log_norm_bound_finite (B : ℝ) (_hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc (0 : ℝ) B, ‖x * Real.log x‖ ≤ C := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B) := isCompact_Icc
  have hcontinuous : Continuous (fun x : ℝ => ‖x * Real.log x‖) :=
    continuous_norm.comp Real.continuous_mul_log
  obtain ⟨C, hC0, hC⟩ :=
    hcompact.bddAbove_image hcontinuous.continuousOn |>.exists_ge 0
  refine ⟨C, hC0, ?_⟩
  intro x hx
  exact hC _ ⟨x, hx, rfl⟩

private theorem exists_mul_log_norm_bound_two :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖x * Real.log x‖ ≤ C :=
  exists_mul_log_norm_bound_finite 2 (by norm_num)

private noncomputable def entropyApproximationDensityConstant : ℝ :=
  Classical.choose exists_mul_log_norm_bound_two

private theorem entropyApproximationDensityConstant_spec :
    0 ≤ entropyApproximationDensityConstant ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 2,
        ‖x * Real.log x‖ ≤ entropyApproximationDensityConstant := by
  exact Classical.choose_spec exists_mul_log_norm_bound_two

private theorem entropyApproximation_density_bound
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖entropyApproximation n x * Real.log (entropyApproximation n x)‖ ≤
      entropyApproximationDensityConstant +
        2 * ‖x * Real.log x‖ + (2 * Real.log 2) * x := by
  have hC0 := entropyApproximationDensityConstant_spec.1
  have hC := entropyApproximationDensityConstant_spec.2
  have hε := entropyApproximationEpsilon_pos n
  have hε1 := entropyApproximationEpsilon_le_one n
  have hcap : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  let y := entropyApproximation n x
  have hy0 : 0 ≤ y := (entropyApproximation_bounds n hx).1
  have hycap : y ≤ x + entropyApproximationEpsilon n := min_le_left _ _
  have hyN : y ≤ (n : ℝ) + 1 := min_le_right _ _
  by_cases hx1 : x ≤ 1
  · have hy2 : y ≤ 2 := by
      dsimp [y]
      calc
        min (x + entropyApproximationEpsilon n) ((n : ℝ) + 1) ≤
            x + entropyApproximationEpsilon n := min_le_left _ _
        _ ≤ 2 := by linarith
    change ‖y * Real.log y‖ ≤
      entropyApproximationDensityConstant + 2 * ‖x * Real.log x‖ +
        (2 * Real.log 2) * x
    calc
      ‖y * Real.log y‖ ≤ entropyApproximationDensityConstant := hC y ⟨hy0, hy2⟩
      _ ≤ entropyApproximationDensityConstant + 2 * ‖x * Real.log x‖ +
          (2 * Real.log 2) * x := by
        have hn : 0 ≤ 2 * ‖x * Real.log x‖ := by positivity
        have hxterm : 0 ≤ (2 * Real.log 2) * x :=
          mul_nonneg (by positivity) hx
        linarith
  · have hxgt : 1 ≤ x := le_of_not_ge hx1
    have hy1 : 1 ≤ y := le_min (by linarith) hcap
    have hy_le_two_x : y ≤ 2 * x := by
      calc
        y ≤ x + entropyApproximationEpsilon n := hycap
        _ ≤ x + 1 := by linarith
        _ ≤ 2 * x := by linarith
    have hexp : Real.exp (-1) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    have hmono := Real.mul_log_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr (le_trans hexp hy1))
      (Set.mem_Ici.mpr (le_trans hexp (le_trans hy1 hy_le_two_x)))
      hy_le_two_x
    have hphi : y * Real.log y ≤ (2 * x) * Real.log (2 * x) := by
      simpa [mul_comm] using hmono
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hxgt)
    have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) hxne
    have hcalc : (2 * x) * Real.log (2 * x) =
        2 * Real.log 2 * x + 2 * (x * Real.log x) := by
      rw [hlogmul]
      ring
    have hyphi_nonneg : 0 ≤ y * Real.log y :=
      mul_nonneg hy0 (Real.log_nonneg hy1)
    have hphi_norm : ‖y * Real.log y‖ = y * Real.log y := by
      rw [Real.norm_eq_abs, abs_of_nonneg hyphi_nonneg]
    rw [hphi_norm]
    have hxphi : 0 ≤ x * Real.log x :=
      mul_nonneg hx (Real.log_nonneg hxgt)
    have hxnorm : ‖x * Real.log x‖ = x * Real.log x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hxphi]
    rw [hxnorm]
    calc
      y * Real.log y ≤ (2 * x) * Real.log (2 * x) := hphi
      _ = 2 * Real.log 2 * x + 2 * (x * Real.log x) := hcalc
      _ = 2 * (x * Real.log x) + (2 * Real.log 2) * x := by ring
      _ ≤ entropyApproximationDensityConstant + 2 * (x * Real.log x) +
          (2 * Real.log 2) * x := by linarith [hC0]

private noncomputable def entropyApproximationMajorant (f : ℝ) : ℝ :=
  entropyApproximationDensityConstant + 2 * ‖entropyDensity f‖ +
    (2 * Real.log 2) * f

private theorem entropyApproximationMajorant_nonneg {f : ℝ} (hf : 0 ≤ f) :
    0 ≤ entropyApproximationMajorant f := by
  unfold entropyApproximationMajorant
  have hC := entropyApproximationDensityConstant_spec.1
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hphi : 0 ≤ 2 * ‖entropyDensity f‖ := by positivity
  have htail : 0 ≤ (2 * Real.log 2) * f :=
    mul_nonneg (mul_nonneg (by norm_num) hlog) hf
  exact add_nonneg (add_nonneg hC hphi) htail

private theorem entropyApproximationMajorant_bound (n : ℕ) {f : ℝ} (hf : 0 ≤ f) :
    ‖entropyDensity (entropyApproximation n f)‖ ≤ entropyApproximationMajorant f := by
  simpa [entropyDensity, entropyApproximationMajorant, add_assoc] using
    entropyApproximation_density_bound n hf

private theorem entropy_norm_le_of_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f μ)
    (hphi_int : Integrable (fun x => entropyDensity (f x)) μ)
    (C : ℝ) (hC : ∫ x, ‖entropyDensity (f x)‖ ∂μ ≤ C) :
    ‖entropy μ f‖ ≤ C + Real.exp (-1) := by
  have hmean_nonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg fun x => hf_nonneg x
  have hjensen :
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ≤
        ∫ x, entropyDensity (f x) ∂μ := by
    exact Real.convexOn_mul_log.map_integral_le
      Real.continuous_mul_log.continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hf_nonneg) hf_int hphi_int
  have hmean_lower :
      -((∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)) ≤ Real.exp (-1) :=
    neg_mul_log_le_exp_neg_one hmean_nonneg
  have hkernel_le :
      ∫ x, entropyDensity (f x) ∂μ ≤ ∫ x, ‖entropyDensity (f x)‖ ∂μ :=
    integral_mono hphi_int hphi_int.norm fun x => le_abs_self _
  have hkernel_le_C :
      ∫ x, f x * Real.log (f x) ∂μ ≤ C := by
    simpa [entropyDensity] using hkernel_le.trans hC
  have hent_nonneg : 0 ≤ entropy μ f := by
    rw [entropy]
    exact sub_nonneg.mpr hjensen
  have hent_upper : entropy μ f ≤ C + Real.exp (-1) := by
    rw [entropy]
    linarith [hkernel_le_C, hmean_lower]
  rw [Real.norm_of_nonneg hent_nonneg]
  exact hent_upper

private theorem entropy_approximation_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f μ)
    (hphi_int : Integrable (fun x => entropyDensity (f x)) μ) :
    Tendsto (fun n => entropy μ (fun x => entropyApproximation n (f x)))
      atTop (𝓝 (entropy μ f)) := by
  let g : ℕ → α → ℝ := fun n x => entropyApproximation n (f x)
  let Q : α → ℝ := fun x => entropyApproximationMajorant (f x)
  have hQ_int : Integrable Q μ := by
    have hcore : Integrable
        (fun x => 2 * ‖entropyDensity (f x)‖ + (2 * Real.log 2) * f x) μ := by
      change Integrable
        ((fun x => 2 * ‖entropyDensity (f x)‖) +
          (fun x => (2 * Real.log 2) * f x)) μ
      exact (hphi_int.norm.const_mul 2).add (hf_int.const_mul (2 * Real.log 2))
    simpa [Q, entropyApproximationMajorant, add_assoc] using
      (integrable_const entropyApproximationDensityConstant).add hcore
  have hg_meas (n : ℕ) : Measurable (g n) := by
    exact hf.add_const _ |>.min measurable_const
  have hmass : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x + 1)
    · intro n
      exact (hg_meas n).aestronglyMeasurable
    · exact hf_int.add (integrable_const 1)
    · intro n
      filter_upwards with x
      have hb := entropyApproximation_bounds n (hf_nonneg x)
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2.2
    · exact Filter.Eventually.of_forall fun x => entropyApproximation_tendsto (f x)
  have hphi_meas (n : ℕ) : Measurable (fun x => entropyDensity (g n x)) := by
    exact (Real.continuous_mul_log.measurable.comp (hg_meas n))
  have hphi_mass :
      Tendsto (fun n => ∫ x, entropyDensity (g n x) ∂μ) atTop
        (𝓝 (∫ x, entropyDensity (f x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence Q
    · intro n
      exact (hphi_meas n).aestronglyMeasurable
    · exact hQ_int
    · intro n
      filter_upwards with x
      exact entropyApproximationMajorant_bound n (hf_nonneg x)
    · exact Filter.Eventually.of_forall fun x => by
        have hx := entropyApproximation_tendsto (f x)
        exact (Real.continuous_mul_log.tendsto (f x)).comp hx
  have hphi_mean :
      Tendsto (fun n => entropyDensity (∫ x, g n x ∂μ)) atTop
        (𝓝 (entropyDensity (∫ x, f x ∂μ))) := by
    exact (Real.continuous_mul_log.tendsto (∫ x, f x ∂μ)).comp hmass
  have h := hphi_mass.sub hphi_mean
  simpa [entropy, entropyDensity, g] using h

private theorem entropy_section_integral_approximation_tendsto
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_int : Integrable F (μ.prod ν))
    (hphiF_int : Integrable (fun p => entropyDensity (F p)) (μ.prod ν)) :
    Tendsto
      (fun n => ∫ y, entropy μ (fun x => entropyApproximation n (F (x, y))) ∂ν)
      atTop
      (𝓝 (∫ y, entropy μ (fun x => F (x, y)) ∂ν)) := by
  let Q : α × β → ℝ := fun p => entropyApproximationMajorant (F p)
  have hQ_int : Integrable Q (μ.prod ν) := by
    have hcore : Integrable
        (fun p => 2 * ‖entropyDensity (F p)‖ + (2 * Real.log 2) * F p)
        (μ.prod ν) := by
      change Integrable
        ((fun p => 2 * ‖entropyDensity (F p)‖) +
          (fun p => (2 * Real.log 2) * F p)) (μ.prod ν)
      exact (hphiF_int.norm.const_mul 2).add (hF_int.const_mul (2 * Real.log 2))
    simpa [Q, entropyApproximationMajorant, add_assoc] using
      (integrable_const entropyApproximationDensityConstant).add hcore
  have hQ_tail_int : Integrable (fun y => ∫ x, Q (x, y) ∂μ) ν :=
    hQ_int.integral_prod_right
  have hD_int : Integrable (fun y => (∫ x, Q (x, y) ∂μ) + Real.exp (-1)) ν :=
    hQ_tail_int.add (integrable_const _)
  have hF_sec_int : ∀ᵐ y ∂ν, Integrable (fun x => F (x, y)) μ :=
    hF_int.prod_left_ae
  have hphiF_sec_int :
      ∀ᵐ y ∂ν, Integrable (fun x => entropyDensity (F (x, y))) μ :=
    hphiF_int.prod_left_ae
  have hQ_sec_int : ∀ᵐ y ∂ν, Integrable (fun x => Q (x, y)) μ :=
    hQ_int.prod_left_ae
  have hsection_limit : ∀ᵐ y ∂ν,
      Tendsto (fun n => entropy μ (fun x => entropyApproximation n (F (x, y))))
        atTop (𝓝 (entropy μ (fun x => F (x, y)))) := by
    filter_upwards [hF_sec_int, hphiF_sec_int] with y hFy hphiFy
    have hFy_meas : Measurable (fun x => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    exact entropy_approximation_tendsto μ (fun x => F (x, y)) hFy_meas
      (fun x => hF_nonneg (x, y)) hFy hphiFy
  have hsection_meas (n : ℕ) :
      Measurable (fun y => entropy μ (fun x => entropyApproximation n (F (x, y)))) := by
    exact entropy_section_measurable μ
      (fun p => entropyApproximation n (F p))
      ((hF.add_const _).min measurable_const)
  have hlimit_meas :
      Measurable (fun y => entropy μ (fun x => F (x, y))) :=
    entropy_section_measurable μ F hF
  have hdominate : ∀ᵐ y ∂ν, ∀ n,
      ‖entropy μ (fun x => entropyApproximation n (F (x, y)))‖ ≤
        (∫ x, Q (x, y) ∂μ) + Real.exp (-1) := by
    filter_upwards [hF_sec_int, hQ_sec_int] with y hFy hQy
    intro n
    let u : α → ℝ := fun x => entropyApproximation n (F (x, y))
    have hu_meas : Measurable u := by
      exact (hF.comp (measurable_prodMk_right (y := y))).add_const _ |>.min measurable_const
    have hu_nonneg (x : α) : 0 ≤ u x := (entropyApproximation_bounds n
      (hF_nonneg (x, y))).1
    have hu_int : Integrable u μ := by
      apply Integrable.of_bound hu_meas.aestronglyMeasurable ((n : ℝ) + 1)
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)]
      change min (F (x, y) + entropyApproximationEpsilon n) ((n : ℝ) + 1) ≤
        (n : ℝ) + 1
      exact min_le_right _ _
    have hphi_meas : Measurable (fun x => entropyDensity (u x)) :=
      Real.continuous_mul_log.measurable.comp hu_meas
    have hphi_int : Integrable (fun x => entropyDensity (u x)) μ := by
      apply hQy.mono' hphi_meas.aestronglyMeasurable
      filter_upwards with x
      have hq0 := entropyApproximationMajorant_nonneg (hF_nonneg (x, y))
      simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using
        entropyApproximationMajorant_bound n (hF_nonneg (x, y))
    have hphi_bound :
        ∫ x, ‖entropyDensity (u x)‖ ∂μ ≤ ∫ x, Q (x, y) ∂μ :=
      integral_mono hphi_int.norm hQy fun x => entropyApproximationMajorant_bound n
        (hF_nonneg (x, y))
    exact entropy_norm_le_of_integrable μ u hu_nonneg hu_int hphi_int _ hphi_bound
  apply tendsto_integral_of_dominated_convergence
    (fun y => (∫ x, Q (x, y) ∂μ) + Real.exp (-1))
  · intro n
    exact (hsection_meas n).aestronglyMeasurable
  · exact hD_int
  · intro n
    filter_upwards [hdominate] with y hy
    exact hy n
  · exact hsection_limit

/-! ### Tensorization on the actual finite product law -/

/-- Coefficient-one entropy tensorization for nonnegative functions with finite
literal entropy on the actual finite i.i.d. product law. Every coordinate
section's two integrability facts are derived from the global hypotheses by
Fubini after the coordinate insertion equivalence. -/
theorem entropy_piFin_succ_subadditive_nonnegative_finite_entropy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : (Fin (r + 1) → EuclideanSpace ℝ ι) → ℝ)
    (hf : Measurable f) (hf_nonneg : ∀ D, 0 ≤ f D)
    (hf_int : Integrable f (Measure.pi fun _ : Fin (r + 1) => μ))
    (hphi_int : Integrable (fun D => f D * Real.log (f D))
      (Measure.pi fun _ : Fin (r + 1) => μ)) :
    entropy (Measure.pi fun _ : Fin (r + 1) => μ) f ≤
      ∑ i : Fin (r + 1),
        ∫ tail : Fin r → EuclideanSpace ℝ ι,
          entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
          ∂Measure.pi fun _ : Fin r => μ := by
  let Ω := Fin (r + 1) → EuclideanSpace ℝ ι
  let π : Measure Ω := Measure.pi fun _ : Fin (r + 1) => μ
  let g : ℕ → Ω → ℝ := fun n D => entropyApproximation n (f D)
  have hg_meas (n : ℕ) : Measurable (g n) := by
    exact (hf.add_const _).min measurable_const
  have hg_bounds (n : ℕ) (D : Ω) :
      entropyApproximationEpsilon n ≤ g n D ∧ g n D ≤ (n : ℝ) + 1 := by
    dsimp [g, entropyApproximation]
    refine ⟨le_min ?_ ?_, min_le_right _ _⟩
    · have h0 := hf_nonneg D
      dsimp [entropyApproximationEpsilon]
      linarith
    · have hε1 := entropyApproximationEpsilon_le_one n
      have hcap : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      linarith
  have happrox_ineq (n : ℕ) :
      entropy π (g n) ≤
        ∑ i : Fin (r + 1),
          ∫ tail : Fin r → EuclideanSpace ℝ ι,
            entropy μ (fun z => g n ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
            ∂Measure.pi fun _ : Fin r => μ := by
    exact entropy_piFin_succ_subadditive_bounded_positive μ (g n)
      (entropyApproximationEpsilon n) ((n : ℝ) + 1) (hg_meas n)
      (entropyApproximationEpsilon_pos n) (hg_bounds n)
  have hleft_limit : Tendsto (fun n => entropy π (g n)) atTop (𝓝 (entropy π f)) := by
    exact entropy_approximation_tendsto π f hf hf_nonneg hf_int (by
      simpa [entropyDensity] using hphi_int)
  have hcoord_limit (i : Fin (r + 1)) :
      Tendsto
        (fun n =>
          ∫ tail : Fin r → EuclideanSpace ℝ ι,
            entropy μ (fun z => g n ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
            ∂Measure.pi fun _ : Fin r => μ)
        atTop
        (𝓝 (∫ tail : Fin r → EuclideanSpace ℝ ι,
          entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
          ∂Measure.pi fun _ : Fin r => μ)) := by
    let Tail := Fin r → EuclideanSpace ℝ ι
    let ν : Measure Tail := Measure.pi fun _ : Fin r => μ
    let e : Ω ≃ᵐ EuclideanSpace ℝ ι × Tail :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i
    let G : EuclideanSpace ℝ ι × Tail → ℝ := fun p => f (e.symm p)
    have he_measure : MeasurePreserving e π (μ.prod ν) := by
      change MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
        π (μ.prod ν)
      exact measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) i
    have hG_meas : Measurable G := hf.comp e.symm.measurable
    have hG_nonneg (p : EuclideanSpace ℝ ι × Tail) : 0 ≤ G p := hf_nonneg (e.symm p)
    have hG_int : Integrable G (μ.prod ν) := by
      change Integrable (f ∘ e.symm) (μ.prod ν)
      exact (he_measure.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf_int
    have hphiG_int : Integrable (fun p => entropyDensity (G p)) (μ.prod ν) := by
      change Integrable ((fun D => entropyDensity (f D)) ∘ e.symm) (μ.prod ν)
      have hsource : Integrable (fun D : Ω => entropyDensity (f D)) π := by
        simpa [entropyDensity] using hphi_int
      exact (he_measure.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hsource
    have hlimit := entropy_section_integral_approximation_tendsto μ ν G
      hG_meas hG_nonneg hG_int hphiG_int
    have hinsert (z : EuclideanSpace ℝ ι) (tail : Tail) :
        e.symm (z, tail) =
          (Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
            (z, tail) := by
      change ((Fin.insertNthEquiv
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm).symm (z, tail) = _
      simp
    have hsection_eq (H : Ω → ℝ) (tail : Tail) :
        entropy μ (fun z => H (e.symm (z, tail))) =
          entropy μ (fun z => H
            ((Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
              (z, tail))) := by
      apply congrArg (entropy μ)
      funext z
      exact congrArg H (hinsert z tail)
    have hlimit_lhs :
        Tendsto
          (fun n => ∫ tail : Tail,
            entropy μ (fun z => entropyApproximation n
              (f ((Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
                (z, tail)))) ∂ν)
          atTop
          (𝓝 (∫ tail : Tail, entropy μ (fun z => f
            ((Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
              (z, tail))) ∂ν)) := by
      have htarget :
          (∫ tail : Tail, entropy μ (fun z => f
            ((Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
              (z, tail))) ∂ν) =
          ∫ tail : Tail, entropy μ (fun z => f (e.symm (z, tail))) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun tail => (hsection_eq f tail).symm
      have hdomain :
          (fun n => ∫ tail : Tail, entropy μ (fun z => entropyApproximation n
            (f ((Fin.insertNthEquiv (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i)
              (z, tail)))) ∂ν) =ᶠ[atTop]
          (fun n => ∫ tail : Tail, entropy μ (fun z => entropyApproximation n
            (G (z, tail))) ∂ν) := by
        filter_upwards with n
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun tail => by
          simpa [G] using (hsection_eq (fun D => entropyApproximation n (f D)) tail).symm
      rw [htarget]
      exact hlimit.congr' hdomain.symm
    simpa [g, ν] using hlimit_lhs
  have hsum_limit :
      Tendsto
        (fun n =>
          ∑ i : Fin (r + 1),
            ∫ tail : Fin r → EuclideanSpace ℝ ι,
              entropy μ (fun z => g n ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
              ∂Measure.pi fun _ : Fin r => μ)
        atTop
        (𝓝 (∑ i : Fin (r + 1),
          ∫ tail : Fin r → EuclideanSpace ℝ ι,
            entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail)))
            ∂Measure.pi fun _ : Fin r => μ)) := by
    exact tendsto_finsetSum Finset.univ (fun i _ => hcoord_limit i)
  exact le_of_tendsto_of_tendsto hleft_limit hsum_limit
    (Filter.Eventually.of_forall happrox_ineq)

#print axioms entropy_piFin_succ_subadditive_nonnegative_finite_entropy

end LOOConcentration.Revision
