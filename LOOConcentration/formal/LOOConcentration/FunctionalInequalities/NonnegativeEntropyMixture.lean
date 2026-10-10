import LOOConcentration.FunctionalInequalities.EntropyMixture
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Entropy tensorization for bounded nonnegative functions

Approximation by strictly positive functions extends the coefficient-one
two-factor entropy inequality to bounded nonnegative data, including functions
that vanish. Continuity of `x * log x` at zero and dominated convergence
control the entropy and both conditional entropy integrals.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology

private noncomputable def nonnegativeEntropyApproximation (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private theorem nonnegativeEntropyApproximation_pos (n : ℕ) :
    0 < nonnegativeEntropyApproximation n := by
  dsimp [nonnegativeEntropyApproximation]
  positivity

private theorem nonnegativeEntropyApproximation_le_one (n : ℕ) :
    nonnegativeEntropyApproximation n ≤ 1 := by
  dsimp [nonnegativeEntropyApproximation]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem nonnegativeEntropyApproximation_tendsto_zero :
    Tendsto nonnegativeEntropyApproximation atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private theorem exists_mul_log_norm_bound_nonnegative (B : ℝ) :
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

private theorem integrable_mul_log_of_mem_Icc_nonnegative
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ}
    (hfx : ∀ x, f x ∈ Set.Icc 0 B) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  obtain ⟨C, hC0, hC⟩ := exists_mul_log_norm_bound_nonnegative B
  refine Integrable.of_bound
    ((Real.continuous_mul_log.measurable.comp hf).aestronglyMeasurable) C ?_
  filter_upwards with x
  exact hC (f x) (hfx x)

private theorem integrable_of_nonnegative_bounded
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ}
    (hfx : ∀ x, 0 ≤ f x ∧ f x ≤ B) : Integrable f μ := by
  refine Integrable.of_mem_Icc 0 B hf.aemeasurable ?_
  exact Filter.Eventually.of_forall fun x => hfx x

private theorem entropy_section_integrable_nonnegative
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν]
    (F : α × β → ℝ) (B : ℝ)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    Integrable (fun y => entropy μ (fun x => F (x, y))) ν := by
  let phi : ℝ → ℝ := fun z => z * Real.log z
  have hF_values (p : α × β) : F p ∈ Set.Icc 0 B :=
    ⟨hF_nonneg p, hF_le p⟩
  have hF_prod_int : Integrable F (μ.prod ν) :=
    integrable_of_nonnegative_bounded (μ.prod ν) hF fun p =>
      ⟨hF_nonneg p, hF_le p⟩
  have hphiF_meas : Measurable (fun p : α × β => phi (F p)) := by
    exact Real.continuous_mul_log.measurable.comp hF
  have hphiF_int : Integrable (fun p : α × β => phi (F p)) (μ.prod ν) := by
    exact integrable_mul_log_of_mem_Icc_nonnegative (μ.prod ν) hF hF_values
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let phiMean : β → ℝ := fun y => ∫ x, phi (F (x, y)) ∂μ
  have hmean_strong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hmean_meas : Measurable mean := hmean_strong.measurable
  have hphiMean_strong : StronglyMeasurable phiMean := by
    change StronglyMeasurable (fun y => ∫ x, phi (F (x, y)) ∂μ)
    exact hphiF_meas.stronglyMeasurable.integral_prod_left'
  have hphiMean_meas : Measurable phiMean := hphiMean_strong.measurable
  have hmean_int : Integrable mean ν := by
    change Integrable (fun y => ∫ x, F (x, y) ∂μ) ν
    exact hF_prod_int.integral_prod_right
  have hphiMean_int : Integrable phiMean ν := by
    change Integrable (fun y => ∫ x, phi (F (x, y)) ∂μ) ν
    exact hphiF_int.integral_prod_right
  have hmean_values (y : β) : mean y ∈ Set.Icc 0 B := by
    have hsection_meas : Measurable (fun x : α => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    have hsection_int : Integrable (fun x : α => F (x, y)) μ :=
      integrable_of_nonnegative_bounded μ hsection_meas fun x =>
        ⟨hF_nonneg (x, y), hF_le (x, y)⟩
    constructor
    · exact integral_nonneg fun x => hF_nonneg (x, y)
    · calc
        mean y ≤ ∫ x : α, (B : ℝ) ∂μ :=
          integral_mono hsection_int (integrable_const B) fun x => hF_le (x, y)
        _ = B := by simp
  have hphiMeanComp_int :
      Integrable (fun y => mean y * Real.log (mean y)) ν := by
    exact integrable_mul_log_of_mem_Icc_nonnegative ν hmean_meas hmean_values
  have hsection_eq :
      (fun y => entropy μ (fun x => F (x, y))) =
        (fun y => phiMean y - mean y * Real.log (mean y)) := by
    funext y
    simp [entropy, phi, mean, phiMean]
  rw [hsection_eq]
  exact hphiMean_int.sub hphiMeanComp_int

private theorem entropy_outer_integrable_nonnegative
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    Integrable (fun x => entropy ν (fun y => F (x, y))) μ := by
  let Fswap : β × α → ℝ := fun p => F (p.2, p.1)
  have hFswap : Measurable Fswap := hF.comp measurable_swap
  have hFswap_nonneg (p : β × α) : 0 ≤ Fswap p := hF_nonneg (p.2, p.1)
  have hFswap_le (p : β × α) : Fswap p ≤ B := hF_le (p.2, p.1)
  have h := entropy_section_integrable_nonnegative ν μ Fswap B
    hFswap hFswap_nonneg hFswap_le
  simpa [Fswap] using h

/-- Both conditional entropy functions of a bounded nonnegative measurable
function on a probability product are genuinely integrable. -/
theorem entropy_two_factor_conditional_integrable_bounded_nonnegative
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    Integrable (fun x => entropy ν (fun y => F (x, y))) μ ∧
      Integrable (fun y => entropy μ (fun x => F (x, y))) ν := by
  refine ⟨entropy_outer_integrable_nonnegative μ ν F B hF hF_nonneg hF_le, ?_⟩
  exact entropy_section_integrable_nonnegative μ ν F B hF hF_nonneg hF_le

private theorem norm_entropy_le_twice_mul_log_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (B C : ℝ)
    (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ B)
    (hC : ∀ z ∈ Set.Icc (0 : ℝ) B, ‖z * Real.log z‖ ≤ C) :
    ‖entropy μ f‖ ≤ 2 * C := by
  let mean : ℝ := ∫ x, f x ∂μ
  have hf_int : Integrable f μ :=
    integrable_of_nonnegative_bounded μ hf fun x => ⟨hf_nonneg x, hf_le x⟩
  have hphi_int : Integrable (fun x => f x * Real.log (f x)) μ :=
    integrable_mul_log_of_mem_Icc_nonnegative μ hf fun x =>
      ⟨hf_nonneg x, hf_le x⟩
  have hmean_values : mean ∈ Set.Icc 0 B := by
    constructor
    · exact integral_nonneg fun x => hf_nonneg x
    · calc
        mean ≤ ∫ x, (B : ℝ) ∂μ :=
          integral_mono hf_int (integrable_const B) hf_le
        _ = B := by simp
  have hfirst :
      ‖∫ x, f x * Real.log (f x) ∂μ‖ ≤ C := by
    calc
      ‖∫ x, f x * Real.log (f x) ∂μ‖ ≤
          ∫ x, ‖f x * Real.log (f x)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _x, C ∂μ :=
        integral_mono hphi_int.norm (integrable_const C) fun x =>
          hC (f x) ⟨hf_nonneg x, hf_le x⟩
      _ = C := by simp
  have hsecond : ‖mean * Real.log mean‖ ≤ C := hC mean hmean_values
  unfold entropy
  change ‖(∫ x, f x * Real.log (f x) ∂μ) - mean * Real.log mean‖ ≤ 2 * C
  calc
    _ ≤ ‖∫ x, f x * Real.log (f x) ∂μ‖ + ‖mean * Real.log mean‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add hfirst hsecond
    _ = 2 * C := by ring

/-- Entropy is continuous under adding the positive sequence `1/(n+1)` to a
bounded nonnegative measurable function on a probability space. The mass and
`x log x` integrals each converge by dominated convergence on an explicit
compact-range bound. -/
private theorem entropy_add_approximation_tendsto
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ B) :
    Tendsto (fun n => entropy μ (fun x => f x + nonnegativeEntropyApproximation n))
      atTop (𝓝 (entropy μ f)) := by
  let phi : ℝ → ℝ := fun z => z * Real.log z
  let approximants : ℕ → α → ℝ := fun n x => f x + nonnegativeEntropyApproximation n
  obtain ⟨C, hC0, hC⟩ := exists_mul_log_norm_bound_nonnegative (B + 1)
  have hB1 : 0 ≤ B + 1 := by linarith
  have happ_values (n : ℕ) (x : α) : approximants n x ∈ Set.Icc 0 (B + 1) := by
    constructor
    · exact add_nonneg (hf_nonneg x) (le_of_lt (nonnegativeEntropyApproximation_pos n))
    · calc
        approximants n x ≤ B + nonnegativeEntropyApproximation n := by
          dsimp [approximants]
          linarith [hf_le x]
        _ ≤ B + 1 := by linarith [nonnegativeEntropyApproximation_le_one n]
  have happ_meas (n : ℕ) : Measurable (approximants n) := by
    exact hf.add measurable_const
  have happrox_tendsto (x : α) :
      Tendsto (fun n => approximants n x) atTop (𝓝 (f x)) := by
    simpa [approximants] using
      (tendsto_const_nhds.add nonnegativeEntropyApproximation_tendsto_zero)
  have hphi_tendsto (x : α) :
      Tendsto (fun n => phi (approximants n x)) atTop (𝓝 (phi (f x))) := by
    exact (Real.continuous_mul_log.tendsto (f x)).comp (happrox_tendsto x)
  have hmass_tendsto :
      Tendsto (fun n => ∫ x, approximants n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : α => B + 1)
    · intro n
      exact (happ_meas n).aestronglyMeasurable
    · exact integrable_const (B + 1)
    · intro n
      filter_upwards with x
      have hx := happ_values n x
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    · exact Filter.Eventually.of_forall happrox_tendsto
  have hphi_mass_tendsto :
      Tendsto (fun n => phi (∫ x, approximants n x ∂μ))
        atTop (𝓝 (phi (∫ x, f x ∂μ))) := by
    exact (Real.continuous_mul_log.tendsto (∫ x, f x ∂μ)).comp hmass_tendsto
  have hkernel_tendsto :
      Tendsto (fun n => ∫ x, phi (approximants n x) ∂μ)
        atTop (𝓝 (∫ x, phi (f x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : α => C)
    · intro n
      exact ((Real.continuous_mul_log.measurable.comp (happ_meas n)).aestronglyMeasurable)
    · exact integrable_const C
    · intro n
      filter_upwards with x
      exact hC (approximants n x) (happ_values n x)
    · exact Filter.Eventually.of_forall hphi_tendsto
  have hentropy := hkernel_tendsto.sub hphi_mass_tendsto
  simpa [entropy, phi, approximants] using hentropy

/-- The outer integral of a conditional entropy converges under the same
positive approximation. The uniform dominating constant follows from the
compact `[0,B+1]` bound for `x log x`. -/
private theorem entropy_outer_integral_add_approximation_tendsto
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    Tendsto
      (fun n => ∫ x, entropy ν
        (fun y => F (x, y) + nonnegativeEntropyApproximation n) ∂μ)
      atTop
      (𝓝 (∫ x, entropy ν (fun y => F (x, y)) ∂μ)) := by
  let phi : ℝ → ℝ := fun z => z * Real.log z
  let Fplus : ℕ → α × β → ℝ := fun n p => F p + nonnegativeEntropyApproximation n
  let sectionEntropy : ℕ → α → ℝ := fun n x =>
    entropy ν (fun y => F (x, y) + nonnegativeEntropyApproximation n)
  obtain ⟨C, hC0, hC⟩ := exists_mul_log_norm_bound_nonnegative (B + 1)
  have hB1 : 0 ≤ B + 1 := by linarith
  have hFplus_meas (n : ℕ) : Measurable (Fplus n) := by
    exact hF.add measurable_const
  have hFplus_bounds (n : ℕ) (p : α × β) :
      0 ≤ Fplus n p ∧ Fplus n p ≤ B + 1 := by
    constructor
    · exact add_nonneg (hF_nonneg p) (le_of_lt (nonnegativeEntropyApproximation_pos n))
    · calc
        Fplus n p ≤ B + nonnegativeEntropyApproximation n := by
          dsimp [Fplus]
          linarith [hF_le p]
        _ ≤ B + 1 := by linarith [nonnegativeEntropyApproximation_le_one n]
  have hsection_int (n : ℕ) : Integrable (sectionEntropy n) μ := by
    let FplusSwap : β × α → ℝ := fun p => F (p.2, p.1) + nonnegativeEntropyApproximation n
    have hFplusSwap : Measurable FplusSwap := by
      exact (hF.comp measurable_swap).add measurable_const
    have hFplusSwap_nonneg (p : β × α) : 0 ≤ FplusSwap p := by
      exact (add_nonneg (hF_nonneg (p.2, p.1))
        (le_of_lt (nonnegativeEntropyApproximation_pos n)))
    have hFplusSwap_le (p : β × α) : FplusSwap p ≤ B + 1 := by
      calc
        F (p.2, p.1) + nonnegativeEntropyApproximation n ≤
            B + nonnegativeEntropyApproximation n := by
          linarith [hF_le (p.2, p.1)]
        _ ≤ B + 1 := by linarith [nonnegativeEntropyApproximation_le_one n]
    have h := entropy_section_integrable_nonnegative ν μ FplusSwap (B + 1)
      hFplusSwap hFplusSwap_nonneg hFplusSwap_le
    simpa [sectionEntropy, FplusSwap] using h
  have hsectionF_int :
      Integrable (fun x => entropy ν (fun y => F (x, y))) μ :=
    entropy_outer_integrable_nonnegative μ ν F B hF hF_nonneg hF_le
  have hsection_limit (x : α) :
      Tendsto (fun n => sectionEntropy n x) atTop
        (𝓝 (entropy ν (fun y => F (x, y)))) := by
    have hsection_meas : Measurable (fun y : β => F (x, y)) :=
      hF.comp (measurable_prodMk_left (x := x))
    exact entropy_add_approximation_tendsto ν (fun y => F (x, y)) B hB
      hsection_meas (fun y => hF_nonneg (x, y)) (fun y => hF_le (x, y))
  have hsection_bound (n : ℕ) (x : α) : ‖sectionEntropy n x‖ ≤ 2 * C := by
    have hsection_meas :
        Measurable (fun y : β => F (x, y) + nonnegativeEntropyApproximation n) := by
      exact (hF.comp (measurable_prodMk_left (x := x))).add measurable_const
    have hsection_values (y : β) :
        0 ≤ F (x, y) + nonnegativeEntropyApproximation n ∧
          F (x, y) + nonnegativeEntropyApproximation n ≤ B + 1 := by
      constructor
      · exact add_nonneg (hF_nonneg (x, y))
          (le_of_lt (nonnegativeEntropyApproximation_pos n))
      · calc
          F (x, y) + nonnegativeEntropyApproximation n ≤
              B + nonnegativeEntropyApproximation n := by
            linarith [hF_le (x, y)]
          _ ≤ B + 1 := by linarith [nonnegativeEntropyApproximation_le_one n]
    exact norm_entropy_le_twice_mul_log_bound ν
      (fun y => F (x, y) + nonnegativeEntropyApproximation n) (B + 1) C
      hsection_meas (fun y => (hsection_values y).1)
      (fun y => (hsection_values y).2) hC
  apply tendsto_integral_of_dominated_convergence (fun _ : α => 2 * C)
  · intro n
    exact (hsection_int n).aestronglyMeasurable
  · exact integrable_const (2 * C)
  · intro n
    filter_upwards with x
    exact hsection_bound n x
  · exact Filter.Eventually.of_forall hsection_limit

/-- Both conditional entropy functions are integrable for bounded
nonnegative measurable data, and their actual coefficient-one tensorization
inequality holds. The proof uses `F + 1/(n+1)`, the accepted positive theorem,
and dominated convergence; it permits zeros of `F`. -/
theorem entropy_two_factor_subadditive_bounded_nonnegative
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    entropy (μ.prod ν) F ≤
      (∫ x, entropy ν (fun y => F (x, y)) ∂μ) +
        (∫ y, entropy μ (fun x => F (x, y)) ∂ν) := by
  let Fplus : ℕ → α × β → ℝ := fun n p => F p + nonnegativeEntropyApproximation n
  have hFplus_meas (n : ℕ) : Measurable (Fplus n) := by
    exact hF.add measurable_const
  have hFplus_bounds (n : ℕ) (p : α × β) :
      0 < nonnegativeEntropyApproximation n ∧
        nonnegativeEntropyApproximation n ≤ Fplus n p ∧ Fplus n p ≤ B + 1 := by
    refine ⟨nonnegativeEntropyApproximation_pos n, ?_, ?_⟩
    · dsimp [Fplus]
      linarith [hF_nonneg p]
    · calc
        Fplus n p ≤ B + nonnegativeEntropyApproximation n := by
          dsimp [Fplus]
          linarith [hF_le p]
        _ ≤ B + 1 := by linarith [nonnegativeEntropyApproximation_le_one n]
  have hpositive_ineq (n : ℕ) :
      entropy (μ.prod ν) (Fplus n) ≤
        (∫ x, entropy ν (fun y => Fplus n (x, y)) ∂μ) +
          (∫ y, entropy μ (fun x => Fplus n (x, y)) ∂ν) := by
    have h := entropy_two_factor_subadditive_bounded_positive μ ν (Fplus n)
      (nonnegativeEntropyApproximation n) (B + 1) (hFplus_meas n)
      (nonnegativeEntropyApproximation_pos n) fun p =>
        ⟨(hFplus_bounds n p).2.1, (hFplus_bounds n p).2.2⟩
    simpa only [Fplus] using h
  have hleft_limit :
      Tendsto (fun n => entropy (μ.prod ν) (Fplus n)) atTop
        (𝓝 (entropy (μ.prod ν) F)) := by
    have h := entropy_add_approximation_tendsto (μ.prod ν) F B hB
      hF hF_nonneg hF_le
    simpa only [Fplus] using h
  have hfirst_conditional_limit :
      Tendsto
        (fun n => ∫ x, entropy ν (fun y => Fplus n (x, y)) ∂μ)
        atTop (𝓝 (∫ x, entropy ν (fun y => F (x, y)) ∂μ)) := by
    have h := entropy_outer_integral_add_approximation_tendsto μ ν F B hB
      hF hF_nonneg hF_le
    simpa only [Fplus] using h
  let Fswap : β × α → ℝ := fun p => F (p.2, p.1)
  have hFswap_meas : Measurable Fswap := hF.comp measurable_swap
  have hFswap_nonneg (p : β × α) : 0 ≤ Fswap p := hF_nonneg (p.2, p.1)
  have hFswap_le (p : β × α) : Fswap p ≤ B := hF_le (p.2, p.1)
  have hsecond_conditional_limit :
      Tendsto
        (fun n => ∫ y, entropy μ (fun x => Fplus n (x, y)) ∂ν)
        atTop (𝓝 (∫ y, entropy μ (fun x => F (x, y)) ∂ν)) := by
    have h := entropy_outer_integral_add_approximation_tendsto ν μ Fswap B hB
      hFswap_meas hFswap_nonneg hFswap_le
    simpa only [Fswap, Fplus] using h
  have hright_limit := hfirst_conditional_limit.add hsecond_conditional_limit
  exact le_of_tendsto_of_tendsto hleft_limit hright_limit
    (Filter.Eventually.of_forall hpositive_ineq)

#print axioms entropy_two_factor_conditional_integrable_bounded_nonnegative
#print axioms entropy_two_factor_subadditive_bounded_nonnegative

end LOOConcentration
