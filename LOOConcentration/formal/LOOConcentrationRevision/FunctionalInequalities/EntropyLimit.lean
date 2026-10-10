import LOOConcentrationRevision.FunctionalInequalities.EntropyComputation
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- The positive integral is recovered from finite entropy and its negative part. -/
theorem positive_density_eq_entropy_add_negative (f : Lp ℝ 2 μ)
    (hf : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) μ) :
    ((∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ : ℝ≥0∞) : EReal) =
      (squareEntropy μ f : EReal) +
      ((∫⁻ x, ENNReal.ofReal (-((f x)^2 * Real.log ((f x)^2))) ∂μ : ℝ≥0∞) : EReal) +
      (((∫ x, (f x)^2 ∂μ) * Real.log (∫ x, (f x)^2 ∂μ) : ℝ) : EReal) := by
  have hp : (∫⁻ x, ENNReal.ofReal ((f x)^2 * Real.log ((f x)^2)) ∂μ) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.2).ne
  have hn := (squareEntropy_negative_part_lt_top f).ne
  rw [coe_squareEntropy_eq_expression, ← EReal.coe_ennreal_toReal hp,
    ← EReal.coe_ennreal_toReal hn]
  simp only [← EReal.coe_sub, ← EReal.coe_add]
  congr 1
  ring

/-- The uniformly bounded negative density integral is continuous along a.e. pointwise limits. -/
theorem tendsto_negative_density_integral (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (-((f n x)^2 * Real.log ((f n x)^2))) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (-((g x)^2 * Real.log ((g x)^2))) ∂μ)) := by
  apply tendsto_lintegral_of_dominated_convergence'
    (fun _ : α => ENNReal.ofReal (Real.exp (-1)))
  · intro n
    exact (Real.continuous_mul_log.comp_aestronglyMeasurable
      (integrable_sq (f n)).aestronglyMeasurable).neg.aemeasurable.ennreal_ofReal
  · intro n
    exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
      (neg_mul_log_le_exp_neg_one (sq_nonneg (f n x)))
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [hfg] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_mul_log.tendsto ((g x)^2)).comp (hx.pow 2)).neg

omit [IsProbabilityMeasure μ] in
/-- Strong L2 convergence supplies the square-mean limit needed by the entropy consumer. -/
theorem tendsto_integral_sq_of_tendsto_Lp (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ)) := by
  have heq (v : Lp ℝ 2 μ) : (∫ x, (v x)^2 ∂μ) = ‖v‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  simp_rw [heq]
  exact hfg.norm.pow 2

/-- Fatou and continuity of the negative density discharge the entropy limit step.
The sequence and its hypotheses must be constructed in the zero-energy perturbation consumer. -/
theorem squareEntropy_eq_zero_of_tendsto (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hmean : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ)))
    (hfinite : ∀ n, squareEntropy μ (f n) < ⊤)
    (hentropy : Tendsto (fun n => squareEntropy μ (f n)) atTop (𝓝 0)) :
    squareEntropy μ g = 0 := by
  let P : Lp ℝ 2 μ → ℝ≥0∞ := fun v => ∫⁻ x, ENNReal.ofReal ((v x)^2 * Real.log ((v x)^2)) ∂μ
  let N : Lp ℝ 2 μ → ℝ≥0∞ := fun v => ∫⁻ x, ENNReal.ofReal (-((v x)^2 * Real.log ((v x)^2))) ∂μ
  let M : ℝ := (∫ x, (g x)^2 ∂μ) * Real.log (∫ x, (g x)^2 ∂μ)
  have hi : ∀ n, Integrable (fun x => (f n x)^2 * Real.log ((f n x)^2)) μ :=
    fun n => (squareEntropy_lt_top_iff_integrable_density (f n)).mp (hfinite n)
  have hPfinite : ∀ n, P (f n) ≠ ⊤ := fun n =>
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (hi n).2).ne
  have hNfinite : N g ≠ ⊤ := (squareEntropy_negative_part_lt_top g).ne
  have hES := EReal.tendsto_coe_ennreal.mpr hentropy
  have hEN := EReal.tendsto_coe_ennreal.mpr (tendsto_negative_density_integral f g hfg)
  have hsum := (EReal.continuousAt_add (p := (((0 : ℝ≥0∞) : EReal), (N g : EReal)))
    (Or.inl (by simp)) (Or.inl (by simp))).tendsto.comp (hES.prodMk_nhds hEN)
  simp only [EReal.coe_ennreal_zero, zero_add] at hsum
  have hM := EReal.tendsto_coe.mpr ((Real.continuous_mul_log.tendsto
    (∫ x, (g x)^2 ∂μ)).comp hmean)
  have hsumM := (EReal.continuousAt_add (p := ((N g : EReal), (M : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
      (hsum.prodMk_nhds hM)
  have hPcast : Tendsto (fun n => (P (f n) : EReal)) atTop
      (𝓝 ((N g : EReal) + (M : EReal))) := by
    convert hsumM using 1
    funext n
    exact positive_density_eq_entropy_add_negative (f n) (hi n)
  have hPreal : Tendsto (fun n => (P (f n)).toReal) atTop (𝓝 ((N g).toReal + M)) := by
    apply EReal.tendsto_coe.mp
    convert hPcast using 1
    · funext n
      exact EReal.coe_ennreal_toReal (hPfinite n)
    · rw [EReal.coe_add, EReal.coe_ennreal_toReal hNfinite]
  have hy : 0 ≤ (N g).toReal + M :=
    ge_of_tendsto hPreal (Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  have hPseq : Tendsto (fun n => P (f n)) atTop (𝓝 (ENNReal.ofReal ((N g).toReal + M))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hPreal
    have heq : (fun n => ENNReal.ofReal ((P (f n)).toReal)) = fun n => P (f n) :=
      funext fun n => ENNReal.ofReal_toReal (hPfinite n)
    dsimp only [Function.comp_def] at h
    rwa [heq] at h
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal ((f n x)^2 * Real.log ((f n x)^2)))
      atTop (𝓝 (ENNReal.ofReal ((g x)^2 * Real.log ((g x)^2)))) := by
    filter_upwards [hfg] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_mul_log.tendsto ((g x)^2)).comp (hx.pow 2))
  have hFatou : P g ≤ ENNReal.ofReal ((N g).toReal + M) := by
    calc
      P g = ∫⁻ x, liminf (fun n => ENNReal.ofReal ((f n x)^2 * Real.log ((f n x)^2))) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => P (f n)) atTop := lintegral_liminf_le' fun n =>
        (Real.continuous_mul_log.comp_aestronglyMeasurable
          (integrable_sq (f n)).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      _ = _ := hPseq.liminf_eq
  have hg := integrable_density_of_positive_part_ne_top g
    ((hFatou.trans_lt ENNReal.ofReal_lt_top).ne)
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [ENNReal.toReal_ofReal hy] at hbound
  rw [squareEntropy_eq_of_integrable_density g hg]
  apply ENNReal.ofReal_eq_zero.mpr
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  change (P g).toReal - (N g).toReal - M ≤ 0
  linarith only [hbound]

/-- The actual L2 perturbation supplies pointwise convergence and square-mean convergence.
Only its finite and vanishing entropy bounds remain for the LSI producer. -/
theorem squareEntropy_eq_zero_of_perturbation (g v : Lp ℝ 2 μ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (hfinite : ∀ n, squareEntropy μ (g + t n • v) < ⊤)
    (hentropy : Tendsto (fun n => squareEntropy μ (g + t n • v)) atTop (𝓝 0)) :
    squareEntropy μ g = 0 := by
  have hLp : Tendsto (fun n => g + t n • v) atTop (𝓝 g) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := g)).add (ht.smul (tendsto_const_nhds (x := v)))
  have hae (n : ℕ) : ∀ᵐ x ∂μ, (g + t n • v) x = g x + t n * v x := by
    filter_upwards [Lp.coeFn_add g (t n • v), Lp.coeFn_smul (t n) v] with x ha hs
    change (g + t n • v) x = g x + (t n • v) x at ha
    change (t n • v) x = t n * v x at hs
    rw [ha, hs]
  have hpointwise : ∀ᵐ x ∂μ, Tendsto (fun n => (g + t n • v) x) atTop (𝓝 (g x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    simp_rw [hx]
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := g x)).add (ht.mul_const (v x))
  exact squareEntropy_eq_zero_of_tendsto (fun n => g + t n • v) g hpointwise
    (tendsto_integral_sq_of_tendsto_Lp _ _ hLp) hfinite hentropy

end LOOConcentration.Revision
