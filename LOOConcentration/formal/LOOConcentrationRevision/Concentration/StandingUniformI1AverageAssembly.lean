import LOOConcentrationRevision.Concentration.StandingUniformI1Source
import LOOConcentrationRevision.Concentration.ImportingConsumer
import LOOConcentrationRevision.Results.StandingLossDecomposition
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.DeletedTransport
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Revision
open MeasureTheory
open scoped Gradient

/-- Finite exponential Jensen with a common fixed-parameter moment bound. -/
private theorem exp_integrable_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin (n + 2) → Ω → ℝ) (s Q : ℝ)
    (hXmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hXexp : ∀ i, Integrable (fun ω => Real.exp (s * X i ω)) μ ∧
      (∫ ω, Real.exp (s * X i ω) ∂μ) ≤ Real.exp (Q * s ^ 2)) :
    Integrable (fun ω => Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / (n + 2 : ℝ)))) μ ∧
      (∫ ω, Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / (n + 2 : ℝ))) ∂μ) ≤
        Real.exp (Q * s ^ 2) := by
  let N : ℝ := (n + 2 : ℝ)
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hweights : (∑ i : Fin (n + 2), (1 / N : ℝ)) = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, N, nsmul_eq_mul]
    field_simp [hN]
  have hsumMeas : AEStronglyMeasurable
      (fun ω => ∑ i : Fin (n + 2), X i ω) μ := by
    have hfun : (∑ i : Fin (n + 2), X i) = fun ω => ∑ i : Fin (n + 2), X i ω := by
      ext ω
      simp
    exact hfun ▸ Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hXmeas i)
  have havgMeas : AEStronglyMeasurable
      (fun ω => Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / N))) μ := by
    have harg : AEStronglyMeasurable
        (fun ω => s * ((∑ i : Fin (n + 2), X i ω) / N)) μ := by
      have harg' : AEStronglyMeasurable
          (fun ω => (s / N) * ∑ i : Fin (n + 2), X i ω) μ := hsumMeas.const_mul (s / N)
      convert harg' using 1
      ext ω
      field_simp [hN]
    exact Real.continuous_exp.comp_aestronglyMeasurable harg
  have hsumInt : Integrable
      (fun ω => ∑ i : Fin (n + 2), Real.exp (s * X i ω)) μ := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact (hXexp i).1
  have hjensen (ω : Ω) :
      Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / N)) ≤
        (∑ i : Fin (n + 2), Real.exp (s * X i ω)) / N := by
    have hj := convexOn_exp.map_sum_le
      (t := Finset.univ) (w := fun _ : Fin (n + 2) => (1 / N : ℝ))
      (p := fun i => s * X i ω)
      (fun _ _ => by positivity) hweights (fun _ _ => Set.mem_univ _)
    have hleft : (∑ i : Fin (n + 2), (1 / N : ℝ) * (s * X i ω)) =
        s * ((∑ i : Fin (n + 2), X i ω) / N) := by
      simp only [← Finset.mul_sum]
      field_simp [hN]
    have hright : (∑ i : Fin (n + 2), (1 / N : ℝ) * Real.exp (s * X i ω)) =
        (∑ i : Fin (n + 2), Real.exp (s * X i ω)) / N := by
      simp only [← Finset.mul_sum]
      ring_nf
    simpa only [smul_eq_mul, hleft, hright] using hj
  have havgInt : Integrable
      (fun ω => Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / N))) μ := by
    apply (hsumInt.div_const N).mono' havgMeas
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hjensen ω
  have hsumBound :
      (∑ i : Fin (n + 2), ∫ ω, Real.exp (s * X i ω) ∂μ) ≤
        (n + 2 : ℝ) * Real.exp (Q * s ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin (n + 2), Real.exp (Q * s ^ 2) :=
        Finset.sum_le_sum fun i _ => (hXexp i).2
      _ = (n + 2 : ℝ) * Real.exp (Q * s ^ 2) := by simp
  refine ⟨havgInt, ?_⟩
  calc
    (∫ ω, Real.exp (s * ((∑ i : Fin (n + 2), X i ω) / N)) ∂μ) ≤
        ∫ ω, (∑ i : Fin (n + 2), Real.exp (s * X i ω)) / N ∂μ :=
      integral_mono_ae havgInt (hsumInt.div_const N)
        (Filter.Eventually.of_forall fun ω => hjensen ω)
    _ = ((∑ i : Fin (n + 2), ∫ ω, Real.exp (s * X i ω) ∂μ) / N) := by
      rw [integral_div, integral_finsetSum Finset.univ (fun i _ => (hXexp i).1)]
    _ ≤ Real.exp (Q * s ^ 2) := by
      apply (div_le_iff₀ hNpos).2
      simpa [N, mul_comm] using hsumBound

/-- Uniformize the actual deleted-fit conditional MGF using the standing
coefficient envelopes. The small-parameter cutoff is inherited from the
positive-growth producer; zero growth keeps its all-parameter endpoint. -/
theorem standing_deleted_loss_uniform_section_exp_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d a b : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hb : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b) :
    ∀ s : ℝ, b = 0 ∨
      |s| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal * b) →
      ∀ᵐ z ∂μ,
        Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            Real.exp (s * (fittedLoss (T n) loss D z -
              meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))))
          (Measure.pi fun _ : Fin (n + 1) => μ) ∧
        (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) loss D z -
            meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
            (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) *
              (∫ y, observationNormSq y ∂μ)) * s^2)) := by
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let Q : ℝ := 2 * C * (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) * M₂)
  have hC : 0 ≤ C := by dsimp [C]; exact ENNReal.toReal_nonneg
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg fun z => observationNormSq_nonneg z
  have hpos := standing_deleted_loss_centered_exp_log_bound μ T loss δ₁ δ₂ δ₃ c d hSt
  have hzero := standing_deleted_loss_centered_exp_log_bound_zero μ T loss δ₁ δ₂ δ₃ c d hSt
  intro s hs
  filter_upwards [hpos, hzero, ha, hb] with z hp hz hδ₁ hδ₂
  by_cases hbZero : b = 0
  · have hδ₂Zero : δ₂ (n + 1) z = 0 := by
      apply le_antisymm
      · simpa [hbZero] using hδ₂
      · exact hSt.stable.delta₂_nonneg n z
    obtain ⟨hInt, hBound, _⟩ := hz hδ₂Zero s
    refine ⟨hInt, ?_⟩
    have hδ₁Nonneg := hSt.stable.delta₁_nonneg n z
    have hδ₁Sq : (δ₁ (n + 1) z)^2 ≤ a^2 := by nlinarith
    have hcoef : C * (δ₁ (n + 1) z)^2 / 2 ≤ Q := by
      have hleft := mul_le_mul_of_nonneg_left hδ₁Sq hC
      dsimp [Q]
      have hExtra : 0 ≤ C * b^2 * ((n + 1 : ℕ) : ℝ) * M₂ := by positivity
      rw [hbZero]
      nlinarith
    calc
      _ ≤ Real.exp ((C * (δ₁ (n + 1) z)^2 / 2) * s^2) := by
        simpa [C] using hBound
      _ ≤ Real.exp (Q * s^2) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
  · have hbPos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbZero)
    have hsCut : |s| ≤ 1 / (4 * C * b) := by simpa [C] using hs.resolve_left hbZero
    by_cases hCZero : C = 0
    · have hs0 : s = 0 := by
        have hs' : |s| ≤ 0 := by simpa [hCZero] using hsCut
        exact abs_eq_zero.mp (le_antisymm hs' (abs_nonneg s))
      constructor
      · simp [hs0]
      · simp [hs0]
    · have hCPos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCZero)
      by_cases hδ₂Zero : δ₂ (n + 1) z = 0
      · obtain ⟨hInt, hBound, _⟩ := hz hδ₂Zero s
        refine ⟨hInt, ?_⟩
        have hδ₁Nonneg := hSt.stable.delta₁_nonneg n z
        have hδ₁Sq : (δ₁ (n + 1) z)^2 ≤ a^2 := by nlinarith
        have hcoef : C * (δ₁ (n + 1) z)^2 / 2 ≤ Q := by
          have hleft := mul_le_mul_of_nonneg_left hδ₁Sq hC
          dsimp [Q]
          have hExtra : 0 ≤ C * b^2 * ((n + 1 : ℕ) : ℝ) * M₂ := by positivity
          nlinarith
        calc
          _ ≤ Real.exp ((C * (δ₁ (n + 1) z)^2 / 2) * s^2) := by
            simpa [C] using hBound
          _ ≤ Real.exp (Q * s^2) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
      · have hδ₂Pos : 0 < δ₂ (n + 1) z :=
          lt_of_le_of_ne (hSt.stable.delta₂_nonneg n z) (Ne.symm hδ₂Zero)
        have hdenSmall : 0 < 4 * C * δ₂ (n + 1) z := by positivity
        have hdenBig : 0 < 4 * C * b := by positivity
        have hdenLe : 4 * C * δ₂ (n + 1) z ≤ 4 * C * b := by nlinarith [hδ₂]
        have hrecip := one_div_le_one_div_of_le hdenSmall hdenLe
        obtain ⟨hInt, hBound, _⟩ := hp hδ₂Pos s (hsCut.trans hrecip)
        refine ⟨hInt, ?_⟩
        have hδ₁Nonneg := hSt.stable.delta₁_nonneg n z
        have hδ₁Sq : (δ₁ (n + 1) z)^2 ≤ a^2 := by nlinarith
        have hδ₂Nonneg := hSt.stable.delta₂_nonneg n z
        have hδ₂Sq : (δ₂ (n + 1) z)^2 ≤ b^2 := by nlinarith
        have hNM₂ : 0 ≤ ((n + 1 : ℕ) : ℝ) * M₂ := mul_nonneg (by positivity) hM₂
        have hterm := mul_le_mul_of_nonneg_right hδ₂Sq hNM₂
        have hcoef :
            2 * C * ((δ₁ (n + 1) z)^2 +
              2 * (δ₂ (n + 1) z)^2 * ((n + 1 : ℕ) : ℝ) * M₂) ≤ Q := by
          have hinner : (δ₁ (n + 1) z)^2 +
              2 * (δ₂ (n + 1) z)^2 * ((n + 1 : ℕ) : ℝ) * M₂ ≤
              a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) * M₂ := by nlinarith
          dsimp [Q]
          exact mul_le_mul_of_nonneg_left hinner (by positivity)
        calc
          _ ≤ Real.exp ((2 * C * ((δ₁ (n + 1) z)^2 +
                2 * (δ₂ (n + 1) z)^2 * ((n + 1 : ℕ) : ℝ) * M₂)) * s^2) := by
            simpa [C, M₂] using hBound
          _ ≤ Real.exp (Q * s^2) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)


/-- Transport the uniform conditional MGF through each actual delete-one
coordinate map. This treats the ordered coordinates as equal-law sections and
makes no independence claim about their errors. -/
theorem standing_deleted_coordinate_uniform_exp_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d a b : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hb : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b)
    (i : Fin (n + 2)) :
    ∀ s : ℝ, b = 0 ∨
      |s| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal * b) →
      Integrable
        (fun D : Dataset (Observation k m) (n + 2) =>
          Real.exp (s * (meanFittedLoss μ (T n) loss (D i)
            (hSt.mean_integrable (D i)) - fittedLoss (T n) loss (deleteAt D i) (D i))))
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
      (∫ D : Dataset (Observation k m) (n + 2),
        Real.exp (s * (meanFittedLoss μ (T n) loss (D i)
          (hSt.mean_integrable (D i)) - fittedLoss (T n) loss (deleteAt D i) (D i)))
        ∂Measure.pi fun _ : Fin (n + 2) => μ) ≤
        Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
          (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) *
            (∫ y, observationNormSq y ∂μ)) * s^2)) := by
  intro s hs
  let P : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
    fun p => Real.exp ((-s) * (fittedLoss (T n) loss p.1 p.2 -
      meanFittedLoss μ (T n) loss p.2 (hSt.mean_integrable p.2)))
  let Q : ℝ := 2 * (observationLogSobolevConstant μ).toReal *
    (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ))
  have hsec := standing_deleted_loss_uniform_section_exp_mgf μ T loss δ₁ δ₂ δ₃ c d a b
    hSt ha0 hb0 ha hb (-s) (by simpa [abs_neg] using hs)
  have hshort := standingShortLoss_integrable μ T loss δ₁ δ₂ δ₃ c d hSt
  have hmean : Integrable
      (fun z => meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)) μ := by
    simpa only [meanFittedLoss] using hshort.integral_prod_right
  have hlossMeas : Measurable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T n) loss p.1 p.2) := hSt.stable.measurable_loss n
  have hfAEM : AEStronglyMeasurable f (P.prod μ) := by
    have harg : AEStronglyMeasurable
        (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
          (-s) * (fittedLoss (T n) loss p.1 p.2 -
            meanFittedLoss μ (T n) loss p.2 (hSt.mean_integrable p.2))) (P.prod μ) := by
      exact (hlossMeas.aestronglyMeasurable.sub
        hmean.aestronglyMeasurable.comp_snd).const_mul (-s)
    exact Real.continuous_exp.comp_aestronglyMeasurable harg
  have hnormMeas : AEStronglyMeasurable
      (fun z => ∫ D : Dataset (Observation k m) (n + 1), ‖f (D, z)‖ ∂P) μ :=
    hfAEM.prod_swap.norm.integral_prod_right'
  have hsecNormInt : Integrable
      (fun z => ∫ D : Dataset (Observation k m) (n + 1), ‖f (D, z)‖ ∂P) μ := by
    apply (integrable_const (Real.exp (Q * s^2))).mono' hnormMeas
    filter_upwards [hsec] with z hz
    have hEq : (∫ D : Dataset (Observation k m) (n + 1), ‖f (D, z)‖ ∂P) =
        ∫ D, f (D, z) ∂P := by
      apply integral_congr_ae
      filter_upwards with D
      exact Real.norm_of_nonneg (Real.exp_nonneg _)
    have hIpos : 0 ≤ ∫ D : Dataset (Observation k m) (n + 1), f (D, z) ∂P :=
      integral_nonneg (fun D => Real.exp_nonneg _)
    have hNormPos : 0 ≤ ∫ D : Dataset (Observation k m) (n + 1), ‖f (D, z)‖ ∂P :=
      integral_nonneg (fun D => norm_nonneg _)
    rw [Real.norm_of_nonneg hNormPos, hEq]
    simpa [f, Q] using hz.2
  have hsecInt : ∀ᵐ z ∂μ,
      Integrable (fun D : Dataset (Observation k m) (n + 1) => f (D, z)) P := by
    filter_upwards [hsec] with z hz
    simpa only [P, f] using hz.1
  have hprodInt : Integrable f (P.prod μ) :=
    (integrable_prod_iff' hfAEM).2 ⟨hsecInt, hsecNormInt⟩
  have hOuterInt : Integrable
      (fun z => ∫ D : Dataset (Observation k m) (n + 1), f (D, z) ∂P) μ :=
    hprodInt.integral_prod_right
  have hOuterBound :
      (∫ z, ∫ D : Dataset (Observation k m) (n + 1), f (D, z) ∂P ∂μ) ≤
        Real.exp (Q * s^2) := by
    calc
      _ ≤ ∫ _z : Observation k m, Real.exp (Q * s^2) ∂μ :=
        integral_mono_ae hOuterInt (integrable_const _) (by
          filter_upwards [hsec] with z hz
          simpa [f, Q] using hz.2)
      _ = Real.exp (Q * s^2) := by simp
  have hprodBound : (∫ p, f p ∂(P.prod μ)) ≤ Real.exp (Q * s^2) := by
    rw [integral_prod_symm f hprodInt]
    exact hOuterBound
  have hdeletedInt := deleted_section_integrable μ i f hprodInt
  have hdeletedIntegral := deleted_section_integral μ i f hprodInt
  have hactualInt : Integrable
      (fun D : Dataset (Observation k m) (n + 2) =>
        Real.exp (s * (meanFittedLoss μ (T n) loss (D i)
          (hSt.mean_integrable (D i)) - fittedLoss (T n) loss (deleteAt D i) (D i))))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
    convert hdeletedInt using 1
    funext D
    simp [f]
    ring_nf
  refine ⟨hactualInt, ?_⟩
  calc
    _ = ∫ D : Dataset (Observation k m) (n + 2), f (deleteAt D i, D i)
          ∂Measure.pi fun _ : Fin (n + 2) => μ := by
      apply integral_congr_ae
      filter_upwards with D
      simp [f]
      ring_nf
    _ = ∫ p, f p ∂(P.prod μ) := hdeletedIntegral
    _ ≤ Real.exp (Q * s^2) := hprodBound


/-- The full-sample standing-I1 MGF, obtained from the actual deleted-fit
coordinate bounds by finite exponential Jensen. -/
theorem standing_I1_actual_uniform_average_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d a b : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hb : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b) :
    ∀ s : ℝ, b = 0 ∨
      |s| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal * b) →
      Integrable
        (fun D : Dataset (Observation k m) (n + 2) =>
          Real.exp (s * standingI1 μ T loss δ₁ δ₂ δ₃ c d hSt D))
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
      (∫ D : Dataset (Observation k m) (n + 2),
        Real.exp (s * standingI1 μ T loss δ₁ δ₂ δ₃ c d hSt D)
        ∂Measure.pi fun _ : Fin (n + 2) => μ) ≤
        Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
          (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) *
            (∫ y, observationNormSq y ∂μ)) * s^2)) := by
  intro s hs
  let ν : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let X : Fin (n + 2) → Dataset (Observation k m) (n + 2) → ℝ :=
    fun i D => meanFittedLoss μ (T n) loss (D i) (hSt.mean_integrable (D i)) -
      fittedLoss (T n) loss (deleteAt D i) (D i)
  let Q : ℝ := 2 * (observationLogSobolevConstant μ).toReal *
    (a^2 + 2 * b^2 * ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ))
  have hshort := standingShortLoss_integrable μ T loss δ₁ δ₂ δ₃ c d hSt
  have hmean : Integrable
      (fun z => meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)) μ := by
    simpa only [meanFittedLoss] using hshort.integral_prod_right
  have hXmeas : ∀ i, AEStronglyMeasurable (X i) ν := by
    intro i
    have hmeanCoord : Integrable
        (fun D : Dataset (Observation k m) (n + 2) =>
          meanFittedLoss μ (T n) loss (D i) (hSt.mean_integrable (D i))) ν := by
      exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hmean
    have hdeleted : Integrable
        (fun D : Dataset (Observation k m) (n + 2) =>
          fittedLoss (T n) loss (deleteAt D i) (D i)) ν :=
      hSt.stable.integrable_deleted n i
    have hXi : Integrable (X i) ν := by
      exact hmeanCoord.sub hdeleted
    exact hXi.aestronglyMeasurable
  have hXexp : ∀ i, Integrable (fun D => Real.exp (s * X i D)) ν ∧
      (∫ D, Real.exp (s * X i D) ∂ν) ≤ Real.exp (Q * s^2) := by
    intro i
    have hcoord := standing_deleted_coordinate_uniform_exp_mgf μ T loss δ₁ δ₂ δ₃ c d a b
      hSt ha0 hb0 ha hb i s hs
    simpa [X, Q, ν] using hcoord
  have haverage := exp_integrable_average_bound ν X s Q hXmeas hXexp
  have hidentity (D : Dataset (Observation k m) (n + 2)) :
      standingI1 μ T loss δ₁ δ₂ δ₃ c d hSt D =
        (∑ i : Fin (n + 2), X i D) / (n + 2 : ℝ) := by
    simpa [X] using
      standing_I1_actual_deleted_section_average μ T loss δ₁ δ₂ δ₃ c d hSt D
  have hfun :
      (fun D : Dataset (Observation k m) (n + 2) =>
        Real.exp (s * standingI1 μ T loss δ₁ δ₂ δ₃ c d hSt D)) =
      (fun D => Real.exp (s * ((∑ i : Fin (n + 2), X i D) / (n + 2 : ℝ)))) := by
    funext D
    rw [hidentity D]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact haverage.1
  · rw [hfun]
    exact haverage.2

end LOOConcentration.Revision
