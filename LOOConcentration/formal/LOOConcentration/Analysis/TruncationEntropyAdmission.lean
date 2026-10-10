import LOOConcentration.Analysis.ClipMollify
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LOOConcentration

/-- The square of the literal symmetric truncation at cap `n + 1`. -/
def entropyClipSquare {Ω : Type*} (u : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (clipValue ((n : ℝ) + 1) (u ω)) ^ 2

private noncomputable def mulLogKernel (x : ℝ) : ℝ := x * Real.log x

private noncomputable def shiftedMulLogKernel (x : ℝ) : ℝ :=
  mulLogKernel x + Real.exp (-1)

private theorem continuous_clipValue_local (A : ℝ) :
    Continuous (fun x : ℝ => clipValue A x) := by
  unfold clipValue
  exact continuous_const.max (continuous_id.min continuous_const)

private theorem clipValue_eq_self_of_abs_lt_local {A x : ℝ} (h : |x| < A) :
    clipValue A x = x := by
  have hx := abs_lt.mp h
  unfold clipValue
  rw [min_eq_left hx.2.le, max_eq_right hx.1.le]

private theorem clipValue_tendsto_atTop_local (x : ℝ) :
    Tendsto (fun A : ℝ => clipValue A x) atTop (𝓝 x) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop |x|] with A hA
  exact (clipValue_eq_self_of_abs_lt_local hA).symm

private theorem clipValue_sequence_tendsto_local (x : ℝ) :
    Tendsto (fun n : ℕ => clipValue ((n : ℝ) + 1) x) atTop (𝓝 x) := by
  have hcap : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (clipValue_tendsto_atTop_local x).comp hcap

private theorem clipValue_abs_le_abs_local {A x : ℝ} (hA : 0 ≤ A) :
    |clipValue A x| ≤ |x| := by
  have hzero : clipValue A 0 = 0 := by
    simp [clipValue, hA]
  simpa [hzero] using abs_clipValue_sub_le A x 0

private theorem mulLogKernel_lower_shift (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ shiftedMulLogKernel x := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hprod := Real.negMulLog_mul x (Real.exp 1)
  have hnegExp : Real.negMulLog (Real.exp 1) = -Real.exp 1 := by
    simp [Real.negMulLog_def, Real.log_exp]
  have hbound := Real.negMulLog_le_one_sub_self
    (mul_nonneg hx (le_of_lt he))
  rw [hprod, hnegExp] at hbound
  have hmul : Real.exp 1 * Real.negMulLog x ≤ 1 := by nlinarith
  have hlog : Real.negMulLog x ≤ 1 / Real.exp 1 :=
    (le_div_iff₀ he).2 (by nlinarith)
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg]
    simp
  have hnegMulLog : Real.negMulLog x = -(x * Real.log x) := by
    rw [Real.negMulLog_eq_neg]
  change 0 ≤ x * Real.log x + Real.exp (-1)
  rw [hnegMulLog, ← hexp] at hlog
  nlinarith

private theorem integrable_mulLogKernel_of_bounded_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f)
    (hfb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ B) :
    Integrable (fun ω => mulLogKernel (f ω)) μ := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) B))
    Real.continuous_mul_log.continuousOn
  let C' := max C 0
  have hgmeas : Measurable (fun ω => mulLogKernel (f ω)) := by
    exact (Real.continuous_mul_log.measurable).comp hf
  refine (integrable_const C').mono' hgmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hbound := hC (f ω) (Set.mem_Icc.mpr (hfb ω))
  dsimp [C']
  exact hbound.trans (le_max_left _ _)

private theorem integrable_entropyClipSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} (hu : Measurable u) (n : ℕ) :
    Integrable (entropyClipSquare u n) μ := by
  have hclip : Measurable (fun ω => clipValue ((n : ℝ) + 1) (u ω)) :=
    (continuous_clipValue_local _).measurable.comp hu
  have hnonneg (ω : Ω) : 0 ≤ entropyClipSquare u n ω := sq_nonneg _
  have hbound (ω : Ω) : entropyClipSquare u n ω ≤ ((n : ℝ) + 1) ^ 2 := by
    have hcap : 0 ≤ (n : ℝ) + 1 := by positivity
    have hclipBounds := clipValue_bounds (u := u ω) hcap
    have habs : |clipValue ((n : ℝ) + 1) (u ω)| ≤ (n : ℝ) + 1 :=
      abs_le.mpr ⟨by linarith [hclipBounds.1], hclipBounds.2⟩
    change (clipValue ((n : ℝ) + 1) (u ω)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2
    nlinarith [mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hcap (abs_nonneg (clipValue ((n : ℝ) + 1) (u ω))))]
  have hmeas : Measurable (entropyClipSquare u n) := by
    exact (hclip.pow_const 2)
  refine (integrable_const (((n : ℝ) + 1) ^ 2)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_of_nonneg (hnonneg ω)]
  exact hbound ω

private theorem integrable_mulLog_entropyClipSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} (hu : Measurable u) (n : ℕ) :
    Integrable (fun ω => mulLogKernel (entropyClipSquare u n ω)) μ := by
  apply integrable_mulLogKernel_of_bounded_nonneg
    (f := entropyClipSquare u n) (B := ((n : ℝ) + 1) ^ 2)
  · exact ((continuous_clipValue_local _).measurable.comp hu).pow_const 2
  · intro ω
    exact ⟨sq_nonneg _, by
      have hcap : 0 ≤ (n : ℝ) + 1 := by positivity
      have hclipBounds := clipValue_bounds (u := u ω) hcap
      have habs : |clipValue ((n : ℝ) + 1) (u ω)| ≤ (n : ℝ) + 1 :=
        abs_le.mpr ⟨by linarith [hclipBounds.1], hclipBounds.2⟩
      change (clipValue ((n : ℝ) + 1) (u ω)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2
      nlinarith [mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg hcap (abs_nonneg (clipValue ((n : ℝ) + 1) (u ω))))]⟩

private theorem entropyClipSquare_le
    {Ω : Type*} {u : Ω → ℝ} (n : ℕ) (ω : Ω) :
    entropyClipSquare u n ω ≤ u ω ^ 2 := by
  have hcap : 0 ≤ (n : ℝ) + 1 := by positivity
  have hclip := clipValue_abs_le_abs_local (A := (n : ℝ) + 1) (x := u ω) hcap
  have hsq : |clipValue ((n : ℝ) + 1) (u ω)| ^ 2 ≤ |u ω| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hclip)
      (add_nonneg (abs_nonneg (clipValue ((n : ℝ) + 1) (u ω)))
        (abs_nonneg (u ω)))]
  simpa only [entropyClipSquare, sq_abs] using hsq

private theorem entropyClipSquare_pointwise_tendsto
    {Ω : Type*} {u : Ω → ℝ} (ω : Ω) :
    Tendsto (fun n : ℕ => entropyClipSquare u n ω) atTop (𝓝 (u ω ^ 2)) := by
  have hclip := clipValue_sequence_tendsto_local (u ω)
  have hsq := (continuous_pow 2).continuousAt.tendsto.comp hclip
  change Tendsto ((fun x : ℝ => x ^ 2) ∘
    (fun n : ℕ => clipValue ((n : ℝ) + 1) (u ω))) atTop (𝓝 (u ω ^ 2))
  exact hsq

private theorem entropyClipSquare_mass_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} (hu : Measurable u)
    (hu2 : Integrable (fun ω => u ω ^ 2) μ) :
    Tendsto (fun n : ℕ => ∫ ω, entropyClipSquare u n ω ∂μ) atTop
      (𝓝 (∫ ω, u ω ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (bound := fun ω => u ω ^ 2)
  · intro n
    have hclip : Measurable (fun ω => clipValue ((n : ℝ) + 1) (u ω)) :=
      (continuous_clipValue_local _).measurable.comp hu
    exact (hclip.pow_const 2).aestronglyMeasurable
  · exact hu2
  · intro n
    filter_upwards with ω
    change ‖(clipValue ((n : ℝ) + 1) (u ω)) ^ 2‖ ≤ u ω ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact entropyClipSquare_le n ω
  · filter_upwards [] with ω
    exact entropyClipSquare_pointwise_tendsto ω

private theorem entropyClipSquare_mass_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} (hu : Measurable u)
    (hu2 : Integrable (fun ω => u ω ^ 2) μ) (n : ℕ) :
    0 ≤ ∫ ω, entropyClipSquare u n ω ∂μ ∧
      (∫ ω, entropyClipSquare u n ω ∂μ) ≤ ∫ ω, u ω ^ 2 ∂μ := by
  constructor
  · exact integral_nonneg fun ω => sq_nonneg _
  · exact integral_mono_ae (integrable_entropyClipSquare hu n) hu2
      (ae_of_all μ (entropyClipSquare_le n))

private theorem shiftedClipFatou
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hfmeas : ∀ n, Measurable (fun ω => shiftedMulLogKernel (f n ω)))
    (hpoint : ∀ ω, Tendsto (fun n => shiftedMulLogKernel (f n ω)) atTop
      (𝓝 (shiftedMulLogKernel (F ω)))) :
    ∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (F ω)) ∂μ ≤
      atTop.liminf (fun n => ∫⁻ ω,
        ENNReal.ofReal (shiftedMulLogKernel (f n ω)) ∂μ) := by
  have hfatou : ∫⁻ ω, atTop.liminf
      (fun n => ENNReal.ofReal (shiftedMulLogKernel (f n ω))) ∂μ ≤
      atTop.liminf (fun n => ∫⁻ ω,
        ENNReal.ofReal (shiftedMulLogKernel (f n ω)) ∂μ) := by
    apply lintegral_liminf_le'
    intro n
    exact (ENNReal.continuous_ofReal.measurable.comp (hfmeas n)).aemeasurable
  calc
    ∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (F ω)) ∂μ =
        ∫⁻ ω, atTop.liminf
          (fun n => ENNReal.ofReal (shiftedMulLogKernel (f n ω))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hpoint ω)).liminf_eq.symm
    _ ≤ atTop.liminf (fun n => ∫⁻ ω,
        ENNReal.ofReal (shiftedMulLogKernel (f n ω)) ∂μ) := hfatou

private theorem integral_shiftedMulLogKernel
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable (fun ω => mulLogKernel (f ω)) μ) :
    (∫ ω, shiftedMulLogKernel (f ω) ∂μ) =
      (∫ ω, mulLogKernel (f ω) ∂μ) + Real.exp (-1) := by
  calc
    (∫ ω, shiftedMulLogKernel (f ω) ∂μ) =
        ∫ ω, mulLogKernel (f ω) + Real.exp (-1) ∂μ := by
      simp only [shiftedMulLogKernel]
    _ = (∫ ω, mulLogKernel (f ω) ∂μ) +
        ∫ ω, Real.exp (-1) ∂μ := integral_add hf (integrable_const _)
    _ = (∫ ω, mulLogKernel (f ω) ∂μ) + Real.exp (-1) := by
      simp [integral_const]

/--
Uniform entropy control of the literal clipped squares admits the actual
square and its entropy. The premise `hu2` is supplied by the separate square
admission route; this theorem only performs the shifted-Fatou passage.
-/
theorem integrable_mulLogKernel_of_uniform_entropyClip_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} (hu : Measurable u)
    (hu2 : Integrable (fun ω => u ω ^ 2) μ) (K : ℝ)
    (hclipEntropy : ∀ n, looconcentrationEntropy μ (entropyClipSquare u n) ≤ K) :
    Integrable (fun ω => (u ω ^ 2) * Real.log (u ω ^ 2)) μ ∧
      looconcentrationEntropy μ (fun ω => u ω ^ 2) ≤ K := by
  let mass : ℕ → ℝ := fun n => ∫ ω, entropyClipSquare u n ω ∂μ
  let massLimit : ℝ := ∫ ω, u ω ^ 2 ∂μ
  have hmassTendsto : Tendsto mass atTop (𝓝 massLimit) := by
    simpa [mass, massLimit] using entropyClipSquare_mass_tendsto hu hu2
  have hmassNonneg (n : ℕ) : 0 ≤ mass n := by
    simpa [mass] using
      (entropyClipSquare_mass_bounds hu hu2 n).1
  have hmassLe (n : ℕ) : mass n ≤ massLimit := by
    simpa [mass, massLimit] using
      (entropyClipSquare_mass_bounds hu hu2 n).2
  have hmassLogTendsto :
      Tendsto (fun n => mulLogKernel (mass n)) atTop
        (𝓝 (mulLogKernel massLimit)) := by
    exact Real.continuous_mul_log.continuousAt.tendsto.comp hmassTendsto
  let upper : ℕ → ℝ := fun n => K + mulLogKernel (mass n) + Real.exp (-1)
  let upperLimit : ℝ := K + mulLogKernel massLimit + Real.exp (-1)
  have hupperTendsto : Tendsto upper atTop (𝓝 upperLimit) := by
    simpa [upper, upperLimit] using
      (tendsto_const_nhds.add hmassLogTendsto).add tendsto_const_nhds
  have hclipLogIntegrable (n : ℕ) :
      Integrable (fun ω => mulLogKernel (entropyClipSquare u n ω)) μ :=
    integrable_mulLog_entropyClipSquare hu n
  have hclipShiftIntegrable (n : ℕ) :
      Integrable (fun ω => shiftedMulLogKernel (entropyClipSquare u n ω)) μ := by
    simpa [shiftedMulLogKernel] using
      (hclipLogIntegrable n).add (integrable_const (Real.exp (-1)))
  have hclipShiftIntegral (n : ℕ) :
      (∫ ω, shiftedMulLogKernel (entropyClipSquare u n ω) ∂μ) =
        (∫ ω, mulLogKernel (entropyClipSquare u n ω) ∂μ) + Real.exp (-1) := by
    exact integral_shiftedMulLogKernel (hclipLogIntegrable n)
  have hclipEntropy' (n : ℕ) :
      (∫ ω, mulLogKernel (entropyClipSquare u n ω) ∂μ) -
        mass n * Real.log (mass n) ≤ K := by
    simpa [looconcentrationEntropy, mulLogKernel, mass] using hclipEntropy n
  have hclipShiftNonneg (n : ℕ) (ω : Ω) :
      0 ≤ shiftedMulLogKernel (entropyClipSquare u n ω) :=
    mulLogKernel_lower_shift _ (sq_nonneg _)
  have hupperBound (n : ℕ) :
      (∫ ω, shiftedMulLogKernel (entropyClipSquare u n ω) ∂μ) ≤ upper n := by
    rw [hclipShiftIntegral n]
    dsimp [upper]
    have hmassTerm : mass n * Real.log (mass n) = mulLogKernel (mass n) := by
      rfl
    rw [← hmassTerm]
    linarith [hclipEntropy' n]
  have hupperNonneg (n : ℕ) : 0 ≤ upper n := by
    have hIntNonneg :
        0 ≤ ∫ ω, shiftedMulLogKernel (entropyClipSquare u n ω) ∂μ :=
      integral_nonneg (hclipShiftNonneg n)
    exact hIntNonneg.trans (hupperBound n)
  have hupperLimitNonneg : 0 ≤ upperLimit :=
    ge_of_tendsto' hupperTendsto hupperNonneg
  have hshiftMeas :
      Measurable (fun ω => shiftedMulLogKernel (u ω ^ 2)) := by
    have hsquare : Measurable (fun ω => u ω ^ 2) := hu.pow_const 2
    exact (Real.continuous_mul_log.add continuous_const).measurable.comp hsquare
  have hclipShiftMeas (n : ℕ) :
      Measurable (fun ω => shiftedMulLogKernel (entropyClipSquare u n ω)) := by
    have hsquare : Measurable (entropyClipSquare u n) := by
      exact ((continuous_clipValue_local _).measurable.comp hu).pow_const 2
    exact (Real.continuous_mul_log.add continuous_const).measurable.comp hsquare
  have hshiftPoint (ω : Ω) :
      Tendsto (fun n => shiftedMulLogKernel (entropyClipSquare u n ω)) atTop
        (𝓝 (shiftedMulLogKernel (u ω ^ 2))) := by
    exact (Real.continuous_mul_log.add continuous_const).continuousAt.tendsto.comp
      (entropyClipSquare_pointwise_tendsto ω)
  have hfatou :
      (∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (u ω ^ 2)) ∂μ) ≤
        atTop.liminf (fun n =>
          ∫⁻ ω, ENNReal.ofReal
            (shiftedMulLogKernel (entropyClipSquare u n ω)) ∂μ) := by
    exact shiftedClipFatou hclipShiftMeas hshiftPoint
  have hclipLintegralBound (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal
        (shiftedMulLogKernel (entropyClipSquare u n ω)) ∂μ) ≤
          ENNReal.ofReal (upper n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hclipShiftIntegrable n)
      (ae_of_all μ (hclipShiftNonneg n))]
    exact ENNReal.ofReal_le_ofReal (hupperBound n)
  have hliminfBound :
      atTop.liminf (fun n =>
        ∫⁻ ω, ENNReal.ofReal
          (shiftedMulLogKernel (entropyClipSquare u n ω)) ∂μ) ≤
          atTop.liminf (fun n => ENNReal.ofReal (upper n)) := by
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hclipLintegralBound)
  have hupperENNRTendsto :
      Tendsto (fun n => ENNReal.ofReal (upper n)) atTop
        (𝓝 (ENNReal.ofReal upperLimit)) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hupperTendsto
  have hupperLiminf :
      atTop.liminf (fun n => ENNReal.ofReal (upper n)) =
        ENNReal.ofReal upperLimit := hupperENNRTendsto.liminf_eq
  have hactualLintegralFinite :
      (∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (u ω ^ 2)) ∂μ) < ∞ := by
    have hbound :
        (∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (u ω ^ 2)) ∂μ) ≤
          ENNReal.ofReal upperLimit := by
      exact hfatou.trans (hliminfBound.trans_eq hupperLiminf)
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hshiftNonneg : ∀ ω, 0 ≤ shiftedMulLogKernel (u ω ^ 2) := by
    intro ω
    exact mulLogKernel_lower_shift _ (sq_nonneg _)
  have hshiftIntegrable :
      Integrable (fun ω => shiftedMulLogKernel (u ω ^ 2)) μ := by
    refine ⟨hshiftMeas.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all μ hshiftNonneg)).2
      hactualLintegralFinite
  have hlogIntegrable : Integrable (fun ω => mulLogKernel (u ω ^ 2)) μ := by
    have hsub := hshiftIntegrable.sub (integrable_const (Real.exp (-1)))
    have hfun : (fun ω => mulLogKernel (u ω ^ 2)) =
        (fun ω => shiftedMulLogKernel (u ω ^ 2)) -
          (fun _ : Ω => Real.exp (-1)) := by
      funext ω
      simp [shiftedMulLogKernel]
    rw [hfun]
    exact hsub
  have hactualShiftIntegral :
      ENNReal.ofReal (∫ ω, shiftedMulLogKernel (u ω ^ 2) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (shiftedMulLogKernel (u ω ^ 2)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hshiftIntegrable
      (ae_of_all μ hshiftNonneg)
  have hactualRealBound :
      (∫ ω, shiftedMulLogKernel (u ω ^ 2) ∂μ) ≤ upperLimit := by
    apply (ENNReal.ofReal_le_ofReal_iff hupperLimitNonneg).mp
    rw [hactualShiftIntegral]
    exact hfatou.trans (hliminfBound.trans_eq hupperLiminf)
  have hactualShiftIntegralEq :
      (∫ ω, shiftedMulLogKernel (u ω ^ 2) ∂μ) =
        (∫ ω, mulLogKernel (u ω ^ 2) ∂μ) + Real.exp (-1) :=
    integral_shiftedMulLogKernel hlogIntegrable
  have hactualLogIntegrable :
      Integrable (fun ω => (u ω ^ 2) * Real.log (u ω ^ 2)) μ := by
    simpa only [mulLogKernel] using hlogIntegrable
  constructor
  · exact hactualLogIntegrable
  · unfold looconcentrationEntropy
    rw [hactualShiftIntegralEq] at hactualRealBound
    dsimp [upperLimit, massLimit, mulLogKernel] at hactualRealBound
    linarith

end LOOConcentration
