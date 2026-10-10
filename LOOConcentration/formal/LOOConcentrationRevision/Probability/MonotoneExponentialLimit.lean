import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Whole-integral monotone convergence and bounded exponential caps

The first result is the extended-integral monotone convergence theorem in a
form that keeps the limit function internally produced by the pointwise
convergence premise. The second result applies it to the actual scalar caps
`(j+1) * (1 - exp (-X/(j+1)))`.

Source: the revised manuscript, lines 1053--1060; the MCT is the standard
external result used in the actual norm-cap limit passage.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LOOConcentration.Revision

noncomputable section

/-- Whole extended-integral monotone convergence, with measurable
approximants and their pointwise limit supplied by their actual limit. -/
theorem source_monotone_lintegral_eq_iSup
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ≥0∞) (F : α → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hmono : Monotone f)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (F x))) :
    (∫⁻ x, F x ∂μ) = ⨆ j, ∫⁻ x, f j x ∂μ := by
  have hpoint : (fun x => ⨆ j, f j x) = F := by
    funext x
    apply iSup_eq_of_tendsto (fun i j hij => hmono hij x)
    exact hlim x
  calc
    (∫⁻ x, F x ∂μ) = ∫⁻ x, ⨆ j, f j x ∂μ := by
      exact congrArg (fun G : α → ℝ≥0∞ => ∫⁻ x, G x ∂μ) hpoint.symm
    _ = ⨆ j, ∫⁻ x, f j x ∂μ := lintegral_iSup hf hmono

private def capScalar (A t : ℝ) : ℝ :=
  A * (1 - Real.exp (-(t / A)))

private theorem capScalar_lower {A t : ℝ} (hA : 0 < A) :
    t * Real.exp (-(t / A)) ≤ capScalar A t := by
  have he : 1 + t / A ≤ Real.exp (t / A) := by
    simpa [add_comm] using Real.add_one_le_exp (t / A)
  have hprod : (1 + t / A) * Real.exp (-t / A) ≤ 1 := by
    calc
      (1 + t / A) * Real.exp (-t / A) ≤
          Real.exp (t / A) * Real.exp (-t / A) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        have hz : t / A + -t / A = 0 := by ring
        rw [hz, Real.exp_zero]
  have hprod' : (1 + t / A) * Real.exp (-(t / A)) ≤ 1 := by
    simpa only [neg_div] using hprod
  have hquot : (t / A) * Real.exp (-(t / A)) ≤
      1 - Real.exp (-(t / A)) := by nlinarith [hprod']
  unfold capScalar
  calc
    t * Real.exp (-(t / A)) = A * ((t / A) * Real.exp (-(t / A))) := by
      field_simp [hA.ne']
    _ ≤ A * (1 - Real.exp (-(t / A))) :=
      mul_le_mul_of_nonneg_left hquot hA.le

private theorem capScalar_le_argument {A t : ℝ} (hA : 0 < A) :
    capScalar A t ≤ t := by
  have hExp : 1 - Real.exp (-(t / A)) ≤ t / A := by
    have h := Real.add_one_le_exp (-(t / A))
    linarith
  unfold capScalar
  calc
    A * (1 - Real.exp (-(t / A))) ≤ A * (t / A) :=
      mul_le_mul_of_nonneg_left hExp hA.le
    _ = t := by field_simp [hA.ne']

private theorem capScalar_le_cap {A t : ℝ} (hA : 0 < A) :
    capScalar A t ≤ A := by
  unfold capScalar
  have h : 1 - Real.exp (-(t / A)) ≤ 1 := by
    linarith [Real.exp_nonneg (-(t / A))]
  calc
    A * (1 - Real.exp (-(t / A))) ≤ A * 1 :=
      mul_le_mul_of_nonneg_left h hA.le
    _ = A := by ring

private theorem capScalar_nonneg {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    0 ≤ capScalar A t := by
  unfold capScalar
  have harg : -(t / A) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg ht hA.le)
  have hExp : Real.exp (-(t / A)) ≤ 1 := Real.exp_le_one_iff.mpr harg
  exact mul_nonneg hA.le (by linarith)

private theorem capScalar_mono {t A B : ℝ} (ht : 0 ≤ t)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    capScalar A t ≤ capScalar B t := by
  let x := t / A
  let y := t / B
  let z := x - y
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hxy : x = y + z := by dsimp [z]; ring
  have hzEq : z = t * (B - A) / (A * B) := by
    dsimp [x, y, z]
    field_simp [hA.ne', hB.ne']
  have hz : 0 ≤ z := by
    rw [hzEq]
    positivity
  have hAz : A * z = (B - A) * y := by
    dsimp [y, z, x]
    field_simp [hA.ne', hB.ne']
  have hy : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by
    have he : 1 + y ≤ Real.exp y := by
      simpa [add_comm] using Real.add_one_le_exp y
    have hprod : (1 + y) * Real.exp (-y) ≤ 1 := by
      calc
        (1 + y) * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [hprod]
  have hzle : 1 - Real.exp (-z) ≤ z := by
    have h := Real.add_one_le_exp (-z)
    nlinarith
  have hePos : 0 ≤ Real.exp (-y) := Real.exp_nonneg _
  have hcompare : A * Real.exp (-y) * (1 - Real.exp (-z)) ≤
      (B - A) * (1 - Real.exp (-y)) := by
    calc
      A * Real.exp (-y) * (1 - Real.exp (-z)) ≤
          A * Real.exp (-y) * z :=
        mul_le_mul_of_nonneg_left hzle (mul_nonneg hA.le hePos)
      _ = (B - A) * (y * Real.exp (-y)) := by
        calc
          A * Real.exp (-y) * z = Real.exp (-y) * (A * z) := by ring
          _ = Real.exp (-y) * ((B - A) * y) := by rw [hAz]
          _ = (B - A) * (y * Real.exp (-y)) := by ring
      _ ≤ (B - A) * (1 - Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left hy hBA
  have hdiff : capScalar B t - capScalar A t =
      (B - A) * (1 - Real.exp (-y)) -
        A * Real.exp (-y) * (1 - Real.exp (-z)) := by
    unfold capScalar
    rw [show t / B = y by rfl, show t / A = x by rfl]
    rw [hxy, neg_add, Real.exp_add]
    ring
  rw [← sub_nonneg, hdiff]
  exact sub_nonneg.mpr hcompare

private theorem capScalarSequence_tendsto {t : ℝ} :
    Tendsto (fun j : ℕ => capScalar ((j + 1 : ℕ) : ℝ) t)
      atTop (𝓝 t) := by
  have hsmall : Tendsto (fun j : ℕ => t / ((j + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat t).comp
      (tendsto_add_atTop_nat 1)
  have hexp : Tendsto
      (fun j : ℕ => Real.exp (-(t / ((j + 1 : ℕ) : ℝ)))) atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘ fun j : ℕ => -(t / ((j + 1 : ℕ) : ℝ)))
      atTop (𝓝 1)
    simpa only [neg_zero, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp hsmall.neg)
  have hlow : Tendsto
      (fun j : ℕ => t * Real.exp (-(t / ((j + 1 : ℕ) : ℝ))))
      atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.mul hexp
  have hhigh : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh
  · intro j
    have hA : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have h := capScalar_lower (t := t) hA
    simpa [capScalar, neg_div] using h
  · intro j
    have hA : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    exact capScalar_le_argument hA

private theorem actualBoundedCapExpInt
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : α → ℝ) (hX : Measurable X)
    (s : ℝ) (hs : 0 ≤ s) (j : ℕ) :
    Integrable (fun x => Real.exp
      (s * capScalar ((j + 1 : ℕ) : ℝ) (X x))) μ := by
  let A : ℝ := ((j + 1 : ℕ) : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hQmeas : Measurable (fun x => capScalar A (X x)) := by
    dsimp [capScalar]
    exact ((measurable_const : Measurable (fun _ : α => (1 : ℝ))).sub
      (Real.measurable_exp.comp ((hX.div_const A).neg))).const_mul A
  have hExpMeas : Measurable (fun x => Real.exp (s * capScalar A (X x))) :=
    Real.measurable_exp.comp (measurable_const.mul hQmeas)
  have hQle : ∀ x, capScalar A (X x) ≤ A :=
    fun x => capScalar_le_cap hA
  apply Integrable.mono' (integrable_const (Real.exp (s * A)))
    hExpMeas.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hQle x) hs)

/-- Uniform bounds on the actual capped exponential integrals imply
integrability and the same bound for the exponential of the limit. The cap
integrability, measurability of the limit, and the whole extended-integral
passage are derived in the proof. -/
theorem actual_cap_exponential_limit
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : α → ℝ) (hX : Measurable X)
    (hXnn : ∀ x, 0 ≤ X x) (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hcap : ∀ j : ℕ,
      (∫ x, Real.exp (s * (((j + 1 : ℕ) : ℝ) *
        (1 - Real.exp (-X x / ((j + 1 : ℕ) : ℝ))))) ∂μ) ≤ K) :
    Integrable (fun x => Real.exp (s * X x)) μ ∧
      (∫ x, Real.exp (s * X x) ∂μ) ≤ K := by
  let q : ℕ → α → ℝ := fun j x =>
    capScalar ((j + 1 : ℕ) : ℝ) (X x)
  let f : ℕ → α → ℝ≥0∞ := fun j x => ENNReal.ofReal (Real.exp (s * q j x))
  let F : α → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (s * X x))
  have hqmeas : ∀ j, Measurable (q j) := by
    intro j
    dsimp [q, capScalar]
    exact ((measurable_const : Measurable (fun _ : α => (1 : ℝ))).sub
      (Real.measurable_exp.comp ((hX.div_const _).neg))).const_mul _
  have hfmeas : ∀ j, Measurable (f j) := by
    intro j
    dsimp [f]
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (hqmeas j)))
  have hqmono : Monotone q := by
    intro i j hij x
    have hAi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    have hAj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have hAij : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hij 1
    exact capScalar_mono (hXnn x) hAi hAj hAij
  have hfmono : Monotone f := by
    intro i j hij x
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hqmono hij x) hs
  have hqpoint : ∀ x, Tendsto (fun j => q j x) atTop (𝓝 (X x)) := by
    intro x
    simpa [q] using capScalarSequence_tendsto (t := X x)
  have hflim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (F x)) := by
    intro x
    have hscaled : Tendsto (fun j => s * q j x) atTop (𝓝 (s * X x)) :=
      tendsto_const_nhds.mul (hqpoint x)
    have hexp : Tendsto (fun j => Real.exp (s * q j x)) atTop
        (𝓝 (Real.exp (s * X x))) :=
      (Real.continuous_exp.tendsto _).comp hscaled
    change Tendsto (fun j => ENNReal.ofReal (Real.exp (s * q j x)))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (s * X x))))
    exact ENNReal.tendsto_ofReal hexp
  have hwholeMCT := source_monotone_lintegral_eq_iSup μ f F hfmeas hfmono hflim
  have hcapENN : ∀ j, (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal K := by
    intro j
    have hInt := actualBoundedCapExpInt μ X hX s hs j
    have hIntegral :
      (∫ x, Real.exp (s * q j x) ∂μ) ≤ K := by
      simpa [q, capScalar, neg_div] using hcap j
    have hEq := ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all μ (fun x => (Real.exp_pos _).le))
    rw [← hEq]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [q] using hIntegral)
  have hlimitENN : (∫⁻ x, F x ∂μ) ≤ ENNReal.ofReal K := by
    rw [hwholeMCT]
    exact iSup_le hcapENN
  have hExpMeas : Measurable (fun x => Real.exp (s * X x)) :=
    Real.measurable_exp.comp (measurable_const.mul hX)
  have hfinite : (∫⁻ x, ENNReal.ofReal (Real.exp (s * X x)) ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (by simpa [F] using hlimitENN) ENNReal.ofReal_lt_top
  have hInt : Integrable (fun x => Real.exp (s * X x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hExpMeas.aestronglyMeasurable
      (ae_of_all μ (fun x => (Real.exp_pos _).le))).mp hfinite
  have hEq := ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all μ (fun x => (Real.exp_pos _).le))
  refine ⟨hInt, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hK).1
  simpa [F] using hEq.symm ▸ hlimitENN


/-- The actual nonnegative scalar caps have finite real expectations that
increase to the same raw mean. All cap integrability and pointwise facts are
produced internally; the only moment input is integrability of the limit. -/
theorem actual_cap_expectation_monotone_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (hX : Measurable X) (hXnn : ∀ x, 0 ≤ X x)
    (hInt : Integrable X μ) :
    Monotone (fun j : ℕ => ∫ x, ((j + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-X x / ((j + 1 : ℕ) : ℝ))) ∂μ) ∧
    Tendsto (fun j : ℕ => ∫ x, ((j + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-X x / ((j + 1 : ℕ) : ℝ))) ∂μ)
      atTop (𝓝 (∫ x, X x ∂μ)) := by
  let q : ℕ → α → ℝ := fun j x => capScalar ((j+1 : ℕ) : ℝ) (X x)
  have hqmeas (j : ℕ) : Measurable (q j) := by
    dsimp [q, capScalar]
    fun_prop
  have hqInt (j : ℕ) : Integrable (q j) μ := by
    apply hInt.mono' (hqmeas j).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (capScalar_nonneg (by positivity) (hXnn x))]
    exact capScalar_le_argument (by positivity)
  have hqmono : Monotone q := by
    intro i j hij x
    exact capScalar_mono (hXnn x) (by positivity) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hIntMono : Monotone (fun j => ∫ x, q j x ∂μ) := by
    intro i j hij
    exact integral_mono (hqInt i) (hqInt j) (fun x => hqmono hij x)
  have hlim : ∀ x, Tendsto (fun j => q j x) atTop (𝓝 (X x)) :=
    fun x => capScalarSequence_tendsto
  have hmeanlim := integral_tendsto_of_tendsto_of_monotone hqInt hInt
    (ae_of_all μ (fun x => fun i j hij => hqmono hij x)) (ae_of_all μ hlim)
  simpa only [q, capScalar, neg_div] using And.intro hIntMono hmeanlim

end

end LOOConcentration.Revision
