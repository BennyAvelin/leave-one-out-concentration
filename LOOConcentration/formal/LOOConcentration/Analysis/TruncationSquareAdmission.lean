import LOOConcentration.Analysis.ClipMollify
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open Topology
open scoped ENNReal

/-!
# Square-integrability admission from bounded truncations

This module isolates the uniform-variance predecessor used to admit a
measurable finite-valued function into the square-integrable class. The
truncations are the literal `clipFunction` from `ClipMollify`. The uniform
variance premise is intended to be supplied by an independently proved
bounded-test Poincare inequality.
-/

/-- The actual symmetric clip of `u` at radius `n + 1`. -/
def finiteEnergyTruncation {α : Type*} (u : α → ℝ) (n : ℕ) : α → ℝ :=
  clipFunction ((n : ℝ) + 1) u

/-- The real mean of an actual bounded truncation. -/
noncomputable def finiteEnergyTruncationMean {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : α → ℝ) (n : ℕ) : ℝ :=
  ∫ x, finiteEnergyTruncation u n x ∂μ

/-- The variance of an actual bounded truncation, written as its centered
second moment. -/
noncomputable def finiteEnergyTruncationVariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : α → ℝ) (n : ℕ) : ℝ :=
  ∫ x, (finiteEnergyTruncation u n x - finiteEnergyTruncationMean μ u n) ^ 2 ∂μ

/-- An anchor set on which the untruncated function is bounded. -/
def finiteEnergyAnchorSet {α : Type*} (u : α → ℝ) (M : ℕ) : Set α :=
  {x | |u x| ≤ (M : ℝ)}

private theorem integrable_of_measurable_abs_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {B : ℝ}
    (hf : Measurable f) (hbound : ∀ x, |f x| ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hbound x

theorem measurable_finiteEnergyTruncation {α : Type*} [MeasurableSpace α]
    {u : α → ℝ} (hu : Measurable u) (n : ℕ) :
    Measurable (finiteEnergyTruncation u n) := by
  unfold finiteEnergyTruncation clipFunction clipValue
  exact measurable_const.max (hu.min measurable_const)

theorem finiteEnergyTruncation_abs_le {α : Type*} {u : α → ℝ} (n : ℕ) (x : α) :
    |finiteEnergyTruncation u n x| ≤ (n : ℝ) + 1 := by
  unfold finiteEnergyTruncation clipFunction
  have hb := clipValue_bounds (N := (n : ℝ) + 1) (u := u x) (by positivity)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem clipFunction_eq_self_of_abs_le {α : Type*} {u : α → ℝ}
    {A : ℝ} {x : α} (hA : |u x| ≤ A) : clipFunction A u x = u x := by
  unfold clipFunction clipValue
  rw [min_eq_left (abs_le.mp hA).2, max_eq_right (abs_le.mp hA).1]

theorem integrable_finiteEnergyTruncation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (n : ℕ) : Integrable (finiteEnergyTruncation u n) μ := by
  apply integrable_of_measurable_abs_le
    (B := (n : ℝ) + 1) (measurable_finiteEnergyTruncation hu n)
  exact finiteEnergyTruncation_abs_le n

theorem integrable_finiteEnergyTruncation_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (n : ℕ) : Integrable (fun x => finiteEnergyTruncation u n x ^ 2) μ := by
  let A : ℝ := (n : ℝ) + 1
  apply integrable_of_measurable_abs_le
    (B := A ^ 2) ((measurable_finiteEnergyTruncation hu n).pow_const 2)
  intro x
  have hclip := finiteEnergyTruncation_abs_le (u := u) n x
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hclip' : |finiteEnergyTruncation u n x| ≤ A := by simpa [A] using hclip
  rw [abs_of_nonneg (sq_nonneg _)]
  rw [← sq_abs (finiteEnergyTruncation u n x)]
  have hprod := mul_nonneg (sub_nonneg.mpr hclip')
    (add_nonneg hA (abs_nonneg (finiteEnergyTruncation u n x)))
  nlinarith

private theorem integrable_finiteEnergyCenteredTruncation_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (n : ℕ) :
    Integrable
      (fun x => (finiteEnergyTruncation u n x -
        finiteEnergyTruncationMean μ u n) ^ 2) μ := by
  let A : ℝ := (n : ℝ) + 1
  let m := finiteEnergyTruncationMean μ u n
  have hmeas : Measurable (fun x =>
      (finiteEnergyTruncation u n x - m) ^ 2) := by
    exact ((measurable_finiteEnergyTruncation hu n).sub measurable_const).pow_const 2
  apply integrable_of_measurable_abs_le (B := (A + |m|) ^ 2) hmeas
  intro x
  have hclip := finiteEnergyTruncation_abs_le (u := u) n x
  have hdev : |finiteEnergyTruncation u n x - m| ≤ A + |m| := by
    calc
      |finiteEnergyTruncation u n x - m| ≤
          |finiteEnergyTruncation u n x| + |m| := abs_sub _ _
      _ ≤ A + |m| := by simpa [A] using add_le_add_right hclip |m|
  rw [abs_of_nonneg (sq_nonneg _)]
  rw [← sq_abs (finiteEnergyTruncation u n x - m)]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hdev)
    (add_nonneg (add_nonneg hA (abs_nonneg m))
      (abs_nonneg (finiteEnergyTruncation u n x - m)))
  nlinarith

private theorem finiteEnergyTruncationVariance_eq_secondMoment_sub_mean_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (n : ℕ) :
    finiteEnergyTruncationVariance μ u n =
      (∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ) -
        (finiteEnergyTruncationMean μ u n) ^ 2 := by
  let v := finiteEnergyTruncation u n
  let m := finiteEnergyTruncationMean μ u n
  have hv : Integrable v μ := by
    simpa [v] using integrable_finiteEnergyTruncation μ hu n
  have hv2 : Integrable (fun x => v x ^ 2) μ := by
    simpa [v] using integrable_finiteEnergyTruncation_sq μ hu n
  have hpoly : (fun x => (v x - m) ^ 2) =
      fun x => v x ^ 2 - (2 * m) * v x + m ^ 2 := by
    funext x
    ring
  have hmid : Integrable (fun x => v x ^ 2 - (2 * m) * v x) μ :=
    hv2.sub (hv.const_mul (2 * m))
  rw [finiteEnergyTruncationVariance]
  calc
    (∫ x, (v x - m) ^ 2 ∂μ) =
        ∫ x, (v x ^ 2 - (2 * m) * v x + m ^ 2) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          exact congrFun hpoly x
    _ = (∫ x, v x ^ 2 - (2 * m) * v x ∂μ) + ∫ x, m ^ 2 ∂μ :=
          integral_add hmid (integrable_const _)
    _ = ((∫ x, v x ^ 2 ∂μ) - ∫ x, (2 * m) * v x ∂μ) + ∫ x, m ^ 2 ∂μ := by
          rw [integral_sub hv2 (hv.const_mul _)]
    _ = (∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ) - m ^ 2 := by
          rw [integral_const_mul, integral_const]
          simp [v, m, finiteEnergyTruncationMean, Measure.real, measure_univ]
          ring

theorem measurableSet_finiteEnergyAnchorSet {α : Type*} [MeasurableSpace α]
    {u : α → ℝ} (hu : Measurable u) (M : ℕ) :
    MeasurableSet (finiteEnergyAnchorSet u M) := by
  have habs : Measurable (fun x => |u x|) := by
    have hEq : (fun x => |u x|) = (fun x => max (u x) (-u x)) := by
      funext x
      exact abs_eq_max_neg
    rw [hEq]
    exact hu.max hu.neg
  exact measurableSet_le habs measurable_const

/-- Every measurable finite real function has a measurable bounded anchor of
positive probability. -/
theorem exists_finiteEnergyAnchorSet_pos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (u : α → ℝ) :
    ∃ M : ℕ, 0 < μ.real (finiteEnergyAnchorSet u M) := by
  have hcover : (⋃ M : ℕ, finiteEnergyAnchorSet u M) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨M, hM⟩ := exists_nat_gt (|u x|)
      refine Set.mem_iUnion.mpr ⟨M, ?_⟩
      dsimp [finiteEnergyAnchorSet]
      exact le_of_lt hM
  have hmass : μ (⋃ M : ℕ, finiteEnergyAnchorSet u M) ≠ 0 := by
    rw [hcover, measure_univ]
    norm_num
  obtain ⟨M, hM⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  have hfinite : μ (finiteEnergyAnchorSet u M) ≠ ∞ := measure_ne_top μ _
  exact ⟨M, ENNReal.toReal_pos hM.ne' hfinite⟩

private theorem finiteEnergyTruncationMean_abs_le_of_anchor
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (M n : ℕ)
    (hanchor : 0 < μ.real (finiteEnergyAnchorSet u M))
    (hlevel : (M : ℝ) ≤ (n : ℝ) + 1)
    {V : ℝ}
    (hvariance : finiteEnergyTruncationVariance μ u n ≤ V) :
    |finiteEnergyTruncationMean μ u n| ≤
      (M : ℝ) + Real.sqrt (V / μ.real (finiteEnergyAnchorSet u M)) := by
  let v := finiteEnergyTruncation u n
  let m := finiteEnergyTruncationMean μ u n
  let K := finiteEnergyAnchorSet u M
  let αmass := μ.real K
  let g := K.indicator (1 : α → ℝ)
  have hKmeas : MeasurableSet K := by
    exact measurableSet_finiteEnergyAnchorSet hu M
  have hα : 0 < αmass := by simpa [αmass, K] using hanchor
  have hv : Integrable v μ := by simpa [v] using integrable_finiteEnergyTruncation μ hu n
  have hv2 : Integrable (fun x => v x ^ 2) μ := by
    simpa [v] using integrable_finiteEnergyTruncation_sq μ hu n
  have hdevSq : Integrable (fun x => (v x - m) ^ 2) μ := by
    simpa [v, m] using integrable_finiteEnergyCenteredTruncation_sq μ hu n
  have hdevMeas : Measurable (fun x => |v x - m|) := by
    have hsub : Measurable (fun x => v x - m) :=
      (measurable_finiteEnergyTruncation hu n).sub measurable_const
    have hEq : (fun x => |v x - m|) = (fun x => max (v x - m) (-(v x - m))) := by
      funext x
      exact abs_eq_max_neg
    rw [hEq]
    exact hsub.max hsub.neg
  have hdevLp : MemLp (fun x => |v x - m|) 2 μ := by
    apply (memLp_two_iff_integrable_sq hdevMeas.aestronglyMeasurable).2
    convert hdevSq using 1
    ext x
    simp [sq_abs]
  have hgMeas : Measurable g := measurable_const.indicator hKmeas
  have hgInt : Integrable g μ := by
    apply integrable_of_measurable_abs_le (B := 1) hgMeas
    intro x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hgSq : (fun x => g x ^ 2) = g := by
    funext x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hgLp : MemLp g 2 μ := by
    apply (memLp_two_iff_integrable_sq hgMeas.aestronglyMeasurable).2
    rw [hgSq]
    exact hgInt
  have hprodInt : Integrable (fun x => |v x - m| * g x) μ :=
    hdevLp.integrable_mul hgLp
  have hgNonneg : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hcsReal := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all μ fun x => abs_nonneg (v x - m))
    (ae_of_all μ hgNonneg)
    (by simpa using hdevLp) (by simpa using hgLp)
  have hcs : ∫ x, |v x - m| * g x ∂μ ≤
      (∫ x, |v x - m| ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    convert hcsReal using 1
    all_goals norm_num [Real.rpow_natCast]
  have hvariance' : ∫ x, (v x - m) ^ 2 ∂μ ≤ V := by
    simpa [v, m, finiteEnergyTruncationVariance] using hvariance
  have hdevIntegral : ∫ x, |v x - m| ^ 2 ∂μ =
      ∫ x, (v x - m) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [sq_abs]
  have hgIntegral : ∫ x, g x ^ 2 ∂μ = αmass := by
    rw [hgSq]
    simpa [g, αmass] using (integral_indicator_one (s := K) hKmeas)
  have hcs' : ∫ x, |v x - m| * g x ∂μ ≤
      Real.sqrt V * Real.sqrt αmass := by
    calc
      ∫ x, |v x - m| * g x ∂μ ≤
          (∫ x, |v x - m| ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hcs
      _ = (∫ x, (v x - m) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * αmass ^ (1 / 2 : ℝ) := by
        have hleft := congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) hdevIntegral
        have hright := congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) hgIntegral
        calc
          _ = (∫ x, (v x - m) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
              (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
                congrArg (fun z : ℝ => z * (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) hleft
          _ = _ :=
                congrArg (fun z : ℝ => (∫ x, (v x - m) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * z) hright
      _ ≤ Real.sqrt V * Real.sqrt αmass := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        exact mul_le_mul
          (Real.sqrt_le_sqrt hvariance') le_rfl
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmeanPoint : ∀ x,
      |m| * g x ≤ (M : ℝ) * g x + |v x - m| * g x := by
    intro x
    by_cases hx : x ∈ K
    · have huBound : |u x| ≤ (M : ℝ) := hx
      have hclipEq : v x = u x := by
        dsimp [v, finiteEnergyTruncation]
        exact clipFunction_eq_self_of_abs_le (huBound.trans hlevel)
      rw [hclipEq]
      simp [g, hx]
      have htriangle : |m| ≤ |u x| + |u x - m| := by
        calc
          |m| = |u x - (u x - m)| := by congr 1; ring
          _ ≤ |u x| + |u x - m| := abs_sub _ _
      nlinarith
    · simp [g, hx]
  have hleftInt : Integrable (fun x => |m| * g x) μ := hgInt.const_mul _
  have hfirstRightInt : Integrable (fun x => (M : ℝ) * g x) μ := hgInt.const_mul _
  have hsumInt : Integrable
      (fun x => (M : ℝ) * g x + |v x - m| * g x) μ :=
    hfirstRightInt.add hprodInt
  have hmono := integral_mono hleftInt hsumInt hmeanPoint
  have hleftEq : (∫ x, |m| * g x ∂μ) = |m| * αmass := by
    calc
      _ = |m| * ∫ x, g x ∂μ := integral_const_mul _ _
      _ = |m| * αmass := by
        have hKint : (∫ x, g x ∂μ) = αmass := by
          simpa [g, αmass] using (integral_indicator_one (s := K) hKmeas)
        rw [hKint]
  have hrightEq : (∫ x, (M : ℝ) * g x + |v x - m| * g x ∂μ) =
      (M : ℝ) * αmass + ∫ x, |v x - m| * g x ∂μ := by
    rw [integral_add hfirstRightInt hprodInt, integral_const_mul]
    have hKint : (∫ x, g x ∂μ) = αmass := by
      simpa [g, αmass] using (integral_indicator_one (s := K) hKmeas)
    rw [hKint]
  have hmeanIntegral : |m| * αmass ≤
      (M : ℝ) * αmass + Real.sqrt V * Real.sqrt αmass := by
    rw [hleftEq, hrightEq] at hmono
    exact hmono.trans (add_le_add_right hcs' ((M : ℝ) * αmass))
  have hmeanDiv : |m| ≤
      ((M : ℝ) * αmass + Real.sqrt V * Real.sqrt αmass) / αmass :=
    (le_div_iff₀ hα).2 hmeanIntegral
  have hroot : Real.sqrt αmass ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hsquareRoot : Real.sqrt αmass ^ 2 = αmass :=
    Real.sq_sqrt hα.le
  calc
    |m| ≤ ((M : ℝ) * αmass + Real.sqrt V * Real.sqrt αmass) / αmass := hmeanDiv
    _ = (M : ℝ) + Real.sqrt V / Real.sqrt αmass := by
      field_simp [hα.ne', hroot]
      linear_combination (Real.sqrt V) * hsquareRoot
    _ = (M : ℝ) + Real.sqrt (V / αmass) := by
      rw [Real.sqrt_div' V (le_of_lt hα)]

private theorem finiteEnergyTruncation_square_mass_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (M n : ℕ)
    (hanchor : 0 < μ.real (finiteEnergyAnchorSet u M))
    {V : ℝ} (hV : 0 ≤ V)
    (hvariance : ∀ j, finiteEnergyTruncationVariance μ u j ≤ V) :
    ∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ ≤
      V + ((M : ℝ) + Real.sqrt (V / μ.real (finiteEnergyAnchorSet u M))) ^ 2 := by
  let B : ℝ := (M : ℝ)
  by_cases hlarge : B ≤ (n : ℝ) + 1
  · have hm := finiteEnergyTruncationMean_abs_le_of_anchor μ hu M n hanchor hlarge
      (hvariance n)
    have hidentity := finiteEnergyTruncationVariance_eq_secondMoment_sub_mean_sq μ hu n
    have hvariance' :
        (∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ) -
            (finiteEnergyTruncationMean μ u n) ^ 2 ≤ V := by
      rw [← hidentity]
      exact hvariance n
    have hsecond :
        ∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ ≤
          V + (finiteEnergyTruncationMean μ u n) ^ 2 := by
      nlinarith
    calc
      _ ≤ V + |finiteEnergyTruncationMean μ u n| ^ 2 := by
        simpa only [sq_abs] using hsecond
      _ ≤ V + (B + Real.sqrt
          (V / μ.real (finiteEnergyAnchorSet u M))) ^ 2 := by
        have hmean' := hm
        have hroot : 0 ≤ Real.sqrt
            (V / μ.real (finiteEnergyAnchorSet u M)) := Real.sqrt_nonneg _
        have hright : 0 ≤ B + Real.sqrt
            (V / μ.real (finiteEnergyAnchorSet u M)) := by
          dsimp [B]
          positivity
        have hprod := mul_nonneg
          (sub_nonneg.mpr hmean')
          (add_nonneg hright (abs_nonneg (finiteEnergyTruncationMean μ u n)))
        nlinarith
      _ = _ := by dsimp [B]
  · have hsmall : (n : ℝ) + 1 < B := lt_of_not_ge hlarge
    have hclipSqBound : ∀ x, finiteEnergyTruncation u n x ^ 2 ≤ B ^ 2 := by
      intro x
      have hclip := finiteEnergyTruncation_abs_le (u := u) n x
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hclipB : |finiteEnergyTruncation u n x| ≤ B := le_trans hclip hsmall.le
      have hprod := mul_nonneg
        (sub_nonneg.mpr hclipB)
        (add_nonneg hB (abs_nonneg (finiteEnergyTruncation u n x)))
      rw [← sq_abs (finiteEnergyTruncation u n x)]
      nlinarith
    have hsq := integrable_finiteEnergyTruncation_sq μ hu n
    have hconst : Integrable (fun _ : α => B ^ 2) μ := integrable_const _
    have hmass :
        ∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ ≤ ∫ _ : α, B ^ 2 ∂μ :=
      integral_mono hsq hconst hclipSqBound
    have hprobInt : (∫ _ : α, B ^ 2 ∂μ) = B ^ 2 := by
      simp [Measure.real, measure_univ]
    have hrootNonneg : 0 ≤ Real.sqrt
        (V / μ.real (finiteEnergyAnchorSet u M)) := by positivity
    rw [hprobInt] at hmass
    have hbound : B ^ 2 ≤
        V + (B + Real.sqrt (V / μ.real (finiteEnergyAnchorSet u M))) ^ 2 := by
      nlinarith [hV, hrootNonneg]
    simpa [B] using hmass.trans hbound

/-- A genuine uniform variance bound for the actual symmetric clips admits a
measurable finite real function into `L²`. The variance premise is the only
conditional predecessor; all clipped means and square integrals are proved
internally. -/
theorem integrable_sq_of_uniform_finiteEnergyTruncationVariance
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : Measurable u) {V : ℝ} (hV : 0 ≤ V)
    (hvariance : ∀ n,
      finiteEnergyTruncationVariance μ u n ≤ V) :
    Integrable (fun x => u x ^ 2) μ := by
  obtain ⟨M, hanchor⟩ := exists_finiteEnergyAnchorSet_pos μ u
  let B : ℝ := V + ((M : ℝ) +
    Real.sqrt (V / μ.real (finiteEnergyAnchorSet u M))) ^ 2
  have hmass : ∀ n,
      ∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ ≤ B := by
    intro n
    simpa [B] using finiteEnergyTruncation_square_mass_le μ hu M n hanchor hV hvariance
  have hfatou : ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ ≤
      Filter.liminf (fun n =>
        ∫⁻ x, ENNReal.ofReal (finiteEnergyTruncation u n x ^ 2) ∂μ) atTop := by
    calc
      ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ =
          ∫⁻ x, Filter.liminf (fun n =>
            ENNReal.ofReal (finiteEnergyTruncation u n x ^ 2)) atTop ∂μ := by
        apply lintegral_congr
        intro x
        obtain ⟨N, hN⟩ := exists_nat_gt (|u x|)
        have hbound : |u x| ≤ (N : ℝ) := le_of_lt hN
        have hevent : ∀ᶠ n : ℕ in atTop,
            finiteEnergyTruncation u n x = u x := by
          filter_upwards [eventually_ge_atTop N] with n hn
          unfold finiteEnergyTruncation
          apply clipFunction_eq_self_of_abs_le
          have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        have heq : (fun n : ℕ =>
            ENNReal.ofReal (finiteEnergyTruncation u n x ^ 2)) =ᶠ[atTop]
            fun _ => ENNReal.ofReal (u x ^ 2) := by
          filter_upwards [hevent] with n hn
          rw [hn]
        have hlim : Tendsto
            (fun n => ENNReal.ofReal (finiteEnergyTruncation u n x ^ 2))
            atTop (𝓝 (ENNReal.ofReal (u x ^ 2))) :=
          tendsto_nhds_of_eventually_eq heq
        exact hlim.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n =>
        ENNReal.measurable_ofReal.comp
          ((measurable_finiteEnergyTruncation hu n).pow_const 2))
  have hclipLintegral_eq (n : ℕ) :
      ∫⁻ x, ENNReal.ofReal (finiteEnergyTruncation u n x ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, finiteEnergyTruncation u n x ^ 2 ∂μ) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_finiteEnergyTruncation_sq μ hu n)
      (ae_of_all μ fun x => sq_nonneg _)
  have hlintegral_bound : ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ ≤ ENNReal.ofReal B := by
    refine hfatou.trans ?_
    apply Filter.liminf_le_of_frequently_le'
    exact Frequently.of_forall fun n => by
      rw [hclipLintegral_eq]
      exact ENNReal.ofReal_le_ofReal (hmass n)
  have hnormBound : ∫⁻ x, ‖u x ^ 2‖ₑ ∂μ ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ := by
        apply lintegral_congr
        intro x
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ENNReal.ofReal B := hlintegral_bound
  have hfinite : ∫⁻ x, ‖u x ^ 2‖ₑ ∂μ < ∞ :=
    lt_of_le_of_lt hnormBound ENNReal.ofReal_lt_top
  refine ⟨(hu.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact hfinite

#print axioms integrable_finiteEnergyTruncation
#print axioms integrable_finiteEnergyTruncation_sq
#print axioms exists_finiteEnergyAnchorSet_pos
#print axioms integrable_sq_of_uniform_finiteEnergyTruncationVariance

end LOOConcentration
