import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory Set

/-! Helpers for the shifted-line route from an ambient a.e. gradient bound to
an all-pairs segment estimate.  The first lemma isolates only the one-
dimensional FTC calculation; its line derivative premise must be produced by
the separate translated-line/Fubini argument. -/

/-- An absolutely continuous restriction to a shifted segment obeys the
endpoint-average gradient-growth estimate, with the explicit translation
error `b * ‖z‖`. -/
theorem interval_abs_sub_le_shifted_segment_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (x y z : E) (a b : ℝ)
    (hac : AbsolutelyContinuousOnInterval g 0 1)
    (hb : 0 ≤ b)
    (hderiv : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      |deriv g t| ≤ ‖y - x‖ * (a + b * ‖(1 - t) • x + t • y + z‖)) :
    |g 1 - g 0| ≤
      ‖y - x‖ * (a + b / 2 * (‖x‖ + ‖y‖) + b * ‖z‖) := by
  let u : ℝ → ℝ := fun t =>
    ‖y - x‖ * (a + b * ((1 - t) * ‖x‖ + t * ‖y‖ + ‖z‖))
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(1 - t) • x + t • y + z‖ ≤
        (1 - t) * ‖x‖ + t * ‖y‖ + ‖z‖ := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := by linarith
    calc
      ‖(1 - t) • x + t • y + z‖
          ≤ ‖(1 - t) • x + t • y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖(1 - t) • x‖ + ‖t • y‖ + ‖z‖ := by
        nlinarith [norm_add_le ((1 - t) • x) (t • y)]
      _ = (1 - t) * ‖x‖ + t * ‖y‖ + ‖z‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1t, abs_of_nonneg ht0]
  have hderiv' : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      |deriv g t| ≤ u t := by
    filter_upwards [hderiv, ae_restrict_mem measurableSet_Icc] with t hdt ht
    calc
      |deriv g t| ≤ ‖y - x‖ * (a + b * ‖(1 - t) • x + t • y + z‖) := hdt
      _ ≤ u t := by
        dsimp [u]
        gcongr
        exact hpath t ht
  have hint : IntervalIntegrable u volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [u]
    fun_prop
  have hintAbs : IntervalIntegrable (fun t => |deriv g t|) volume 0 1 :=
    hac.intervalIntegrable_deriv.abs
  have hftc := hac.integral_deriv_eq_sub
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by norm_num) hac.intervalIntegrable_deriv.abs hint hderiv'
  have hconst :
      (∫ t in (0 : ℝ)..1, u t) =
        ‖y - x‖ * (a + b / 2 * (‖x‖ + ‖y‖) + b * ‖z‖) := by
    have hpoint (t : ℝ) :
        u t = ‖y - x‖ *
          ((a + b * ‖x‖ + b * ‖z‖) + t * (b * ‖y‖ - b * ‖x‖)) := by
      dsimp [u]
      ring
    calc
      (∫ t in (0 : ℝ)..1, u t) =
          ∫ t in (0 : ℝ)..1, ‖y - x‖ *
            ((a + b * ‖x‖ + b * ‖z‖) + t * (b * ‖y‖ - b * ‖x‖)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hpoint t
      _ = ‖y - x‖ *
          ((a + b * ‖x‖ + b * ‖z‖) + (b * ‖y‖ - b * ‖x‖) / 2) := by
        have hc0 : IntervalIntegrable
            (fun _ : ℝ => a + b * ‖x‖ + b * ‖z‖) volume 0 1 := by
          exact (continuous_const : Continuous
            (fun _ : ℝ => a + b * ‖x‖ + b * ‖z‖)).intervalIntegrable
            (μ := volume) 0 1
        have hc1 : IntervalIntegrable
            (fun t : ℝ => t * (b * ‖y‖ - b * ‖x‖)) volume 0 1 := by
          exact ((continuous_id.mul (continuous_const : Continuous
            (fun _ : ℝ => b * ‖y‖ - b * ‖x‖)))).intervalIntegrable
            (μ := volume) 0 1
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add hc0 hc1]
        rw [intervalIntegral.integral_mul_const]
        simp only [intervalIntegral.integral_const, integral_id]
        norm_num
        ring_nf
        all_goals
          left
          trivial
      _ = ‖y - x‖ * (a + b / 2 * (‖x‖ + ‖y‖) + b * ‖z‖) := by ring
  calc
    |g 1 - g 0| = |∫ t in (0 : ℝ)..1, deriv g t| := by
      rw [← hftc]
    _ ≤ ∫ t in (0 : ℝ)..1, |deriv g t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm
          (μ := volume) (f := fun t : ℝ => deriv g t) (by norm_num))
    _ ≤ ∫ t in (0 : ℝ)..1, u t := hmono
    _ = ‖y - x‖ * (a + b / 2 * (‖x‖ + ‖y‖) + b * ‖z‖) := hconst

/-- Translating a fixed segment by a volume-a.e. good set of points gives
almost every translate on which the source property holds for almost every
parameter.  This is the measure-theoretic step needed before applying the
one-dimensional FTC helper above. -/
theorem ae_shifted_segment_of_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : EuclideanSpace ℝ ι → Prop)
    (hp : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ ι)), p w)
    (x y : EuclideanSpace ℝ ι) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        p ((1 - t) • x + t • y + z) := by
  let E := EuclideanSpace ℝ ι
  have hbad : (volume : Measure E) {w | ¬ p w} = 0 := ae_iff.mp hp
  obtain ⟨N, hbadN, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null hbad
  have hN : ∀ᵐ w ∂(volume : Measure E), w ∉ N := by
    apply ae_iff.mpr
    simpa using hNzero
  let line (t : ℝ) (z : E) := (1 - t) • x + t • y + z
  have hsection (t : ℝ) : ∀ᵐ z ∂(volume : Measure E), line t z ∉ N := by
    let c : E := (1 - t) • x + t • y
    have hpull :=
      (measurePreserving_add_right (volume : Measure E) c).quasiMeasurePreserving.ae hN
    filter_upwards [hpull] with z hz
    simpa [line, c, add_assoc, add_comm, add_left_comm] using hz
  have hmeas : MeasurableSet {q : ℝ × E | line q.1 q.2 ∉ N} := by
    change MeasurableSet ((fun q : ℝ × E => line q.1 q.2) ⁻¹' Nᶜ)
    apply hNmeas.compl.preimage
    dsimp [line]
    fun_prop
  have hswap := (MeasureTheory.Measure.ae_ae_comm
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := volume) hmeas).mp (Filter.Eventually.of_forall hsection)
  filter_upwards [hswap] with z hz
  filter_upwards [hz] with t ht
  by_contra hpt
  exact ht (hbadN hpt)

end LOOConcentration.Revision
