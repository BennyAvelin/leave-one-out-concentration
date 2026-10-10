import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic.Module
import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentration.Geometry.NormTransport

/-!
# Segment estimates from the frozen dataset local slope

The scalar restriction of a locally Lipschitz data function to a closed affine
segment is absolutely continuous. Its derivative is bounded by the frozen
local slope times the exact Euclidean speed of the segment.
-/

set_option autoImplicit false

open Filter Set
open MeasureTheory
open scoped Topology

namespace LOOConcentration

abbrev DataCarrier (k m n : ℕ) :=
  Dataset (Observation (k + 1) (m + 1)) (n + 1)

abbrev LocallyLipschitzDataFunction (k m n : ℕ) :=
  {g : DataCarrier k m n → ℝ //
    ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
      ∀ E ∈ U, ∀ F ∈ U,
        |g E - g F| ≤ C * datasetNorm (E - F)}

theorem datasetToEuclidean_smul {k m n : ℕ} (c : ℝ)
    (D : Dataset (Observation k m) n) :
    datasetToEuclidean (c • D) = c • datasetToEuclidean D := by
  apply PiLp.ext
  intro q
  rcases q with ⟨i, j⟩
  cases j <;> simp [datasetToEuclidean]

/-- Homogeneity of the frozen unnormalized dataset norm. -/
theorem datasetNorm_smul {k m n : ℕ} (c : ℝ)
    (D : Dataset (Observation k m) n) :
    datasetNorm (c • D) = |c| * datasetNorm D := by
  rw [datasetNorm_eq_euclidean, datasetNorm_eq_euclidean,
    datasetToEuclidean_smul, norm_smul, Real.norm_eq_abs]

/-- The affine path from `y` to `x`, parameterized on the real line. -/
def segmentPath {k m n : ℕ} (x y : DataCarrier k m n) (t : ℝ) :
    DataCarrier k m n := y + t • (x - y)

private theorem datasetNorm_zero {k m n : ℕ} :
    datasetNorm (0 : DataCarrier k m n) = 0 := by
  rw [datasetNorm_eq_euclidean]
  have hmap : datasetToEuclidean (0 : DataCarrier k m n) = 0 := by
    apply PiLp.ext
    intro q
    rcases q with ⟨i, j⟩
    rcases j with j | j <;> simp [datasetToEuclidean]
  rw [hmap]
  simp

private theorem segmentPath_continuous {k m n : ℕ} (x y : DataCarrier k m n) :
    Continuous (segmentPath x y) := by
  change Continuous fun t : ℝ => y + t • (x - y)
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem segmentPath_sub {k m n : ℕ} (x y : DataCarrier k m n) (s t : ℝ) :
    segmentPath x y s - segmentPath x y t = (s - t) • (x - y) := by
  simp only [segmentPath]
  module

theorem segmentPath_norm_sub {k m n : ℕ} (x y : DataCarrier k m n) (s t : ℝ) :
    datasetNorm (segmentPath x y s - segmentPath x y t) =
      |s - t| * datasetNorm (x - y) := by
  rw [segmentPath_sub, datasetNorm_smul]

theorem segmentPath_eq_convexCombination {k m n : ℕ} (x y : DataCarrier k m n)
    (t : ℝ) :
    segmentPath x y t = (1 - t) • y + t • x := by
  simp only [segmentPath, sub_smul, one_smul]
  module

theorem segmentPath_norm_le {k m n : ℕ} (x y : DataCarrier k m n)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    datasetNorm (segmentPath x y t) ≤
      (1 - t) * datasetNorm y + t * datasetNorm x := by
  rw [segmentPath_eq_convexCombination]
  calc
    datasetNorm ((1 - t) • y + t • x) ≤
        datasetNorm ((1 - t) • y) + datasetNorm (t • x) := datasetNorm_add_le _ _
    _ = |1 - t| * datasetNorm y + |t| * datasetNorm x := by
      rw [datasetNorm_smul, datasetNorm_smul]
    _ = (1 - t) * datasetNorm y + t * datasetNorm x := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]

/-- The scalar restriction of a locally Lipschitz data function is locally Lipschitz. -/
theorem segmentPullback_locallyLipschitz {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (x y : DataCarrier k m n) :
    LocallyLipschitz (fun t : ℝ => F.1 (segmentPath x y t)) := by
  intro t
  obtain ⟨U, hU, C, hC, hLip⟩ := F.2 (segmentPath x y t)
  have hpath_cont : Continuous (segmentPath x y) := segmentPath_continuous x y
  have hpre : segmentPath x y ⁻¹' U ∈ 𝓝 t :=
    hpath_cont.continuousAt.preimage_mem_nhds hU
  refine ⟨Real.toNNReal (C * datasetNorm (x - y)), segmentPath x y ⁻¹' U,
    hpre, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro s hs t ht
  rw [Real.dist_eq, Real.dist_eq]
  calc
    |F.1 (segmentPath x y s) - F.1 (segmentPath x y t)| ≤
        C * datasetNorm (segmentPath x y s - segmentPath x y t) :=
      hLip _ hs _ ht
    _ = C * (|s - t| * datasetNorm (x - y)) := by rw [segmentPath_norm_sub]
    _ = (C * datasetNorm (x - y)) * |s - t| := by ring

def segmentPullback {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n)
    (x y : DataCarrier k m n) (t : ℝ) : ℝ :=
  F.1 (segmentPath x y t)

theorem segmentPullback_absolutelyContinuous {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (x y : DataCarrier k m n) :
    AbsolutelyContinuousOnInterval (segmentPullback F x y) 0 1 := by
  have hloc := segmentPullback_locallyLipschitz F x y
  have hlocIcc : LocallyLipschitzOn (Icc (0 : ℝ) 1) (segmentPullback F x y) :=
    hloc.locallyLipschitzOn
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hlocIcc
  have hKU : LipschitzOnWith K (segmentPullback F x y) (uIcc 0 1) := by
    simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hK
  exact hKU.absolutelyContinuousOnInterval

private theorem segmentPullback_deriv_bound {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (x y : DataCarrier k m n) (hxy : x ≠ y) (t : ℝ) :
    |deriv (segmentPullback F x y) t| ≤
      datasetNorm (x - y) * (a + b * datasetNorm (segmentPath x y t)) := by
  let speed := datasetNorm (x - y)
  let z := segmentPath x y t
  let q : DataCarrier k m n → ℝ := fun E =>
    |F.1 E - F.1 z| / datasetNorm (E - z)
  let L := a + b * datasetNorm z
  have hspeed : 0 < speed := datasetNorm_pos_of_ne (sub_ne_zero.mpr hxy)
  have hLnonneg : 0 ≤ L :=
    add_nonneg ha (mul_nonneg hb (Real.sqrt_nonneg _))
  have hlim : limsup q (𝓝[≠] z) ≤ L := by
    simpa [q, L, z, datasetLocalSlope] using hSlope z
  have hq_bdd : (𝓝[≠] z).IsBoundedUnder (· ≤ ·) q := by
    simpa [q] using datasetSlope_bounded F z
  have hpath_cont : Continuous (segmentPath x y) := segmentPath_continuous x y
  have hpath_inj : ∀ {s u : ℝ}, s ≠ u → segmentPath x y s ≠ segmentPath x y u := by
    intro s u hsu heq
    have hn : datasetNorm (segmentPath x y s - segmentPath x y u) = 0 := by
      rw [heq]
      simp [datasetNorm_zero]
    rw [segmentPath_norm_sub] at hn
    have habs : |s - u| = 0 := (mul_eq_zero.mp hn).resolve_right (ne_of_gt hspeed)
    exact hsu (sub_eq_zero.mp (abs_eq_zero.mp habs))
  have hpath_punct : Tendsto (segmentPath x y)
      (𝓝[≠] t) (𝓝[≠] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpath_cont.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hpath_inj hs
  have hderiv_eps : ∀ ε : ℝ, 0 < ε →
      |deriv (segmentPullback F x y) t| ≤ (L + ε) * speed := by
    intro ε hε
    have hquot_event : ∀ᶠ E in 𝓝[≠] z, q E < L + ε :=
      eventually_lt_of_limsup_lt (hlim.trans_lt (lt_add_of_pos_right L hε)) hq_bdd
    have hline_event : ∀ᶠ s in 𝓝[≠] t, q (segmentPath x y s) < L + ε :=
      hpath_punct.eventually hquot_event
    let C := (L + ε) * speed
    have hpunct : ∀ᶠ s in 𝓝[≠] t,
        ‖segmentPullback F x y s - segmentPullback F x y t‖ ≤ C * ‖s - t‖ := by
      filter_upwards [hline_event, self_mem_nhdsWithin] with s hq hs
      have hden : 0 < datasetNorm (segmentPath x y s - z) := by
        rw [segmentPath_norm_sub]
        exact mul_pos (abs_pos.mpr (sub_ne_zero.mpr hs)) hspeed
      have hmul : |F.1 (segmentPath x y s) - F.1 z| <
          (L + ε) * datasetNorm (segmentPath x y s - z) := by
        exact (div_lt_iff₀ hden).mp (by simpa [q] using hq)
      rw [segmentPath_norm_sub] at hmul
      simpa [C, segmentPullback, z, Real.norm_eq_abs, mul_assoc, mul_left_comm,
        mul_comm] using le_of_lt hmul
    have hnear : ∀ᶠ s in 𝓝 t,
        ‖segmentPullback F x y s - segmentPullback F x y t‖ ≤ C * ‖s - t‖ := by
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpunct with ⟨U, hU, hsub⟩
      apply Filter.mem_of_superset hU
      intro s hs
      by_cases hst : s = t
      · simp [hst]
      · exact hsub ⟨hs, hst⟩
    have hC : 0 ≤ C := mul_nonneg (add_nonneg hLnonneg hε.le) (le_of_lt hspeed)
    have hnorm := norm_deriv_le_of_lip' hC hnear
    simpa [C, Real.norm_eq_abs] using hnorm
  have hderiv : |deriv (segmentPullback F x y) t| ≤ L * speed := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hη : 0 < ε / speed := div_pos hε hspeed
    calc
      |deriv (segmentPullback F x y) t| ≤ (L + ε / speed) * speed :=
        hderiv_eps (ε / speed) hη
      _ = L * speed + ε := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hspeed)]
  simpa [L, speed, z, mul_comm] using hderiv

/-- The source segment estimate, in the exact frozen data norm. -/
theorem datasetLocalSlope_segment_estimate {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (x y : DataCarrier k m n) :
    |F.1 x - F.1 y| ≤
      datasetNorm (x - y) * (a + b / 2 * (datasetNorm x + datasetNorm y)) := by
  by_cases hxy : x = y
  · subst y
    simp [datasetNorm_zero]
  let g := segmentPullback F x y
  let speed := datasetNorm (x - y)
  have hAC : AbsolutelyContinuousOnInterval g 0 1 :=
    segmentPullback_absolutelyContinuous F x y
  have hFTC : (∫ t in (0 : ℝ)..1, deriv g t) = g 1 - g 0 :=
    hAC.integral_deriv_eq_sub
  have hderiv := fun t => segmentPullback_deriv_bound F a b ha hb hSlope x y hxy t
  have hlin : ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv g t| ≤ speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x)) := by
    intro t ht
    calc
      |deriv g t| ≤ speed * (a + b * datasetNorm (segmentPath x y t)) := by
        simpa [g, speed] using hderiv t
      _ ≤ speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (datasetNorm_pos_of_ne (sub_ne_zero.mpr hxy)))
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left (segmentPath_norm_le x y ht) hb) a
  have hIntDeriv : IntervalIntegrable (fun t => |deriv g t|) volume 0 1 :=
    hAC.intervalIntegrable_deriv.abs
  have hcontMajorant : Continuous (fun t : ℝ =>
      speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x))) := by
    fun_prop
  have hIntMajorant : IntervalIntegrable (fun t : ℝ =>
      speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x))) volume 0 1 :=
    hcontMajorant.intervalIntegrable 0 1
  have hIntegral := intervalIntegral.integral_mono_on
    (a := (0 : ℝ)) (b := 1) (by norm_num) hIntDeriv hIntMajorant hlin
  have hIntegralValue :
      (∫ t in (0 : ℝ)..1,
        speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x))) =
          speed * (a + b / 2 * (datasetNorm x + datasetNorm y)) := by
    have hfun : (fun t : ℝ => a + b * ((1 - t) * datasetNorm y + t * datasetNorm x)) =
        fun t => (a + b * datasetNorm y) + t * (b * (datasetNorm x - datasetNorm y)) := by
      funext t
      ring
    have hid : (∫ t in (0 : ℝ)..1, t) = (1 / 2 : ℝ) := by
      have hderiv : ∀ t : ℝ,
          HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
        intro t
        simpa using (hasDerivAt_pow 2 t).div_const 2
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1) (f := fun t : ℝ => t ^ 2 / 2)
        (f' := fun t : ℝ => t) (fun t _ => hderiv t)
        ((continuous_id).intervalIntegrable 0 1)
      norm_num at h ⊢
    have hmulInt : IntervalIntegrable (fun t : ℝ =>
        t * (b * (datasetNorm x - datasetNorm y))) volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable 0 1
    calc
      (∫ t in (0 : ℝ)..1,
        speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x))) =
          speed * (∫ t in (0 : ℝ)..1,
            a + b * ((1 - t) * datasetNorm y + t * datasetNorm x)) := by
              rw [intervalIntegral.integral_const_mul]
      _ = speed * (∫ t in (0 : ℝ)..1,
            (a + b * datasetNorm y) + t * (b * (datasetNorm x - datasetNorm y))) := by
              rw [hfun]
      _ = speed * (a + b * datasetNorm y +
            (b * (datasetNorm x - datasetNorm y)) / 2) := by
              congr 1
              rw [intervalIntegral.integral_add intervalIntegrable_const hmulInt]
              simp [intervalIntegral.integral_const, intervalIntegral.integral_mul_const, hid]
              ring
      _ = speed * (a + b / 2 * (datasetNorm x + datasetNorm y)) := by ring
  calc
    |F.1 x - F.1 y| = |g 1 - g 0| := by
      simp [g, segmentPullback, segmentPath]
    _ = |∫ t in (0 : ℝ)..1, deriv g t| := by rw [hFTC]
    _ ≤ ∫ t in (0 : ℝ)..1, |deriv g t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1,
        speed * (a + b * ((1 - t) * datasetNorm y + t * datasetNorm x)) := hIntegral
    _ = speed * (a + b / 2 * (datasetNorm x + datasetNorm y)) := hIntegralValue

end LOOConcentration
