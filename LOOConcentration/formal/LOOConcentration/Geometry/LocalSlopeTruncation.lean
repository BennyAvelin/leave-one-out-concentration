import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.Algebra.Order.Group.MinMax

/-! Truncation preserves local Euclidean Lipschitzness and cannot increase local slope. -/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

noncomputable def clippedObservationFunction {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (N : ℝ) :
    {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)} :=
  ⟨fun z => max (-N) (min (f.1 z) N), by
    intro z
    obtain ⟨U, hU, C, hC, hLip⟩ := f.2 z
    refine ⟨U, hU, C, hC, ?_⟩
    intro w hw v hv
    calc
      |max (-N) (min (f.1 w) N) - max (-N) (min (f.1 v) N)| =
          |max (min (f.1 w) N) (-N) - max (min (f.1 v) N) (-N)| := by
            simp only [max_comm]
      _ ≤ |min (f.1 w) N - min (f.1 v) N| :=
        abs_max_sub_max_le_abs _ _ _
      _ ≤ |f.1 w - f.1 v| := by
        simpa using abs_min_sub_min_le_max (f.1 w) N (f.1 v) N
      _ ≤ C * observationNorm (w - v) := hLip w hw v hv⟩

theorem observationLocalSlope_clip_le {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (N : ℝ) (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope (clippedObservationFunction f N) z ≤
      observationLocalSlope f z := by
  unfold observationLocalSlope
  apply limsup_le_limsup
  · apply Filter.Eventually.of_forall
    intro w
    have hclip :
        |(clippedObservationFunction f N).1 w -
          (clippedObservationFunction f N).1 z| ≤ |f.1 w - f.1 z| := by
      change |max (-N) (min (f.1 w) N) - max (-N) (min (f.1 z) N)| ≤ _
      calc
        _ = |max (min (f.1 w) N) (-N) - max (min (f.1 z) N) (-N)| := by
          simp only [max_comm]
        _ ≤ |min (f.1 w) N - min (f.1 z) N| := abs_max_sub_max_le_abs _ _ _
        _ ≤ |f.1 w - f.1 z| := by
          simpa using abs_min_sub_min_le_max (f.1 w) N (f.1 z) N
    exact div_le_div_of_nonneg_right hclip (Real.sqrt_nonneg _)
  · exact observationSlope_cobounded (clippedObservationFunction f N) z
  · exact observationSlope_bounded f z

noncomputable def clippedDatasetFunction {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * datasetNorm (w - v)})
    (N : ℝ) :
    {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * datasetNorm (w - v)} :=
  ⟨fun z => max (-N) (min (f.1 z) N), by
    intro z
    obtain ⟨U, hU, C, hC, hLip⟩ := f.2 z
    refine ⟨U, hU, C, hC, ?_⟩
    intro w hw v hv
    calc
      |max (-N) (min (f.1 w) N) - max (-N) (min (f.1 v) N)| =
          |max (min (f.1 w) N) (-N) - max (min (f.1 v) N) (-N)| := by
            simp only [max_comm]
      _ ≤ |min (f.1 w) N - min (f.1 v) N| :=
        abs_max_sub_max_le_abs _ _ _
      _ ≤ |f.1 w - f.1 v| := by
        simpa using abs_min_sub_min_le_max (f.1 w) N (f.1 v) N
      _ ≤ C * datasetNorm (w - v) := hLip w hw v hv⟩

theorem datasetLocalSlope_clip_le {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * datasetNorm (w - v)})
    (N : ℝ) (z : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    datasetLocalSlope (clippedDatasetFunction f N) z ≤
      datasetLocalSlope f z := by
  unfold datasetLocalSlope
  apply limsup_le_limsup
  · apply Filter.Eventually.of_forall
    intro w
    have hclip :
        |(clippedDatasetFunction f N).1 w -
          (clippedDatasetFunction f N).1 z| ≤ |f.1 w - f.1 z| := by
      change |max (-N) (min (f.1 w) N) - max (-N) (min (f.1 z) N)| ≤ _
      calc
        _ = |max (min (f.1 w) N) (-N) - max (min (f.1 z) N) (-N)| := by
          simp only [max_comm]
        _ ≤ |min (f.1 w) N - min (f.1 z) N| := abs_max_sub_max_le_abs _ _ _
        _ ≤ |f.1 w - f.1 z| := by
          simpa using abs_min_sub_min_le_max (f.1 w) N (f.1 z) N
    exact div_le_div_of_nonneg_right hclip (Real.sqrt_nonneg _)
  · exact datasetSlope_cobounded (clippedDatasetFunction f N) z
  · exact datasetSlope_bounded f z

end LOOConcentration
