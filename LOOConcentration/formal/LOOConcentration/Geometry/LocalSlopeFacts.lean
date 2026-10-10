import LOOConcentration.Frozen.Slopes.ObservationLocalSlope
import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.Topology.Perfect

/-! Bounded quotient facts for the frozen real local slopes. -/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

theorem observationSlope_bounded {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (z : Observation (k + 1) (m + 1)) :
    (𝓝[≠] z).IsBoundedUnder (· ≤ ·)
      (fun w => |f.1 w - f.1 z| / observationNorm (w - z)) := by
  obtain ⟨U, hU, C, hC, hLip⟩ := f.2 z
  apply Filter.isBoundedUnder_of_eventually_le (a := C)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with w hw hwne
  have hne : w ≠ z := by simpa using hwne
  have hpos := observationNorm_sub_pos hne
  exact (div_le_iff₀ hpos).2 (hLip w hw z (mem_of_mem_nhds hU))

theorem observationSlope_cobounded {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (z : Observation (k + 1) (m + 1)) :
    (𝓝[≠] z).IsCoboundedUnder (· ≤ ·)
      (fun w => |f.1 w - f.1 z| / observationNorm (w - z)) := by
  apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
  exact Filter.Frequently.of_forall (fun w =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

theorem observationLocalSlope_nonneg {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (z : Observation (k + 1) (m + 1)) :
    0 ≤ observationLocalSlope f z := by
  rw [observationLocalSlope]
  apply le_limsup_of_frequently_le
    (hu_le := observationSlope_bounded f z)
  exact Filter.Frequently.of_forall (fun w =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

theorem datasetSlope_bounded {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)})
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    (𝓝[≠] D).IsBoundedUnder (· ≤ ·)
      (fun E => |f.1 E - f.1 D| / datasetNorm (E - D)) := by
  obtain ⟨U, hU, C, hC, hLip⟩ := f.2 D
  apply Filter.isBoundedUnder_of_eventually_le (a := C)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with E hE hEne
  have hne : E ≠ D := by simpa using hEne
  have hpos := datasetNorm_sub_pos hne
  exact (div_le_iff₀ hpos).2 (hLip E hE D (mem_of_mem_nhds hU))

theorem datasetSlope_cobounded {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)})
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    (𝓝[≠] D).IsCoboundedUnder (· ≤ ·)
      (fun E => |f.1 E - f.1 D| / datasetNorm (E - D)) := by
  apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
  exact Filter.Frequently.of_forall (fun E =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

theorem datasetLocalSlope_nonneg {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)})
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    0 ≤ datasetLocalSlope f D := by
  rw [datasetLocalSlope]
  apply le_limsup_of_frequently_le
    (hu_le := datasetSlope_bounded f D)
  exact Filter.Frequently.of_forall (fun E =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

end LOOConcentration
