import LOOConcentrationRevision.FunctionalInequalities.SobolevLinear
import Mathlib.Analysis.LocallyConvex.WeakSpace

set_option autoImplicit false

namespace LOOConcentration.Revision

open Filter

local instance instFactLpTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

noncomputable section

/-- The convex hulls of the tails of a weakly convergent sequence contain a sequence
converging in norm to its weak limit. -/
theorem mazur_convexHull_tail_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E) (u : E)
    (hweak : Tendsto (fun n => toWeakSpace ℝ E (f n)) atTop
      (nhds (toWeakSpace ℝ E u))) :
    ∃ g : ℕ → E,
      (∀ n, g n ∈ convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) ∧
      Tendsto g atTop (nhds u) := by
  classical
  have hweak_tail (n : ℕ) :
      toWeakSpace ℝ E u ∈
        closure (toWeakSpace ℝ E '' {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) := by
    rw [mem_closure_iff]
    intro o ho huo
    have hevent : ∀ᶠ k in atTop, toWeakSpace ℝ E (f k) ∈ o :=
      hweak.eventually (ho.mem_nhds huo)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
    let k := max n N
    have hnk : n ≤ k := Nat.le_max_left n N
    have hNk : N ≤ k := Nat.le_max_right n N
    refine ⟨toWeakSpace ℝ E (f k), hN k hNk, ?_⟩
    exact ⟨f k, ⟨k, hnk, rfl⟩, rfl⟩
  have htail_mono (n : ℕ) :
      toWeakSpace ℝ E '' {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v} ⊆
        toWeakSpace ℝ E ''
          convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v} := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, subset_convexHull ℝ _ hv, rfl⟩
  have hweak_hull (n : ℕ) :
      toWeakSpace ℝ E u ∈
        closure (toWeakSpace ℝ E ''
          convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) := by
    exact (closure_mono (htail_mono n)) (hweak_tail n)
  have hstrong_closure (n : ℕ) :
      u ∈ closure (convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) := by
    have hconvex :
        Convex ℝ (convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) :=
      convex_convexHull ℝ _
    have himage :
        toWeakSpace ℝ E u ∈
          toWeakSpace ℝ E ''
            closure (convexHull ℝ {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v}) := by
      rw [hconvex.toWeakSpace_closure ℝ]
      exact hweak_hull n
    rcases himage with ⟨v, hv, hveq⟩
    have hvu : v = u := (toWeakSpace ℝ E).injective hveq
    simpa [hvu] using hv
  have hexists (n : ℕ) :
      ∃ v : E,
        v ∈ convexHull ℝ {w : E | ∃ k : ℕ, n ≤ k ∧ f k = w} ∧
          ‖v - u‖ < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨v, hv, hvdist⟩ :=
      Metric.mem_closure_iff.mp (hstrong_closure n) (1 / ((n : ℝ) + 1)) hε
    refine ⟨v, hv, ?_⟩
    simpa [dist_eq_norm, norm_sub_rev] using hvdist
  choose g hg_mem hg_dist using hexists
  have hnorm : Tendsto (fun n => ‖g n - u‖) atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hg_dist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨g, hg_mem, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hnorm

/-- A weak limit of literal smooth Sobolev pairs is represented by an actual
element of the joint Sobolev-pair closure. -/
theorem weak_limit_smoothSobolevPairs_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ ι)) [MeasureTheory.IsProbabilityMeasure μ]
    (f : ℕ → WithLp 2
      (MeasureTheory.Lp ℝ 2 μ × MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ))
    (p : WithLp 2
      (MeasureTheory.Lp ℝ 2 μ × MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ))
    (hweak : Tendsto (fun n => toWeakSpace ℝ
      (WithLp 2 (MeasureTheory.Lp ℝ 2 μ × MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ))
      (f n)) atTop
      (nhds (toWeakSpace ℝ
        (WithLp 2 (MeasureTheory.Lp ℝ 2 μ × MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ)) p)))
    (hf : ∀ n, f n ∈ smoothSobolevPairs μ) :
    ∃ u : SobolevPair μ, u.1 = p := by
  let E := WithLp 2
    (MeasureTheory.Lp ℝ 2 μ × MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ)
  obtain ⟨g, hg_mem, hg_tendsto⟩ :=
    @mazur_convexHull_tail_tendsto E inferInstance inferInstance f p hweak
  have htail_subset (n : ℕ) :
      {v : E | ∃ k : ℕ, n ≤ k ∧ f k = v} ⊆ smoothSobolevPairs μ := by
    rintro v ⟨k, _, rfl⟩
    exact hf k
  have hconvex : Convex ℝ (smoothSobolevPairs μ) :=
    (smoothSobolevPairsSubmodule μ).convex
  have hg_smooth (n : ℕ) : g n ∈ smoothSobolevPairs μ :=
    (convexHull_min (htail_subset n) hconvex) (hg_mem n)
  have hp_closure : p ∈ closure (smoothSobolevPairs μ) :=
    isClosed_closure.mem_of_tendsto hg_tendsto
      (Filter.Eventually.of_forall fun n => subset_closure (hg_smooth n))
  exact ⟨⟨p, hp_closure⟩, rfl⟩

end

end LOOConcentration.Revision
