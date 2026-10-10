import LOOConcentrationRevision.FunctionalInequalities.MazurClosure
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false

namespace LOOConcentration.Revision

open Filter MeasureTheory

local instance instFactLpTwoWeak : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

noncomputable section

/-- A bounded sequence in the literal joint `L²` space has a weakly convergent
subsequence.  A strong limit of its scalar coordinates is the scalar coordinate
of that same joint limit. -/
theorem exists_weak_subsequence
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
    (B : ℝ) (hB : ∀ n, ‖f n‖ ≤ B) :
    ∃ p : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => toWeakSpace ℝ
          (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) (f (φ n))) atTop
          (nhds (toWeakSpace ℝ
            (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) p)) := by
  let G := WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)
  let V : Submodule ℝ G := (Submodule.span ℝ (Set.range f)).topologicalClosure
  have hspan_sep : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range f) : Set G) :=
    TopologicalSpace.IsSeparable.span (Set.countable_range f).isSeparable
  have hV_sep : TopologicalSpace.IsSeparable (V : Set G) := by
    change TopologicalSpace.IsSeparable
      (closure (Submodule.span ℝ (Set.range f) : Set G))
    exact hspan_sep.closure
  have hV_separable : TopologicalSpace.SeparableSpace V := hV_sep.separableSpace
  have hV_complete : CompleteSpace V := by
    dsimp [V]
    infer_instance
  let z : ℕ → V := fun n => ⟨f n, by
    change f n ∈ closure (Submodule.span ℝ (Set.range f) : Set G)
    exact subset_closure (Submodule.subset_span (Set.mem_range_self n))⟩
  let d : ℕ → StrongDual ℝ V := fun n => (InnerProductSpace.toDual ℝ V) (z n)
  let dw : ℕ → WeakDual ℝ V := fun n => StrongDual.toWeakDual (d n)
  have hd_bound : ∀ n, ‖d n‖ ≤ B := by
    intro n
    calc
      ‖d n‖ = ‖z n‖ := (InnerProductSpace.toDual ℝ V).norm_map (z n)
      _ = ‖f n‖ := rfl
      _ ≤ B := hB n
  have hdball : ∀ n, dw n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ V) B := by
    intro n
    rw [Set.mem_preimage]
    apply Metric.mem_closedBall.mpr
    have hd : WeakDual.toStrongDual (dw n) = d n := by simp [dw]
    calc
      dist (WeakDual.toStrongDual (dw n)) (0 : StrongDual ℝ V) =
          ‖WeakDual.toStrongDual (dw n) - (0 : StrongDual ℝ V)‖ :=
        dist_eq_norm (WeakDual.toStrongDual (dw n)) (0 : StrongDual ℝ V)
      _ = ‖WeakDual.toStrongDual (dw n)‖ := by rw [sub_zero]
      _ = ‖d n‖ := congrArg norm hd
      _ ≤ B := hd_bound n
  have hcompact : IsSeqCompact
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ V) B) :=
    @WeakDual.isSeqCompact_closedBall ℝ V _ _ _ hV_separable _ 0 B
  obtain ⟨w, _, φ, hφ, hdw⟩ :=
    hcompact.subseq_of_frequently_in (Filter.Frequently.of_forall hdball)
  let q : V := (InnerProductSpace.toDual ℝ V).symm (WeakDual.toStrongDual w)
  have hdw_eval (y : V) :
      Tendsto (fun n => dw (φ n) y) atTop (nhds (w y)) := by
    change Tendsto (fun n => dw (φ n)) atTop (nhds w) at hdw
    have hdual_injective : Function.Injective (topDualPairing ℝ V) := by
      intro a b hab
      apply ContinuousLinearMap.ext
      intro x
      have hx := LinearMap.congr_fun hab x
      simpa only [topDualPairing_apply] using hx
    exact (WeakBilin.tendsto_iff_forall_eval_tendsto
      (topDualPairing ℝ V) hdual_injective).1 hdw y
  have hV_weak : Tendsto (fun n => toWeakSpace ℝ V (z (φ n))) atTop
      (nhds (toWeakSpace ℝ V q)) := by
    have hweak_injective : Function.Injective ((topDualPairing ℝ V).flip) := by
      intro x y hxy
      have he : inner ℝ (x - y) x = inner ℝ (x - y) y := by
        have h := DFunLike.congr_fun hxy (InnerProductSpace.toDualMap ℝ V (x - y))
        change inner ℝ (x - y) x = inner ℝ (x - y) y at h
        exact h
      have hzero : inner ℝ (x - y) (x - y) = 0 := by
        calc
          inner ℝ (x - y) (x - y) = inner ℝ (x - y) x - inner ℝ (x - y) y := by
            rw [inner_sub_right]
          _ = 0 := sub_eq_zero.mpr he
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    exact (WeakBilin.tendsto_iff_forall_eval_tendsto
      ((topDualPairing ℝ V).flip) hweak_injective).2 (by
        intro l
        let y : V := (InnerProductSpace.toDual ℝ V).symm l
        have hly : InnerProductSpace.toDual ℝ V y = l := by
          simp [y]
        have hseq (n : ℕ) : l (z (φ n)) = dw (φ n) y := by
          change l (z (φ n)) = (InnerProductSpace.toDual ℝ V (z (φ n))) y
          rw [← hly]
          simp only [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
            InnerProductSpace.toDualMap_apply_apply]
          exact real_inner_comm _ _
        have hlim : l q = w y := by
          change l q = (WeakDual.toStrongDual w) y
          rw [← hly]
          calc
            (InnerProductSpace.toDual ℝ V y) q = inner ℝ y q := by
              rw [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
                InnerProductSpace.toDualMap_apply_apply]
            _ = inner ℝ q y := real_inner_comm _ _
            _ = (WeakDual.toStrongDual w) y := InnerProductSpace.toDual_symm_apply
        change Tendsto (fun n => l (z (φ n))) atTop (nhds (l q))
        simpa only [hseq, hlim] using hdw_eval y)
  let i : V →L[ℝ] G := V.subtypeL
  have hG_weak : Tendsto (fun n => toWeakSpace ℝ G ((i (z (φ n)) : G))) atTop
      (nhds (toWeakSpace ℝ G ((i q : G)))) := by
    convert (((WeakSpace.map i).continuous.tendsto (toWeakSpace ℝ V q)).comp hV_weak) using 1
    all_goals rfl
  refine ⟨i q, φ, hφ, ?_⟩
  simpa [i] using hG_weak

/-- A strongly convergent scalar coordinate identifies the scalar coordinate
of a weak limit of the same bounded joint subsequence. -/
theorem exists_weak_subsequence_with_scalar_limit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
    (B : ℝ) (hB : ∀ n, ‖f n‖ ≤ B)
    (s : Lp ℝ 2 μ)
    (hscalar : Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop (nhds s)) :
    ∃ p : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => toWeakSpace ℝ
          (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) (f (φ n))) atTop
          (nhds (toWeakSpace ℝ
            (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) p)) ∧
        (WithLp.ofLp p).1 = s := by
  obtain ⟨p, φ, hφ, hweak⟩ := exists_weak_subsequence μ f B hB
  have hscalar_subseq : Tendsto (fun n => (WithLp.ofLp (f (φ n))).1) atTop
      (nhds s) := hscalar.comp hφ.tendsto_atTop
  let G := WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)
  let first : G →L[ℝ] Lp ℝ 2 μ := WithLp.fstL 2 ℝ (Lp ℝ 2 μ)
    (Lp (EuclideanSpace ℝ ι) 2 μ)
  have hfirst_weak : Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 2 μ)
      ((WithLp.ofLp (f (φ n))).1)) atTop
      (nhds (toWeakSpace ℝ (Lp ℝ 2 μ) ((WithLp.ofLp p).1))) := by
    convert (((WeakSpace.map first).continuous.tendsto (toWeakSpace ℝ G p)).comp hweak)
        using 1 <;> rfl
  have hfirst_strong_weak : Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 2 μ)
      ((WithLp.ofLp (f (φ n))).1)) atTop
      (nhds (toWeakSpace ℝ (Lp ℝ 2 μ) s)) := by
    convert (((toWeakSpaceCLM ℝ (Lp ℝ 2 μ)).continuous.tendsto s).comp hscalar_subseq)
        using 1 <;> rfl
  have hfirst_eq : (WithLp.ofLp p).1 = s :=
    (toWeakSpace ℝ (Lp ℝ 2 μ)).injective
      (tendsto_nhds_unique hfirst_weak hfirst_strong_weak)
  exact ⟨p, φ, hφ, hweak, hfirst_eq⟩

/-- A bounded sequence of smooth joint generators has an actual Sobolev-pair
limit with the prescribed scalar coordinate, retaining the gradient in the
same weakly convergent joint subsequence. -/
theorem exists_sobolevPair_of_bounded_smooth_with_scalar_limit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
    (B : ℝ) (hB : ∀ n, ‖f n‖ ≤ B)
    (s : Lp ℝ 2 μ)
    (hscalar : Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop (nhds s))
    (hf : ∀ n, f n ∈ smoothSobolevPairs μ) :
    ∃ u : SobolevPair μ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ
        (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) (f (φ n))) atTop
        (nhds (toWeakSpace ℝ
          (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) u.1)) ∧
      (WithLp.ofLp u.1).1 = s := by
  obtain ⟨p, φ, hφ, hweak, hscalar_eq⟩ :=
    exists_weak_subsequence_with_scalar_limit μ f B hB s hscalar
  have hf_subseq (n : ℕ) : f (φ n) ∈ smoothSobolevPairs μ := hf (φ n)
  obtain ⟨u, hu⟩ := weak_limit_smoothSobolevPairs_mem μ (fun n => f (φ n)) p
    hweak hf_subseq
  refine ⟨u, φ, hφ, ?_, ?_⟩
  · simpa [hu] using hweak
  · rw [hu]
    exact hscalar_eq

end

end LOOConcentration.Revision
