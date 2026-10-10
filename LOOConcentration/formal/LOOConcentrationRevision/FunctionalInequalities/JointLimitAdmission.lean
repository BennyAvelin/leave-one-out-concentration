import LOOConcentrationRevision.FunctionalInequalities.WeakL2Compactness
import LOOConcentrationRevision.FunctionalInequalities.GradientConstraint

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Internally produce the weak subsequence and retain both the prescribed scalar
and the exact gradient majorant in the SAME admitted joint pair. -/
theorem exists_sobolevPair_of_bounded_generators_with_gradient_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
    (B : ℝ) (hB : ∀ n, ‖f n‖ ≤ B) (hf : ∀ n, f n ∈ smoothSobolevPairs μ)
    (s : Lp ℝ 2 μ)
    (hscalar : Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop (nhds s))
    (q : EuclideanSpace ℝ ι → ℝ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖(WithLp.ofLp (f n)).2 x‖ ≤ q x + err n) :
    ∃ u : SobolevPair μ, (WithLp.ofLp u.val).1 = s ∧
      ∀ᵐ x ∂μ, ‖(WithLp.ofLp u.val).2 x‖ ≤ q x := by
  obtain ⟨p, φ, hφ, hweak, hs⟩ :=
    exists_weak_subsequence_with_scalar_limit μ f B hB s hscalar
  have he : Tendsto (fun n => err (φ n)) atTop (nhds 0) :=
    herr.comp hφ.tendsto_atTop
  obtain ⟨u, hu, hg⟩ := weak_smooth_pair_gradient_bound μ
    (fun n => f (φ n)) p hweak (fun n => hf (φ n)) q (fun n => err (φ n))
    he (fun n => hbound (φ n))
  refine ⟨u, ?_, hg⟩
  rw [hu]
  exact hs

end LOOConcentration.Revision
