import LOOConcentrationRevision.Frozen.Definitions.SobolevPair
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open InnerProductSpace
open scoped ENNReal

/-- Bounded smooth separators supply an actual pair with the same function and gradient.
These are generator premises, to be supplied inside the point-mass consumer. -/
theorem exists_sobolevPair_of_bounded_smooth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) :
    ∃ u : SobolevPair μ, (WithLp.ofLp u.val).1 =ᵐ[μ] F ∧
      (WithLp.ofLp u.val).2 =ᵐ[μ] gradient F := by
  have hgradContinuous : Continuous (gradient F) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp (hF.continuous_fderiv (by simp))
  let hf : MemLp F 2 μ := MemLp.of_bound hF.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbound x).1)
  let hg : MemLp (gradient F) 2 μ := MemLp.of_bound hgradContinuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => (hbound x).2)
  let v : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ) :=
    WithLp.toLp 2 (hf.toLp F, hg.toLp (gradient F))
  have hv : v ∈ smoothSobolevPairs μ := ⟨F, hF, ⟨B, hB, hbound⟩, hf, hg, rfl⟩
  let u : SobolevPair μ := ⟨v, subset_closure hv⟩
  refine ⟨u, ?_, ?_⟩
  · simpa only [u, v, WithLp.ofLp_toLp] using hf.coeFn_toLp
  · simpa only [u, v, WithLp.ofLp_toLp] using hg.coeFn_toLp

end LOOConcentration.Revision
