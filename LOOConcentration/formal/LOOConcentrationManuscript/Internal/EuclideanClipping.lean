import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- The manuscript's literal scalar truncator contracts distance and is bounded
by its nonnegative threshold, including threshold zero. -/
theorem scalarClipping_lipschitz_and_bound (b : ℝ) (hb : 0 ≤ b) :
    LipschitzWith 1 (fun x : ℝ => max (min x b) (-b)) ∧
    ∀ x : ℝ, |max (min x b) (-b)| ≤ b := by
  refine ⟨(LipschitzWith.id.min_const b).max_const (-b), ?_⟩
  intro x
  apply abs_le.mpr
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

/-- Coordinate clipping contracts the actual Euclidean norm and has the exact
dimension-dependent radius bound on every finite carrier. -/
theorem euclideanClipping_lipschitz_and_norm
    (ι : Type*) [Fintype ι] (b : ℝ) (hb : 0 ≤ b) :
    let clip := fun D : EuclideanSpace ℝ ι =>
      WithLp.toLp 2 (fun i => max (min (D i) b) (-b))
    LipschitzWith 1 clip ∧
    ∀ D : EuclideanSpace ℝ ι, ‖clip D‖ ≤ b * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  intro clip
  obtain ⟨hLip, hBound⟩ := scalarClipping_lipschitz_and_bound b hb
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro D E
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _hi
    change ‖max (min (D i) b) (-b) - max (min (E i) b) (-b)‖ ^ 2 ≤
      ‖D i - E i‖ ^ 2
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    simpa only [NNReal.coe_one, one_mul] using hLip.norm_sub_le (D i) (E i)
  · intro D
    have hsum : (∑ i : ι, ‖max (min (D i) b) (-b)‖ ^ 2) ≤
        (Fintype.card ι : ℝ) * b ^ 2 := by
      calc
        _ ≤ ∑ _i : ι, b ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          apply (sq_le_sq₀ (norm_nonneg _) hb).2
          simpa only [Real.norm_eq_abs] using hBound (D i)
        _ = _ := by simp
    rw [EuclideanSpace.norm_eq]
    calc
      _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * b ^ 2) := Real.sqrt_le_sqrt hsum
      _ = b * Real.sqrt (Fintype.card ι : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hb, mul_comm]

end LOOConcentration.Manuscript.Internal
