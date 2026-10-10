import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Rademacher input and the norm consumer

These results use Lebesgue volume on every finite Euclidean coordinate space,
including the zero-dimensional one.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped Gradient

theorem locallyLipschitz_ae_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), DifferentiableAt ℝ F x := by
  have hlocal (n : ℕ) :
      LocallyLipschitzOn (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ)) F :=
    LocallyLipschitzOn.mono hF.locallyLipschitzOn (Set.subset_univ _)
  have hae_ball (n : ℕ) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
        x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ) →
          DifferentiableWithinAt ℝ F
            (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ)) x := by
    have hcompact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ)) :=
      isCompact_closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ)
    obtain ⟨K, hK⟩ :=
      LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact (hlocal n)
    exact hK.ae_differentiableWithinAt_of_mem
  have hae_all : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ∀ n : ℕ,
        x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ) →
          DifferentiableWithinAt ℝ F
            (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ)) x :=
    ae_all_iff.2 hae_ball
  filter_upwards [hae_all] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hxBall : x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) (n : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hn
  have hxClosed : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hn.le
  exact (hx n hxClosed).differentiableAt
    (Metric.closedBall_mem_nhds_of_mem hxBall)

theorem gradient_norm_le_of_lipschitzWith
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) (x : EuclideanSpace ℝ ι) :
    ‖gradient F x‖ ≤ (K : ℝ) := by
  calc
    ‖gradient F x‖ = ‖fderiv ℝ F x‖ := by
      rw [gradient, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
    _ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hF

theorem lipschitzWith_ae_differentiableAt_gradient_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (K : ℝ) := by
  filter_upwards [hF.ae_differentiableAt (μ := volume)] with x hx
  exact ⟨hx, gradient_norm_le_of_lipschitzWith hF x⟩

theorem oneLipschitz_ae_differentiableAt_gradient_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ}
    (hF : LipschitzWith (1 : NNReal) F) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (1 : ℝ) := by
  filter_upwards [lipschitzWith_ae_differentiableAt_gradient_norm_le hF] with x hx
  exact ⟨hx.1, by simpa only [NNReal.coe_one] using hx.2⟩

theorem norm_ae_differentiableAt_gradient_growth
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ ι => ‖y‖) x‖ ≤
          (1 : ℝ) + (0 : ℝ) * ‖x‖ := by
  have hnormLip : LipschitzWith (1 : NNReal)
      (fun y : EuclideanSpace ℝ ι => ‖y‖) := lipschitzWith_one_norm
  filter_upwards [oneLipschitz_ae_differentiableAt_gradient_norm_le hnormLip] with x hx
  exact ⟨hx.1, by simpa only [zero_mul, add_zero] using hx.2⟩

end LOOConcentration.Revision
