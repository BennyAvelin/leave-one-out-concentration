import LOOConcentrationRevision.Frozen.Bridges.Bounded_truncation_admission
import LOOConcentrationRevision.Frozen.Bridges.LogSobolevConstant_inequality

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Conditional internal assembly on the actual completed-pair carrier.
Its moment and constant-bound obligations must be produced inside the
finite-base-constant source consumer. All retained witnesses remain joint. -/
theorem completed_lsi_and_bounded_truncations_of_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ENNReal) (hC : C < ⊤) (hLC : logSobolevConstant μ ≤ C)
    (hM2 : Integrable (fun x => ‖x‖^2) μ) :
    (∀ u : SobolevPair μ, squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2*C*sobolevEnergy μ u) ∧
    (∀ (F : EuclideanSpace ℝ ι → ℝ), LocallyLipschitz F →
      ∀ (a b R : NNReal),
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) →
        ∃ u : SobolevPair μ,
          ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ]
            (fun x => max (-(R:ℝ)) (min (F x) (R:ℝ))) ∧
          (∀ᵐ x ∂μ, ‖((WithLp.ofLp u.val).2 :
              EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) ∧
          squareEntropy μ (WithLp.ofLp u.val).1 ≤ 2*C*sobolevEnergy μ u) := by
  have hfinite : logSobolevConstant μ < ⊤ := lt_of_le_of_lt hLC hC
  have hAll (u : SobolevPair μ) : squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2*C*sobolevEnergy μ u := by
    have h := logSobolevConstant_inequality μ hfinite u
    exact h.trans (mul_le_mul_left (mul_le_mul_right hLC (2:ENNReal)) (sobolevEnergy μ u))
  refine ⟨hAll, ?_⟩
  intro F hF a b R hgrad
  obtain ⟨u, hs, hg⟩ := bounded_truncation_admission μ hM2 F hF a b R hgrad
  exact ⟨u, hs, hg, hAll u⟩

end LOOConcentration.Revision
