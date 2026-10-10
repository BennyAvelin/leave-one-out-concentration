import LOOConcentrationManuscript.Internal.KernelDensityFiniteLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

/-- Importing consumer: apply the literal generic KDE finite-loss theorem at
the source kernel, bandwidth, sample, and finite-loss target inputs. -/
theorem genericKDE_finiteLoss_consumer
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (r : ℕ) (X : Fin (r + 1) → ℝ) (g : ℝ → ℝ) (hg : MemLp g 2 volume) :
    Integrable (fun z : ℝ =>
      (g z - ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) ∧
    (∫ z : ℝ,
        (g z - ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) =
      (∫ z : ℝ, g z ^ 2) -
        2 * (∫ z : ℝ, g z * ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) +
        (∫ z : ℝ, (((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) := by
  exact genericKernelDensityEstimator_finite_integrated_loss_expansion
    K h hh hK_nonneg C hK_bound hK_integral r X g hg

end LOOConcentration.Manuscript.Internal
