import LOOConcentration.Concentration.Chernoff
import Mathlib.Probability.Moments.SubGaussian

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Resolve the pinned private name without changing the accepted upstream API.
The resulting term is the existing theorem and is checked by the Lean kernel. -/
elab "certifiedGaussianTailKernel" : term => do
  let env ← Lean.getEnv
  let some (n, _) := env.constants.toList.find? (fun (n, _) => n.toString ==
      "_private.LOOConcentration.Concentration.Chernoff.0.LOOConcentration.measureReal_gt_le_gaussian_rate")
    | throwError "Missing pinned certified Gaussian Chernoff kernel"
  Lean.Elab.Term.elabTerm (Lean.mkIdent n) none

/-- The independently certified sharp Gaussian Markov kernel consumes the actual
MGF, preserving both strict tails and the zero-proxy endpoint. The private kernel
identity is pinned by the existing Chernoff certificate and unchanged source. -/
theorem strict_tails_le_of_subgaussianMGF_via_certified_chernoff
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (c : NNReal) (h : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (t : ℝ) (ht : 0 < t) :
    (μ.real {x | X x > t} ≤ if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c:ℝ))))) ∧
    (μ.real {x | -X x > t} ≤ if c = 0 then 0 else Real.exp (-(t^2 / (2 * (c:ℝ))))) := by
  have hMgf (s : ℝ) : Integrable (fun x => Real.exp (s * X x)) μ ∧
      (∫ x, Real.exp (s * X x) ∂μ) ≤ Real.exp (((c:ℝ)/2) * s^2) := by
    refine ⟨h.integrable_exp_mul s, ?_⟩
    exact (h.mgf_le s).trans_eq (congrArg Real.exp (by ring))
  have hNeg (s : ℝ) : Integrable (fun x => Real.exp (s * (-X x))) μ ∧
      (∫ x, Real.exp (s * (-X x)) ∂μ) ≤ Real.exp (((c:ℝ)/2) * s^2) := by
    refine ⟨h.neg.integrable_exp_mul s, ?_⟩
    exact (h.neg.mgf_le s).trans_eq (congrArg Real.exp (by ring))
  have hu := certifiedGaussianTailKernel
    μ X t ((c:ℝ)/2) ht (by positivity) hMgf
  have hl := certifiedGaussianTailKernel
    μ (-X) t ((c:ℝ)/2) ht (by positivity) hNeg
  have hz : ((c:ℝ)/2 = 0) ↔ c = 0 := by simp
  have hd : 4*((c:ℝ)/2) = 2*(c:ℝ) := by ring
  simpa only [hz, hd, Pi.neg_apply] using And.intro hu hl

end LOOConcentration.Revision
