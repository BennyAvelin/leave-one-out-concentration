import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open scoped ContDiff

/-- The source quadratic risk polynomial has its exact query-gradient growth
bound on the whole feature/response Euclidean carrier. -/
theorem quadraticMean_responseQuery_polynomial_regular (m c : ℝ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
      (x (Sum.inr (0 : Fin 1)) - m) ^ 2 + c) ∧
    ∀ x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1),
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
        (y (Sum.inr (0 : Fin 1)) - m) ^ 2 + c) x ∧
      ‖gradient (fun y : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
        (y (Sum.inr (0 : Fin 1)) - m) ^ 2 + c) x‖ ≤ 2 * |m| + 2 * ‖x‖ := by
  let S : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) →L[ℝ] ℝ :=
    EuclideanSpace.proj (Sum.inr (0 : Fin 1))
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖x (Sum.inr (0 : Fin 1))‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x (Sum.inr (0 : Fin 1))
  have hSmooth : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
      (S x - m) ^ 2 + c) := by fun_prop
  refine ⟨hSmooth, ?_⟩
  intro x
  have hDeriv : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
      (S y - m) ^ 2 + c) ((2 * (S x - m)) • S) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul] using
      (((S.hasFDerivAt (x := x)).sub_const m).pow 2).add_const c
  refine ⟨hDeriv.differentiableAt, ?_⟩
  change ‖gradient (fun y => (S y - m) ^ 2 + c) x‖ ≤ _
  calc
    ‖gradient (fun y => (S y - m) ^ 2 + c) x‖ =
        ‖fderiv ℝ (fun y => (S y - m) ^ 2 + c) x‖ := by
      rw [gradient]
      exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
    _ = |2 * (S x - m)| * ‖S‖ := by rw [hDeriv.fderiv, norm_smul, Real.norm_eq_abs]
    _ ≤ |2 * (S x - m)| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    _ ≤ 2 * |m| + 2 * ‖x‖ := by
      have hcoord : |S x| ≤ ‖x‖ := by
        change |x (Sum.inr (0 : Fin 1))| ≤ ‖x‖
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (Sum.inr (0 : Fin 1))
      have hresidual : |S x - m| ≤ |S x| + |m| := abs_sub _ _
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith

end LOOConcentration.Manuscript.Internal
