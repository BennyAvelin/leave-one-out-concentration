import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ContinuousLinearMap

/-- Quotient differentiation on an arbitrary real normed domain, with the
source positive denominator condition. -/
theorem positiveDenominator_quotient_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E → ℝ) (DA DB : E →L[ℝ] ℝ) (z : E)
    (hA : HasFDerivAt A DA z) (hB : HasFDerivAt B DB z) (hpos : 0 < B z) :
    HasFDerivAt (fun y => A y / B y)
      ((B z ^ 2)⁻¹ • (B z • DA - A z • DB)) z := by
  have hi := (hasDerivAt_inv hpos.ne').hasFDerivAt.comp z hB
  have hm := hA.mul hi
  convert! hm using 1
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, sub_apply,
    smul_eq_mul, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply]
  field_simp
  ring

end LOOConcentration.Manuscript.Internal
