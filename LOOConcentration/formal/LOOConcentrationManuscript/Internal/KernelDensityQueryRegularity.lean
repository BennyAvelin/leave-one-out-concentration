import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- The source C¹ kernel's literal scaled translate has the expected derivative
and the fixed M/h² Lipschitz bound. -/
theorem genericScaledKernel_translate_derivative_and_lipschitz
    (K : ℝ → ℝ) (hK : ContDiff ℝ 1 K) (M : ℝ)
    (hM : ∀ t : ℝ, |deriv K t| ≤ M) (h : ℝ) (hh : 0 < h) (a : ℝ) :
    (∀ x : ℝ, HasDerivAt (fun z : ℝ => K ((z-a)/h)/h)
      (deriv K ((x-a)/h)/h^2) x) ∧
    (∀ x x' : ℝ, |K ((x-a)/h)/h-K ((x'-a)/h)/h| ≤ (M/h^2)*|x-x'|) := by
  have hKM : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hDeriv (x : ℝ) : HasDerivAt (fun z : ℝ => K ((z-a)/h)/h)
      (deriv K ((x-a)/h)/h^2) x := by
    have hInner := ((hasDerivAt_id x).sub_const a).div_const h
    have hRaw := (((hKM ((x-a)/h)).hasDerivAt).comp x hInner).div_const h
    convert hRaw using 1 <;> try rfl
    ring
  refine ⟨hDeriv,?_⟩
  have hMNonneg : 0 ≤ M := (abs_nonneg (deriv K 0)).trans (hM 0)
  have hC : 0 ≤ M/h^2 := div_nonneg hMNonneg (sq_nonneg h)
  let C : NNReal := ⟨M/h^2,hC⟩
  have hDiff : Differentiable ℝ (fun z : ℝ => K ((z-a)/h)/h) :=
    fun x => (hDeriv x).differentiableAt
  have hBound (x : ℝ) : ‖deriv (fun z : ℝ => K ((z-a)/h)/h) x‖₊ ≤ C := by
    apply (NNReal.coe_le_coe).1
    change |deriv (fun z : ℝ => K ((z-a)/h)/h) x| ≤ M/h^2
    rw [(hDeriv x).deriv,abs_div,abs_of_pos (sq_pos_of_pos hh)]
    exact div_le_div_of_nonneg_right (hM _) (sq_nonneg h)
  have hLip := lipschitzWith_of_nnnorm_deriv_le hDiff hBound
  intro x x'
  have hp := hLip.dist_le_mul x x'
  have hcc : (C : ℝ) = M/h^2 := rfl
  rw [Real.dist_eq,Real.dist_eq,hcc] at hp
  exact hp

end LOOConcentration.Manuscript.Internal
