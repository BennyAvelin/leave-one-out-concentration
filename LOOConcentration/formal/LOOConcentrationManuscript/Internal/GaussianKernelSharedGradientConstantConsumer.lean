import LOOConcentrationManuscript.Internal.GaussianKernelActualGradientNormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- A single strictly positive constant is fixed by h and δ before every
sample size, query, and raw dataset in the manuscript's actual gradient bound. -/
theorem gaussianKernel_source_shared_gradient_constant
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (x : ℝ)
      (D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1))),
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
        (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
          ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
      ‖gradient T D‖ ≤ C/Real.sqrt (r+1 : ℝ)+C*‖D‖/(r+1 : ℝ) := by
  let W := (Real.sqrt (2*Real.pi))⁻¹
  let Cy := (W/h)/δ
  let Cx := (W/h^2)/δ
  let Cf := Cx*(1+Cy)
  let C := Cy+Cf
  have hCy : 0 < Cy := by dsimp [Cy,W]; positivity
  have hCx : 0 ≤ Cx := by dsimp [Cx,W]; positivity
  have hCf : 0 ≤ Cf := mul_nonneg hCx (by positivity)
  have hC : 0 < C := add_pos_of_pos_of_nonneg hCy hCf
  have hCyC : Cy ≤ C := le_add_of_nonneg_right hCf
  have hCfC : Cf ≤ C := le_add_of_nonneg_left hCy.le
  refine ⟨C,hC,?_⟩
  intro r x D Kh T
  have hBound := gaussianKernel_predictor_ambient_gradient_norm_bound h δ hh hδ r x D
  change ‖gradient T D‖ ≤ Cy/Real.sqrt (r+1 : ℝ)+Cf*‖D‖/(r+1 : ℝ) at hBound
  apply hBound.trans
  exact add_le_add
    (div_le_div_of_nonneg_right hCyC (Real.sqrt_nonneg _))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCfC (norm_nonneg _)) (by positivity))

end LOOConcentration.Manuscript.Internal
