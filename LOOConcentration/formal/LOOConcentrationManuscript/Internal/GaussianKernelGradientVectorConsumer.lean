import LOOConcentrationManuscript.Internal.GaussianKernelGradientCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- The actual ambient Gaussian gradient equals the whole paired source coefficient vector. -/
theorem gaussianKernel_predictor_ambient_gradient_eq_coefficient_vector
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (x : ℝ)
    (D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1))) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let B := (∑ i : Fin (r+1), Kh (x-D (i,Sum.inl 0)))+(r+1 : ℝ)*δ
    let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
      (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
        ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
    let G : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) :=
      WithLp.toLp 2 (fun q => Sum.elim
        (fun _ : Fin 1 => deriv Kh (x-D (q.1,Sum.inl 0))/B*(-D (q.1,Sum.inr 0)+T D))
        (fun _ : Fin 1 => Kh (x-D (q.1,Sum.inl 0))/B) q.2)
    gradient T D = G := by
  intro Kh B T G
  apply PiLp.ext
  rintro ⟨j,s⟩
  cases s with
  | inl k =>
    rw [Fin.eq_zero k]
    exact (gaussianKernel_predictor_ambient_gradient_coordinates h δ hh hδ r x D j).1
  | inr k =>
    rw [Fin.eq_zero k]
    exact (gaussianKernel_predictor_ambient_gradient_coordinates h δ hh hδ r x D j).2

end LOOConcentration.Manuscript.Internal
