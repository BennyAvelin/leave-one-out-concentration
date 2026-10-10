import LOOConcentrationManuscript.Internal.KernelDensityQueryRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- The literal KDE is M/h²-Lipschitz in the query uniformly in sample size and
the whole raw sample; the constant is inherited from the same scaled kernel. -/
theorem genericKDE_actual_query_lipschitz
    (K : ℝ → ℝ) (hK : ContDiff ℝ 1 K) (M : ℝ)
    (hM : ∀ t : ℝ, |deriv K t| ≤ M) (h : ℝ) (hh : 0 < h) :
    ∀ (r : ℕ) (X : Fin (r+1) → ℝ) (x x' : ℝ),
      let f := fun z : ℝ => (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((z-X j)/h)/h
      |f x-f x'| ≤ (M/h^2)*|x-x'| := by
  intro r X x x' f
  have hN : 0 < (r+1 : ℝ) := by positivity
  have hTerm (j : Fin (r+1)) :
      |K ((x-X j)/h)/h-K ((x'-X j)/h)/h| ≤ (M/h^2)*|x-x'| :=
    (genericScaledKernel_translate_derivative_and_lipschitz K hK M hM h hh (X j)).2 x x'
  have hSum : |(∑ j : Fin (r+1), K ((x-X j)/h)/h)-
      (∑ j : Fin (r+1), K ((x'-X j)/h)/h)| ≤ (r+1 : ℝ)*((M/h^2)*|x-x'|) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (r+1), |K ((x-X j)/h)/h-K ((x'-X j)/h)/h| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (r+1), (M/h^2)*|x-x'| := Finset.sum_le_sum (fun j _ => hTerm j)
      _ = _ := by simp
  change |(r+1 : ℝ)⁻¹*_-(r+1 : ℝ)⁻¹*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ (r+1 : ℝ)⁻¹*((r+1 : ℝ)*((M/h^2)*|x-x'|)) :=
      mul_le_mul_of_nonneg_left hSum (inv_nonneg.mpr hN.le)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hN.ne',one_mul]

end LOOConcentration.Manuscript.Internal
