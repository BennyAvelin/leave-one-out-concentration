import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanQuadraticLossGradient
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript
open scoped Topology ContDiff
noncomputable section

private def responseProjectionLinearMap (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (r + 1)) where
  toFun D := WithLp.toLp 2 (fun i => D (i, Sum.inr (0 : Fin 1)))
  map_add' D E := by
    ext i
    rfl
  map_smul' c D := by
    ext i
    rfl

private def responseProjection (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (r + 1)) :=
  LinearMap.toContinuousLinearMap (responseProjectionLinearMap r)

private theorem responseProjection_apply (r : ℕ)
    (D : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) (i : Fin (r + 1)) :
    responseProjection r D i = D (i, Sum.inr 0) := rfl

private theorem responseProjection_norm_apply_le (r : ℕ)
    (D : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    ‖responseProjection r D‖ ≤ ‖D‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [responseProjection_apply, Real.norm_eq_abs, sq_abs]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type]
  exact Finset.sum_le_sum fun i _ =>
    le_add_of_nonneg_left (sq_nonneg (D (i, Sum.inl 0)))

private theorem responseProjection_opNorm_le_one (r : ℕ) :
    ‖responseProjection r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro D
  calc
    ‖responseProjection r D‖ ≤ ‖D‖ := responseProjection_norm_apply_le r D
    _ = 1 * ‖D‖ := by ring

/-- The quadratic response-mean loss is smooth and has the source gradient-growth
bound on the whole feature/response dataset carrier. -/
theorem empiricalMean_quadraticLoss_ambient_regular (r : ℕ) (z : ℝ)
    (D : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    ContDiff ℝ ∞ (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
      (empiricalMean r (WithLp.toLp 2
        (fun i => E (i, Sum.inr (0 : Fin 1)))) - z) ^ 2) ∧
    ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
      (empiricalMean r (WithLp.toLp 2
        (fun i => E (i, Sum.inr (0 : Fin 1)))) - z) ^ 2) D‖ ≤
      2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
  let S := responseProjection r
  let g : EuclideanSpace ℝ (Fin (r + 1)) → ℝ :=
    fun x => (empiricalMean r x - z) ^ 2
  let f : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun x => g (S x)
  have hScalarDifferentiable : Differentiable ℝ g := by
    change Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin (r + 1)) =>
      (empiricalMean r x - z) ^ 2)
    fun_prop [empiricalMean]
  have hAmbientSmooth : ContDiff ℝ ∞ f := by
    change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ
      (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) => (empiricalMean r (S x) - z) ^ 2)
    fun_prop [empiricalMean]
  have hSNorm : ‖S‖ ≤ 1 := by
    simpa [S] using responseProjection_opNorm_le_one r
  have hGradNorm (x : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
      ‖gradient f x‖ ≤ ‖gradient g (S x)‖ * ‖S‖ := by
    have hComp : HasFDerivAt f
        ((fderiv ℝ g (S x)).comp S) x := by
      have hg : HasFDerivAt g (fderiv ℝ g (S x)) (S x) :=
        (hScalarDifferentiable (S x)).hasFDerivAt
      have hSx : HasFDerivAt S S x := S.hasFDerivAt
      have := hg.comp x hSx
      simpa [f, g, Function.comp_def] using this
    have hFDeriv : fderiv ℝ f x = (fderiv ℝ g (S x)).comp S := hComp.fderiv
    calc
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
        rw [gradient]
        exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
      _ = ‖(fderiv ℝ g (S x)).comp S‖ := by rw [hFDeriv]
      _ ≤ ‖fderiv ℝ g (S x)‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖gradient g (S x)‖ * ‖S‖ := by
        have hDualNorm : ‖fderiv ℝ g (S x)‖ = ‖gradient g (S x)‖ := by
          rw [← toDual_gradient]
          exact (InnerProductSpace.toDual ℝ _).norm_map _
        exact congrArg (fun a : ℝ => a * ‖S‖) hDualNorm
  have hScalarBound := empiricalMean_quadraticLoss_gradient_bound r z (S D)
  have hBoundAtS : ‖gradient g (S D)‖ ≤
      2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (2 / ((r + 1 : ℕ) : ℝ)) * ‖S D‖ := by
    simpa [g] using hScalarBound
  constructor
  · simpa [f, g, S, responseProjection, responseProjectionLinearMap] using hAmbientSmooth
  · change ‖gradient f D‖ ≤ _
    calc
      ‖gradient f D‖ ≤ ‖gradient g (S D)‖ * ‖S‖ := hGradNorm D
      _ ≤ ‖gradient g (S D)‖ := by
        calc
          ‖gradient g (S D)‖ * ‖S‖ ≤ ‖gradient g (S D)‖ * 1 :=
            mul_le_mul_of_nonneg_left hSNorm (norm_nonneg _)
          _ = ‖gradient g (S D)‖ := mul_one _
      _ ≤ 2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
        calc
          ‖gradient g (S D)‖ ≤
              2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                (2 / ((r + 1 : ℕ) : ℝ)) * ‖S D‖ := hBoundAtS
          _ ≤ 2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
            calc
              2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                  (2 / ((r + 1 : ℕ) : ℝ)) * ‖S D‖ =
                (2 / ((r + 1 : ℕ) : ℝ)) * ‖S D‖ +
                  2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by ring
              _ ≤ (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ +
                  2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) :=
                add_le_add_left
                  (mul_le_mul_of_nonneg_left (responseProjection_norm_apply_le r D)
                    (by positivity : 0 ≤ (2 / ((r + 1 : ℕ) : ℝ)))) _
              _ = 2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                  (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by ring

end
end LOOConcentration.Manuscript
