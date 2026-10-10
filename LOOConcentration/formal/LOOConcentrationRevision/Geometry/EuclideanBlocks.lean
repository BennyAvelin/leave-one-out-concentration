import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
namespace LOOConcentration.Revision

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

private def blockCoordinates (i : κ) (v : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (κ × ι) :=
  WithLp.toLp (2 : ENNReal) (fun q => if q.1 = i then v q.2 else 0)

/-- Isometrically include a single observation block in the ordered product. -/
noncomputable def euclideanBlockInclusion (i : κ) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (κ × ι) where
  toLinearMap :=
    { toFun := blockCoordinates i
      map_add' := by
        intro v w
        ext q
        rcases q with ⟨j, a⟩
        by_cases hji : j = i <;> simp [blockCoordinates, hji]
      map_smul' := by
        intro c v
        ext q
        rcases q with ⟨j, a⟩
        by_cases hji : j = i <;> simp [blockCoordinates, hji] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [blockCoordinates, Fintype.sum_prod_type]

private theorem blockInclusion_single (i : κ) (a : ι) :
    euclideanBlockInclusion i (EuclideanSpace.single a (1 : ℝ)) =
      EuclideanSpace.single (i, a) (1 : ℝ) := by
  ext q
  rcases q with ⟨j, b⟩
  by_cases hji : j = i
  · subst j
    simp [euclideanBlockInclusion, blockCoordinates]
  · simp [euclideanBlockInclusion, blockCoordinates, hji]

/-- Scalar derivative energy is exactly the sum of its coordinate-block energies. -/
theorem sum_euclideanBlock_composition_norm_sq
    (L : EuclideanSpace ℝ (κ × ι) →L[ℝ] ℝ) :
    (∑ i : κ, ‖L.comp (euclideanBlockInclusion i).toContinuousLinearMap‖ ^ 2) =
      ‖L‖ ^ 2 := by
  have hblock (i : κ) :
      ‖L.comp (euclideanBlockInclusion i).toContinuousLinearMap‖ ^ 2 =
        ∑ a : ι, (L (euclideanBlockInclusion i
          (EuclideanSpace.basisFun ι ℝ a))) ^ 2 := by
    simpa only [OrthonormalBasis.norm_dual, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using
      (OrthonormalBasis.norm_dual (EuclideanSpace.basisFun ι ℝ)
        (L.comp (euclideanBlockInclusion i).toContinuousLinearMap))
  calc
    _ = ∑ i : κ, ∑ a : ι,
        (L (euclideanBlockInclusion i (EuclideanSpace.basisFun ι ℝ a))) ^ 2 := by
      exact Finset.sum_congr rfl (fun i _ => hblock i)
    _ = ∑ i : κ, ∑ a : ι,
        (L (EuclideanSpace.basisFun (κ × ι) ℝ (i, a))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [EuclideanSpace.basisFun_apply, blockInclusion_single,
        EuclideanSpace.basisFun_apply]
    _ = ∑ q : κ × ι, (L (EuclideanSpace.basisFun (κ × ι) ℝ q)) ^ 2 := by
      rw [← Fintype.sum_prod_type']
    _ = ‖L‖ ^ 2 := (OrthonormalBasis.norm_dual
      (EuclideanSpace.basisFun (κ × ι) ℝ) L).symm

/-- The actual coordinate section fixes every other block at the same base point. -/
noncomputable def euclideanCoordinateSection
    (F : EuclideanSpace ℝ (κ × ι) → ℝ)
    (x : EuclideanSpace ℝ (κ × ι)) (i : κ) : EuclideanSpace ℝ ι → ℝ :=
  fun v => F (x + euclideanBlockInclusion i
    (v - WithLp.toLp 2 (fun a => x (i, a))))

private theorem norm_gradient_eq_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] (g : E → ℝ) (y : E) :
      ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

omit [DecidableEq ι] in
/-- Every actual coordinate section has the same smoothness as the full test. -/
theorem contDiff_euclideanCoordinateSection
    (F : EuclideanSpace ℝ (κ × ι) → ℝ) {n : WithTop ℕ∞}
    (hF : ContDiff ℝ n F) (x : EuclideanSpace ℝ (κ × ι)) (i : κ) :
    ContDiff ℝ n (euclideanCoordinateSection F x i) := by
  let v₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun a => x (i, a))
  let I := (euclideanBlockInclusion (ι := ι) i).toContinuousLinearMap
  have hemb : ContDiff ℝ n (fun v => x + I (v - v₀)) := by
    convert (contDiff_const.add (I.contDiff.comp (contDiff_id.sub contDiff_const))) using 1 <;> rfl
  exact hF.comp hemb

omit [DecidableEq ι] in
/-- The derivative of the actual section is the corresponding block restriction. -/
theorem fderiv_euclideanCoordinateSection
    (F : EuclideanSpace ℝ (κ × ι) → ℝ)
    (x : EuclideanSpace ℝ (κ × ι)) (i : κ) (v : EuclideanSpace ℝ ι)
    (hF : DifferentiableAt ℝ F (x + euclideanBlockInclusion i
      (v - WithLp.toLp 2 (fun a => x (i, a))))) :
    fderiv ℝ (euclideanCoordinateSection F x i) v =
      (fderiv ℝ F (x + euclideanBlockInclusion i
        (v - WithLp.toLp 2 (fun a => x (i, a))))).comp
          (euclideanBlockInclusion i).toContinuousLinearMap := by
  let v₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun a => x (i, a))
  let I := (euclideanBlockInclusion (ι := ι) i).toContinuousLinearMap
  have hemb : HasFDerivAt (fun w => x + I (w - v₀)) I v := by
    convert ((I.hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const v₀)).const_add x)
      using 1 <;> rfl
  exact (hF.hasFDerivAt.comp v hemb).fderiv

omit [DecidableEq ι] in
/-- A common full-gradient bound supplies the same bound to every actual section. -/
theorem gradient_euclideanCoordinateSection_norm_le
    (F : EuclideanSpace ℝ (κ × ι) → ℝ) (hF : Differentiable ℝ F)
    (B : ℝ) (hbound : ∀ y, ‖gradient F y‖ ≤ B)
    (x : EuclideanSpace ℝ (κ × ι)) (i : κ) (v : EuclideanSpace ℝ ι) :
    ‖gradient (euclideanCoordinateSection F x i) v‖ ≤ B := by
  rw [norm_gradient_eq_fderiv, fderiv_euclideanCoordinateSection F x i v (hF _)]
  calc
    _ ≤ ‖fderiv ℝ F (x + euclideanBlockInclusion i
        (v - WithLp.toLp 2 (fun a => x (i, a))))‖ *
        ‖(euclideanBlockInclusion i).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F (x + euclideanBlockInclusion i
        (v - WithLp.toLp 2 (fun a => x (i, a))))‖ * 1 :=
      mul_le_mul_of_nonneg_left (euclideanBlockInclusion i).norm_toContinuousLinearMap_le (norm_nonneg _)
    _ ≤ B := by
      rw [mul_one, ← norm_gradient_eq_fderiv]
      exact hbound _

/-- The squared gradients of the actual sections sum to the full squared gradient.
No positive-dimensional assumption is needed. -/
theorem sum_euclideanCoordinateSection_gradient_norm_sq
    (F : EuclideanSpace ℝ (κ × ι) → ℝ)
    (x : EuclideanSpace ℝ (κ × ι)) (hF : DifferentiableAt ℝ F x) :
    (∑ i : κ, ‖gradient (euclideanCoordinateSection F x i)
      (WithLp.toLp 2 (fun a => x (i, a)))‖ ^ 2) = ‖gradient F x‖ ^ 2 := by
  have hsection (i : κ) : fderiv ℝ (euclideanCoordinateSection F x i)
      (WithLp.toLp 2 (fun a => x (i, a))) =
      (fderiv ℝ F x).comp (euclideanBlockInclusion i).toContinuousLinearMap := by
    let v₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun a => x (i, a))
    let I := (euclideanBlockInclusion (ι := ι) i).toContinuousLinearMap
    have hemb : HasFDerivAt (fun v => x + I (v - v₀)) I v₀ := by
      convert ((I.hasFDerivAt.comp v₀
        ((hasFDerivAt_id v₀).sub_const v₀)).const_add x) using 1 <;> rfl
    have hFemb : HasFDerivAt F (fderiv ℝ F x) (x + I (v₀ - v₀)) := by
      simpa using hF.hasFDerivAt
    have hcomp := hFemb.comp v₀ hemb
    change fderiv ℝ (F ∘ fun v => x + I (v - v₀)) v₀ = (fderiv ℝ F x).comp I
    exact hcomp.fderiv
  simp_rw [norm_gradient_eq_fderiv, hsection]
  exact sum_euclideanBlock_composition_norm_sq _

end LOOConcentration.Revision
