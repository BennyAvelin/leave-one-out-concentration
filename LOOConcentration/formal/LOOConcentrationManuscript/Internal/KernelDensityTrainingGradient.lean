import LOOConcentrationManuscript.Internal.KernelDensityQueryRegularityConsumer
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

private theorem kde_feature_energy_le_whole_norm_sq (r : ℕ)
    (v : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    (∑ j : Fin (r + 1), (v (j, Sum.inl 0)) ^ 2) ≤ ‖v‖ ^ 2 := by
  calc
    (∑ j : Fin (r + 1), (v (j, Sum.inl 0)) ^ 2) ≤
        ∑ j : Fin (r + 1),
          ((v (j, Sum.inl 0)) ^ 2 + (v (j, Sum.inr 0)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_add_of_nonneg_right (sq_nonneg _)
    _ = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fintype.sum_prod_type, Fintype.sum_sum_type]

/-- The literal KDE on the full paired data carrier has the source constant
`M/(h²√N)`. The query and every feature are unrestricted; the norm on the
right is the whole paired Euclidean norm. -/
theorem genericKDE_actual_training_regular
    (K : ℝ → ℝ) (hK : ContDiff ℝ 1 K) (M : ℝ)
    (hM : ∀ t : ℝ, |deriv K t| ≤ M) (h : ℝ) (hh : 0 < h) :
    ∀ (r : ℕ) (z : ℝ),
      ContDiff ℝ 1
        (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
          (r + 1 : ℝ)⁻¹ *
            ∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h) ∧
      ∀ E F : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)),
        |((r + 1 : ℝ)⁻¹ *
            ∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h) -
          ((r + 1 : ℝ)⁻¹ *
            ∑ j : Fin (r + 1), K ((z - F (j, Sum.inl 0)) / h) / h)| ≤
          M / (h ^ 2 * Real.sqrt (r + 1 : ℝ)) * ‖E - F‖ := by
  classical
  have hM_nonneg : 0 ≤ M := (abs_nonneg (deriv K 0)).trans (hM 0)
  intro r z
  let f : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ := fun E =>
    (r + 1 : ℝ)⁻¹ *
      ∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h
  constructor
  · dsimp [f]
    have hCoordinate (j : Fin (r + 1)) :
        ContDiff ℝ 1 (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
          E (j, Sum.inl 0)) := by
      exact (PiLp.proj (2 : ENNReal) (𝕜 := ℝ)
        (β := fun _ : (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) => ℝ)
        (j, Sum.inl 0)).contDiff
    have hAtom (j : Fin (r + 1)) :
        ContDiff ℝ 1 (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
          K ((z - E (j, Sum.inl 0)) / h) / h) := by
      have hPreArgument : ContDiff ℝ 1
          (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
            z - E (j, Sum.inl 0)) := contDiff_const.sub (hCoordinate j)
      have hArgument := hPreArgument.div_const h
      exact (hK.comp hArgument).div_const h
    have hSum : ContDiff ℝ 1
        (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
          ∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h) := by
      exact ContDiff.sum (fun j _ => hAtom j)
    have hConstant : ContDiff ℝ 1
        (fun _ : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) => (r + 1 : ℝ)⁻¹) :=
      contDiff_const
    exact hConstant.mul hSum
  · intro E F
    let N : ℝ := (r + 1 : ℝ)
    let v : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) := E - F
    have hN : 0 < N := by dsimp [N]; positivity
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hInv : 0 ≤ N⁻¹ := (inv_nonneg.mpr hN.le)
    have hCoeff : 0 ≤ M / h ^ 2 := div_nonneg hM_nonneg (sq_nonneg h)
    have hCoeffEq : N⁻¹ * (M / h ^ 2) * Real.sqrt N =
        M / (h ^ 2 * Real.sqrt N) := by
      dsimp [N]
      field_simp [ne_of_gt (show 0 < (r + 1 : ℝ) by positivity), hsqrt.ne', hh.ne']
      rw [Real.sq_sqrt hN.le]
      ring
    have hCS :
        (∑ j : Fin (r + 1), |v (j, Sum.inl 0)|) ^ 2 ≤
          (∑ j : Fin (r + 1), (v (j, Sum.inl 0)) ^ 2) * N := by
      simpa [N, sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (r + 1)))
          (fun j => |v (j, Sum.inl 0)|) (fun _ => (1 : ℝ)))
    have hCS' :
        (∑ j : Fin (r + 1), |v (j, Sum.inl 0)|) ^ 2 ≤
          (‖v‖ ^ 2) * N :=
      hCS.trans (mul_le_mul_of_nonneg_right (kde_feature_energy_le_whole_norm_sq r v) hN.le)
    have hSumNonneg : 0 ≤ ∑ j : Fin (r + 1), |v (j, Sum.inl 0)| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have hSumBound :
        (∑ j : Fin (r + 1), |v (j, Sum.inl 0)|) ≤ Real.sqrt N * ‖v‖ := by
      have hsquare : (Real.sqrt N * ‖v‖) ^ 2 = N * ‖v‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN.le]
      have hRhsNonneg : 0 ≤ Real.sqrt N * ‖v‖ := mul_nonneg hsqrt.le (norm_nonneg _)
      nlinarith [hCS', hsquare]
    have hAtom (j : Fin (r + 1)) :
        |K ((z - E (j, Sum.inl 0)) / h) / h -
          K ((z - F (j, Sum.inl 0)) / h) / h| ≤
          (M / h ^ 2) * |v (j, Sum.inl 0)| := by
      have hScaled :=
        (genericScaledKernel_translate_derivative_and_lipschitz K hK M hM h hh 0).2
          (z - E (j, Sum.inl 0)) (z - F (j, Sum.inl 0))
      have hArg :
          |(z - E (j, Sum.inl 0)) - (z - F (j, Sum.inl 0))| =
            |v (j, Sum.inl 0)| := by
        change |(z - E (j, Sum.inl 0)) - (z - F (j, Sum.inl 0))| =
          |E (j, Sum.inl 0) - F (j, Sum.inl 0)|
        rw [show (z - E (j, Sum.inl 0)) - (z - F (j, Sum.inl 0)) =
          -(E (j, Sum.inl 0) - F (j, Sum.inl 0)) by ring, abs_neg]
      simpa only [sub_zero, hArg] using hScaled
    have hSumDiff :
        |(∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h) -
          (∑ j : Fin (r + 1), K ((z - F (j, Sum.inl 0)) / h) / h)| ≤
          ∑ j : Fin (r + 1),
            |K ((z - E (j, Sum.inl 0)) / h) / h -
              K ((z - F (j, Sum.inl 0)) / h) / h| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    have hSumAtoms :
        (∑ j : Fin (r + 1),
            |K ((z - E (j, Sum.inl 0)) / h) / h -
              K ((z - F (j, Sum.inl 0)) / h) / h|) ≤
          (M / h ^ 2) * ∑ j : Fin (r + 1), |v (j, Sum.inl 0)| := by
      calc
        _ ≤ ∑ j : Fin (r + 1), (M / h ^ 2) * |v (j, Sum.inl 0)| :=
          Finset.sum_le_sum fun j _ => hAtom j
        _ = _ := by rw [← Finset.mul_sum]
    have hTarget :
        |f E - f F| ≤ M / (h ^ 2 * Real.sqrt N) * ‖E - F‖ := by
      dsimp [f]
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hN)]
      calc
        N⁻¹ * |(∑ j : Fin (r + 1), K ((z - E (j, Sum.inl 0)) / h) / h) -
            (∑ j : Fin (r + 1), K ((z - F (j, Sum.inl 0)) / h) / h)| ≤
            N⁻¹ * ((M / h ^ 2) * ∑ j : Fin (r + 1), |v (j, Sum.inl 0)|) :=
          mul_le_mul_of_nonneg_left (hSumDiff.trans hSumAtoms) hInv
        _ ≤ N⁻¹ * ((M / h ^ 2) * (Real.sqrt N * ‖v‖)) := by
          gcongr
        _ = (N⁻¹ * (M / h ^ 2) * Real.sqrt N) * ‖v‖ := by ring
        _ = M / (h ^ 2 * Real.sqrt N) * ‖E - F‖ := by rw [hCoeffEq]
    simpa [N, v, Real.dist_eq] using hTarget

end LOOConcentration.Manuscript.Internal
