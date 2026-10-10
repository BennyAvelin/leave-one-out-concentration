import LOOConcentrationManuscript.Internal.ScalarMomentLawTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

private def realToFinOne : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun x := WithLp.toLp 2 (fun i : Fin 1 => if i = 0 then x else 0)
  map_add' x y := by
    ext i
    fin_cases i
    simp
  map_smul' c x := by
    ext i
    fin_cases i
    simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

private def realToFinTwoFeature : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then x else 0)
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

private def realToFinTwoResponse : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i : Fin 2 => if i = 1 then x else 0)
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

private theorem scalarTransportAtSampleAndTest
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (e : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ κ) (r : ℕ) :
    let ν := μ.map e
    (∀ x : ℝ, ‖e x‖ ^ 2 = x ^ 2) ∧
    Integrable (fun y : EuclideanSpace ℝ κ => ‖y‖ ^ 2) ν ∧
    ((∫ y : EuclideanSpace ℝ κ, ‖y‖ ^ 2 ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    ((Measure.pi fun _ : Fin (r + 2) => μ).map
        (fun D : Fin (r + 2) → ℝ => fun i => e (D i)) =
          Measure.pi fun _ : Fin (r + 2) => ν) ∧
    (∀ D : Fin (r + 2) → ℝ,
      (∑ i : Fin (r + 2), ‖e (D i)‖ ^ 2) =
        ∑ i : Fin (r + 2), (D i) ^ 2) := by
  let ν : Measure (EuclideanSpace ℝ κ) := μ.map e
  have h := scalar_linearIsometry_moment_product_transport μ hSecond e
  rcases h with ⟨hnorm, hinter, hintegral, hlaw, hsum⟩
  refine ⟨hnorm, hinter, hintegral, ?_, ?_⟩
  · exact hlaw (r + 1)
  · intro D
    exact hsum (r + 1) D

theorem realToFinOne_moment_product_consumer
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (r : ℕ) :
    let ν := μ.map realToFinOne
    (∀ x : ℝ, ‖realToFinOne x‖ ^ 2 = x ^ 2) ∧
    Integrable (fun y : EuclideanSpace ℝ (Fin 1) => ‖y‖ ^ 2) ν ∧
    ((∫ y : EuclideanSpace ℝ (Fin 1), ‖y‖ ^ 2 ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    ((Measure.pi fun _ : Fin (r + 2) => μ).map
        (fun D : Fin (r + 2) → ℝ => fun i => realToFinOne (D i)) =
          Measure.pi fun _ : Fin (r + 2) => ν) ∧
    (∀ D : Fin (r + 2) → ℝ,
      (∑ i : Fin (r + 2), ‖realToFinOne (D i)‖ ^ 2) =
        ∑ i : Fin (r + 2), (D i) ^ 2) := by
  exact scalarTransportAtSampleAndTest μ hSecond realToFinOne r

theorem realToFinTwoFeature_moment_product_consumer
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (r : ℕ) :
    let ν := μ.map realToFinTwoFeature
    (∀ x : ℝ, ‖realToFinTwoFeature x‖ ^ 2 = x ^ 2) ∧
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) ν ∧
    ((∫ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ^ 2 ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    ((Measure.pi fun _ : Fin (r + 2) => μ).map
        (fun D : Fin (r + 2) → ℝ => fun i => realToFinTwoFeature (D i)) =
          Measure.pi fun _ : Fin (r + 2) => ν) ∧
    (∀ D : Fin (r + 2) → ℝ,
      (∑ i : Fin (r + 2), ‖realToFinTwoFeature (D i)‖ ^ 2) =
        ∑ i : Fin (r + 2), (D i) ^ 2) := by
  exact scalarTransportAtSampleAndTest μ hSecond realToFinTwoFeature r

theorem realToFinTwoResponse_moment_product_consumer
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (r : ℕ) :
    let ν := μ.map realToFinTwoResponse
    (∀ x : ℝ, ‖realToFinTwoResponse x‖ ^ 2 = x ^ 2) ∧
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) ν ∧
    ((∫ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ^ 2 ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    ((Measure.pi fun _ : Fin (r + 2) => μ).map
        (fun D : Fin (r + 2) → ℝ => fun i => realToFinTwoResponse (D i)) =
          Measure.pi fun _ : Fin (r + 2) => ν) ∧
    (∀ D : Fin (r + 2) → ℝ,
      (∑ i : Fin (r + 2), ‖realToFinTwoResponse (D i)‖ ^ 2) =
        ∑ i : Fin (r + 2), (D i) ^ 2) := by
  exact scalarTransportAtSampleAndTest μ hSecond realToFinTwoResponse r

end LOOConcentration.Manuscript.Internal
