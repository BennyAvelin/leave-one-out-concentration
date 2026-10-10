import LOOConcentrationRevision.Geometry.ProductEuclidean
import LOOConcentrationRevision.FunctionalInequalities.ProductGradientEnergy
import LOOConcentrationRevision.FunctionalInequalities.GeneratorLSIClosure
import LOOConcentrationRevision.FunctionalInequalities.SmoothSquareRegularization
import LOOConcentrationRevision.FunctionalInequalities.FiniteEntropyGeneratorConsumer
import LOOConcentrationRevision.FunctionalInequalities.EntropySquareRegularizationLimit

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The literal section in finite entropy tensorization is the same smooth
coordinate section on the ordered Euclidean carrier. -/
theorem piFin_coordinateSection_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (i : Fin (r + 1)) (tail : Fin r → EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ ι) :
    euclideanCoordinateSection F
      (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i z =
    F (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail))) := by
  rw [euclideanCoordinateSection_productToEuclidean]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.update_insertNth]

/-- Apply the actual base intrinsic LSI to each literal regularized section.
Its smoothness and the same global scalar/gradient bound are produced here. -/
theorem entropy_square_add_epsilon_piFin_section_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) (i : Fin (r + 1))
    (tail : Fin r → EuclideanSpace ℝ ι) :
    LOOConcentration.entropy μ (fun z =>
      (F (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail))))^2 + ε) ≤
    2 * C * ∫ z, ‖gradient (euclideanCoordinateSection F
      (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i) z‖^2 ∂μ := by
  let x := productToEuclidean ((MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))
  let G := euclideanCoordinateSection F x i
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    contDiff_euclideanCoordinateSection F hF x i
  have hGb (z : EuclideanSpace ℝ ι) : |G z| ≤ B ∧ ‖gradient G z‖ ≤ B := by
    constructor
    · exact (hbound _).1
    · exact gradient_euclideanCoordinateSection_norm_le F
        (hF.differentiable (by simp)) B (fun y => (hbound y).2) x i z
  have h := bounded_square_add_epsilon_entropy_le_of_logSobolevConstant_le
    μ C hC hLC G hG B hB hGb ε hε
  change LOOConcentration.entropy μ (fun z => (G z)^2 + ε) ≤ _ at h
  simpa only [G, x, piFin_coordinateSection_eq] using h

/-- Literal section entropy is integrable in the actual remaining-coordinate
law; boundedness supplies all density and mean-log finiteness. -/
private theorem integrable_square_add_epsilon_piFin_section_entropy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B)
    (ε : ℝ) (hε : 0 < ε) (i : Fin (r + 1)) :
    Integrable (fun tail : Fin r → EuclideanSpace ℝ ι =>
      LOOConcentration.entropy μ (fun z =>
        (F (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail))))^2 + ε))
      (Measure.pi fun _ : Fin r => μ) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i
  let g : EuclideanSpace ℝ ι × (Fin r → EuclideanSpace ℝ ι) → ℝ :=
    fun p => (F (productToEuclidean (e.symm p)))^2 + ε
  have hg : Measurable g :=
    ((hF.comp continuous_productToEuclidean.measurable).comp e.symm.measurable).pow_const 2
      |>.add_const ε
  have hgb (p : EuclideanSpace ℝ ι × (Fin r → EuclideanSpace ℝ ι)) :
      g p ≤ B^2 + ε := by
    dsimp [g]
    have hs : (F (productToEuclidean (e.symm p)))^2 ≤ B^2 := by
      rw [sq_le_sq, abs_of_nonneg hB]
      exact hbound _
    exact add_le_add hs le_rfl
  exact LOOConcentration.entropy_section_integrable μ
    (Measure.pi fun _ : Fin r => μ) g (B^2 + ε)
    (add_nonneg (sq_nonneg B) hε.le) hg
    (fun p => add_nonneg (sq_nonneg _) hε.le) hgb

/-- The actual product entropy bound for a regularized bounded generator,
using the same base constant and the same full scalar/gradient witnesses. -/
theorem bounded_product_entropy_square_add_epsilon_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    LOOConcentration.entropy (euclideanProductLaw (κ := Fin (r + 1)) μ)
      (fun x => (F x)^2 + ε) ≤
      2 * C * ∫ x, ‖gradient F x‖^2 ∂euclideanProductLaw (κ := Fin (r + 1)) μ := by
  have hraw : Measurable (fun D : Fin (r + 1) → EuclideanSpace ℝ ι =>
      F (productToEuclidean D)) := hF.continuous.measurable.comp
        continuous_productToEuclidean.measurable
  have hTensor := entropy_square_add_epsilon_piFin_subadditive_of_finite_entropy μ
    (fun D => F (productToEuclidean D)) hraw B ε hB hε.le
    (fun D => by simpa only [Real.norm_eq_abs] using (hbound (productToEuclidean D)).1)
  rw [entropy_euclideanProductLaw μ (fun x => (F x)^2 + ε)
    ((hF.continuous.measurable.pow_const 2).add_const ε)]
  refine hTensor.trans ?_
  calc
    _ ≤ ∑ i : Fin (r + 1), 2 * C *
        ∫ tail : Fin r → EuclideanSpace ℝ ι,
          ∫ z, ‖gradient (euclideanCoordinateSection F
            (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i) z‖^2
            ∂μ ∂Measure.pi fun _ : Fin r => μ := by
      apply Finset.sum_le_sum
      intro i _
      have hEnt := integrable_square_add_epsilon_piFin_section_entropy μ F
        hF.continuous.measurable B hB (fun x => (hbound x).1) ε hε i
      have hEnergy := integrable_piFin_section_gradient_energy r μ F hF B hB
        (fun x => (hbound x).2) i
      have h := integral_mono hEnt (hEnergy.const_mul (2 * C))
        (fun tail => entropy_square_add_epsilon_piFin_section_le
          μ C hC hLC F hF B hB hbound ε hε i tail)
      rwa [integral_const_mul] at h
    _ = 2 * C *
        ∑ i : Fin (r + 1), ∫ tail : Fin r → EuclideanSpace ℝ ι,
          ∫ z, ‖gradient (euclideanCoordinateSection F
            (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i) z‖^2
            ∂μ ∂Measure.pi fun _ : Fin r => μ := by rw [Finset.mul_sum]
    _ = _ := congrArg (fun t : ℝ => 2 * C * t)
      (integral_sum_euclideanCoordinateSection_gradient_energy r μ F hF B hB
        (fun x => (hbound x).2))

/-- The uniform bound is produced before removing epsilon on the same density. -/
theorem bounded_product_entropy_square_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) :
    LOOConcentration.entropy (euclideanProductLaw (κ := Fin (r + 1)) μ)
      (fun x => (F x)^2) ≤
      2 * C * ∫ x, ‖gradient F x‖^2 ∂euclideanProductLaw (κ := Fin (r + 1)) μ := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  exact entropy_square_le_of_all_positive_regularizations ν F hF.continuous.measurable
    B hB (fun x => (hbound x).1) (2 * C * ∫ x, ‖gradient F x‖^2 ∂ν)
    (fun ε hε => bounded_product_entropy_square_add_epsilon_le r μ C hC hLC
      F hF B hB hbound ε hε)

/-- The literal completed-pair product constant is at most the intrinsic base
constant. The product generator producer is discharged internally. -/
theorem logSobolevConstant_euclideanProductLaw_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    logSobolevConstant ν ≤ logSobolevConstant μ := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  let C := (logSobolevConstant μ).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal C := by
    change logSobolevConstant μ ≤ ENNReal.ofReal (logSobolevConstant μ).toReal
    rw [ENNReal.ofReal_toReal hfinite.ne]
  have h := logSobolevConstant_le_of_bounded_generator_bound ν C hC
    (fun F hF B hB hbound => bounded_product_entropy_square_le r μ C hC hLC
      F hF B hB hbound)
  simpa only [C, ENNReal.ofReal_toReal hfinite.ne] using h

/-- Every actual completed product pair satisfies the same base-constant LSI,
including zero energy and zero-dimensional observation carriers. -/
theorem all_pairs_lsi_euclideanProductLaw
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (u : let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
      let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
      SobolevPair ν) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    squareEntropy ν (WithLp.ofLp u.val).1 ≤ 2 * logSobolevConstant μ * sobolevEnergy ν u := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  let C := (logSobolevConstant μ).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal C := by
    change logSobolevConstant μ ≤ ENNReal.ofReal (logSobolevConstant μ).toReal
    rw [ENNReal.ofReal_toReal hfinite.ne]
  have h := all_pairs_lsi_of_bounded_generator_bound ν C hC
    (fun F hF B hB hbound => bounded_product_entropy_square_le r μ C hC hLC
      F hF B hB hbound) u
  simpa only [C, ENNReal.ofReal_toReal hfinite.ne] using h

end LOOConcentration.Revision
