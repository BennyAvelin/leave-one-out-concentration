import LOOConcentrationRevision.Geometry.ProductEuclidean

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

private theorem norm_gradient_eq_fderiv_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖fderiv ℝ g x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

private noncomputable def rawBlockEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (i : Fin (r + 1)) (x : EuclideanSpace ℝ (Fin (r + 1) × ι)) : ℝ :=
  ‖(fderiv ℝ F x).comp
    (euclideanBlockInclusion (κ := Fin (r + 1)) i).toContinuousLinearMap‖ ^ 2

private theorem update_piFinSuccAbove_symm
    {E : Type*} [MeasurableSpace E] {r : ℕ}
    (i : Fin (r + 1)) (a b : E) (tail : Fin r → E) :
  Function.update
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i).symm
          (a, tail)) i b =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i).symm
        (b, tail) := by
  let α : Fin (r + 1) → Type _ := fun _ => E
  let tail' : ∀ j : Fin r, α (i.succAbove j) := fun j => tail j
  change Function.update (Fin.insertNth (α := α) i a tail') i b =
    Fin.insertNth (α := α) i b tail'
  exact Fin.update_insertNth (α := α) i a b tail'

/-- A smooth generator with bounded gradient has integrable squared gradient
on every actual coordinate section. -/
theorem integrable_euclideanCoordinateSection_gradient_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin (r + 1) × ι)) (i : Fin (r + 1)) :
    Integrable (fun z =>
      ‖gradient (euclideanCoordinateSection F x i) z‖ ^ 2) μ := by
  let G := euclideanCoordinateSection F x i
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    contDiff_euclideanCoordinateSection F hF x i
  have hgrad : Continuous (fun z => gradient G z) := by
    change Continuous (fun z => (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ ι)).symm (fderiv ℝ G z))
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hG.continuous_fderiv (by simp))
  have hmeas : Measurable (fun z => ‖gradient G z‖ ^ 2) := by
    exact (hgrad.norm.pow 2).measurable
  have hle (z : EuclideanSpace ℝ ι) :
      ‖‖gradient G z‖ ^ 2‖ ≤ B ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hz := gradient_euclideanCoordinateSection_norm_le F
      (hF.differentiable (by simp))
      B hbound x i z
    exact (sq_le_sq₀ (norm_nonneg _) hB).2 hz
  exact Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 2)
    (Filter.Eventually.of_forall hle)

private theorem rawBlockEnergy_le_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B)
    (i : Fin (r + 1)) (x : EuclideanSpace ℝ (Fin (r + 1) × ι)) :
    rawBlockEnergy F i x ≤ B ^ 2 := by
  have hcomp :
      ‖(fderiv ℝ F x).comp
        (euclideanBlockInclusion (κ := Fin (r + 1)) i).toContinuousLinearMap‖ ≤ B := by
    calc
      _ ≤ ‖fderiv ℝ F x‖ *
          ‖(euclideanBlockInclusion (κ := Fin (r + 1)) i).toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ F x‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (euclideanBlockInclusion i).norm_toContinuousLinearMap_le (norm_nonneg _)
      _ ≤ B := by
        rw [mul_one, ← norm_gradient_eq_fderiv_local]
        exact hbound x
  dsimp [rawBlockEnergy]
  exact (sq_le_sq₀ (norm_nonneg _) hB).2 hcomp

private theorem rawBlockEnergy_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (i : Fin (r + 1)) :
    Continuous (rawBlockEnergy F i) := by
  have hderiv : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hcomp : Continuous (fun x => (fderiv ℝ F x).comp
      (euclideanBlockInclusion (κ := Fin (r + 1)) i).toContinuousLinearMap) := by
    exact (isBoundedBilinearMap_comp (𝕜 := ℝ)).continuous.comp
      (hderiv.prodMk continuous_const)
  exact (hcomp.norm.pow 2)

private theorem section_gradient_energy_eq_rawBlockEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : Differentiable ℝ F) (i : Fin (r + 1))
    (z : EuclideanSpace ℝ ι) (tail : Fin r → EuclideanSpace ℝ ι) :
    ‖gradient (euclideanCoordinateSection F
      (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i) z‖ ^ 2 =
      rawBlockEnergy F i (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (z, tail))) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i
  let x₀ := productToEuclidean (e.symm (0, tail))
  let x := productToEuclidean (e.symm (z, tail))
  have hsections : euclideanCoordinateSection F x₀ i =
      euclideanCoordinateSection F x i := by
    funext v
    rw [euclideanCoordinateSection_productToEuclidean,
      euclideanCoordinateSection_productToEuclidean]
    congr 1
    apply congrArg productToEuclidean
    calc
      Function.update (e.symm (0, tail)) i v = e.symm (v, tail) :=
        update_piFinSuccAbove_symm i 0 v tail
      _ = Function.update (e.symm (z, tail)) i v :=
        (update_piFinSuccAbove_symm i z v tail).symm
  have hblock : WithLp.toLp 2 (fun a => x (i, a)) = z := by
    apply PiLp.ext
    intro a
    simp [x, productToEuclidean, e,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_apply_same]
  have hdiff : DifferentiableAt ℝ F
      (x + euclideanBlockInclusion i (z - WithLp.toLp 2 (fun a => x (i, a)))) := by
    simpa [hblock] using hF x
  have hpoint : x + euclideanBlockInclusion i
      (z - WithLp.toLp 2 (fun a => x (i, a))) = x := by
    simp [hblock]
  rw [hsections, norm_gradient_eq_fderiv_local,
    fderiv_euclideanCoordinateSection F x i z hdiff]
  rw [hpoint]
  rfl

private theorem integrable_piFin_section_gradient_energy_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B) (i : Fin (r + 1)) :
    Integrable
      (fun p : EuclideanSpace ℝ ι × (Fin r → EuclideanSpace ℝ ι) =>
        ‖gradient (euclideanCoordinateSection F
          (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, p.2))) i)
          p.1‖ ^ 2)
      (μ.prod (Measure.pi fun _ : Fin r => μ)) := by
  let E := EuclideanSpace ℝ ι
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let e : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i
  let q : E × (Fin r → E) → ℝ := fun p =>
    rawBlockEnergy F i (productToEuclidean (e.symm p))
  let sec : E × (Fin r → E) → ℝ := fun p =>
    ‖gradient (euclideanCoordinateSection F
      (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => E) i).symm (0, p.2))) i) p.1‖ ^ 2
  have hqmeas : Measurable q := by
    exact (rawBlockEnergy_continuous F hF i).measurable.comp
      (continuous_productToEuclidean.measurable.comp e.symm.measurable)
  have hqint : Integrable q (μ.prod ν) := by
    refine Integrable.of_bound hqmeas.aestronglyMeasurable (B ^ 2) ?_
    filter_upwards with p
    have hnonneg : 0 ≤ q p := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact rawBlockEnergy_le_sq F B hB hbound i
      (productToEuclidean (e.symm p))
  have hFdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hfun (z : E) (tail : Fin r → E) : sec (z, tail) = q (z, tail) := by
    exact section_gradient_energy_eq_rawBlockEnergy F hFdiff i z tail
  have hsecInt : Integrable sec (μ.prod ν) := by
    apply hqint.congr
    filter_upwards with p
    exact (hfun p.1 p.2).symm
  change Integrable sec (μ.prod ν)
  exact hsecInt

/-- The actual coordinate-section energy integrated in its observation variable
is integrable over the finite tail law. -/
theorem integrable_piFin_section_gradient_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B) (i : Fin (r + 1)) :
    Integrable
      (fun tail : Fin r → EuclideanSpace ℝ ι =>
        ∫ z : EuclideanSpace ℝ ι,
          ‖gradient (euclideanCoordinateSection F
            (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i)
            z‖ ^ 2 ∂μ)
      (Measure.pi fun _ : Fin r => μ) := by
  let E := EuclideanSpace ℝ ι
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let sec : E × (Fin r → E) → ℝ := fun p =>
    ‖gradient (euclideanCoordinateSection F
      (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => E) i).symm (0, p.2))) i) p.1‖ ^ 2
  have hpair := integrable_piFin_section_gradient_energy_pair r μ F hF B hB hbound i
  change Integrable (fun tail => ∫ z : E, sec (z, tail) ∂μ) ν
  exact hpair.integral_prod_right

/-- The coordinate section energies, integrated over the same full product
witnesses, sum exactly to the energy under the flattened product law. -/
theorem integral_sum_euclideanCoordinateSection_gradient_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B) :
    (∑ i : Fin (r + 1),
      ∫ tail : Fin r → EuclideanSpace ℝ ι,
        ∫ z : EuclideanSpace ℝ ι,
          ‖gradient (euclideanCoordinateSection F
            (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm (0, tail))) i) z‖ ^ 2
          ∂μ ∂Measure.pi fun _ : Fin r => μ) =
      ∫ x, ‖gradient F x‖ ^ 2 ∂euclideanProductLaw (κ := Fin (r + 1)) μ := by
  let E := EuclideanSpace ℝ ι
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let π : Measure (Fin (r + 1) → E) := Measure.pi fun _ : Fin (r + 1) => μ
  have hFdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hblockInt (i : Fin (r + 1)) :
      Integrable (fun D : Fin (r + 1) → E =>
        rawBlockEnergy F i (productToEuclidean D)) π := by
    have hmeas : Measurable (fun D : Fin (r + 1) → E =>
        rawBlockEnergy F i (productToEuclidean D)) := by
      exact (rawBlockEnergy_continuous F hF i).measurable.comp
        continuous_productToEuclidean.measurable
    refine Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 2) ?_
    filter_upwards with D
    have hnonneg : 0 ≤ rawBlockEnergy F i (productToEuclidean D) := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact rawBlockEnergy_le_sq F B hB hbound i (productToEuclidean D)
  have hpointwise (D : Fin (r + 1) → E) :
      (∑ i : Fin (r + 1), rawBlockEnergy F i (productToEuclidean D)) =
        ‖gradient F (productToEuclidean D)‖ ^ 2 := by
    have hsum := sum_euclideanBlock_composition_norm_sq
      (fderiv ℝ F (productToEuclidean D))
    simpa [rawBlockEnergy, norm_gradient_eq_fderiv_local] using hsum
  have hterm (i : Fin (r + 1)) :
      (∫ tail : Fin r → E,
        ∫ z : E,
          ‖gradient (euclideanCoordinateSection F
            (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => E) i).symm (0, tail))) i) z‖ ^ 2
          ∂μ ∂ν) =
        ∫ D : Fin (r + 1) → E,
          rawBlockEnergy F i (productToEuclidean D) ∂π := by
    let e : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i
    let q : E × (Fin r → E) → ℝ := fun p =>
      rawBlockEnergy F i (productToEuclidean (e.symm p))
    let sec : E × (Fin r → E) → ℝ := fun p =>
      ‖gradient (euclideanCoordinateSection F
        (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => E) i).symm (0, p.2))) i) p.1‖ ^ 2
    have hMP : MeasurePreserving e π (μ.prod ν) := by
      simpa [e, π, ν] using
        (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) i)
    have hfun (z : E) (tail : Fin r → E) :
        sec (z, tail) = q (z, tail) := by
      exact section_gradient_energy_eq_rawBlockEnergy F hFdiff i z tail
    have hsecInt : Integrable sec (μ.prod ν) := by
      change Integrable (fun p : E × (Fin r → E) =>
        ‖gradient (euclideanCoordinateSection F
          (productToEuclidean ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => E) i).symm (0, p.2))) i) p.1‖ ^ 2) _
      exact integrable_piFin_section_gradient_energy_pair r μ F hF B hB hbound i
    calc
      _ = ∫ p : E × (Fin r → E), sec p ∂μ.prod ν := by
        simpa [sec] using (integral_prod_symm sec hsecInt).symm
      _ = ∫ p : E × (Fin r → E), q p ∂μ.prod ν := by
        apply integral_congr_ae
        filter_upwards with p
        exact hfun p.1 p.2
      _ = ∫ D : Fin (r + 1) → E, q (e D) ∂π :=
        (hMP.integral_comp' q).symm
      _ = ∫ D : Fin (r + 1) → E,
          rawBlockEnergy F i (productToEuclidean D) ∂π := by
        apply integral_congr_ae
        filter_upwards with D
        change rawBlockEnergy F i (productToEuclidean (e.symm (e D))) = _
        simp
  have hfullmeas : Measurable (fun x : EuclideanSpace ℝ (Fin (r + 1) × ι) =>
      ‖gradient F x‖ ^ 2) := by
    have hgrad : Continuous (fun x => gradient F x) := by
      change Continuous (fun x => (InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin (r + 1) × ι))).symm (fderiv ℝ F x))
      exact (InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin (r + 1) × ι))).symm.continuous.comp
          (hF.continuous_fderiv (by simp))
    exact (hgrad.norm.pow 2).measurable
  have hsumEval :
      (∑ i : Fin (r + 1),
        ∫ D : Fin (r + 1) → E,
          rawBlockEnergy F i (productToEuclidean D) ∂π) =
      ∫ D : Fin (r + 1) → E,
        ‖gradient F (productToEuclidean D)‖ ^ 2 ∂π := by
    calc
      _ = ∫ D : Fin (r + 1) → E,
          ∑ i : Fin (r + 1), rawBlockEnergy F i (productToEuclidean D) ∂π := by
        rw [integral_finsetSum]
        exact fun i _ => hblockInt i
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with D
        exact hpointwise D
  calc
    _ = ∑ i : Fin (r + 1),
        ∫ D : Fin (r + 1) → E,
          rawBlockEnergy F i (productToEuclidean D) ∂π := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = ∫ D : Fin (r + 1) → E,
        ‖gradient F (productToEuclidean D)‖ ^ 2 ∂π := hsumEval
    _ = ∫ x, ‖gradient F x‖ ^ 2 ∂euclideanProductLaw (κ := Fin (r + 1)) μ := by
      symm
      exact integral_euclideanProductLaw μ (fun x => ‖gradient F x‖ ^ 2) hfullmeas

end LOOConcentration.Revision
