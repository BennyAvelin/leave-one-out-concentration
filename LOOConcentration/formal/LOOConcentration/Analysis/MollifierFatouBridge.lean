import LOOConcentration.Analysis.DatasetClipMollify
import LOOConcentration.Analysis.ClipLimit

/-!
# Fatou transfer for the actual dataset mollifier

The scale `1 / (j + 1)` gives a concrete positive sequence of mollifier
radii tending to zero. The first theorem transfers assumed centered
exponential-integral bounds for this actual sequence, with a convergent
upper-bound envelope, to a fixed clipped dataset function. The second theorem
applies that result at every cap `j + 1`, then uses the clipping limit to
transfer the envelope's limit to the original dataset function.

The smooth exponential-integral estimates and integrability of the original
function are explicit producer premises. In particular, no exponential
integrability of the limiting function is assumed.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace LOOConcentration

/-- The concrete positive mollifier radii used in the first Fatou limit. -/
noncomputable def datasetMollifierScale (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹

theorem datasetMollifierScale_pos (j : ℕ) : 0 < datasetMollifierScale j := by
  exact inv_pos.mpr (by positivity)

theorem datasetMollifierScale_tendsto :
    Tendsto datasetMollifierScale atTop (𝓝[>] (0 : ℝ)) := by
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  refine tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_inv_atTop_zero.comp hden, ?_⟩
  filter_upwards [] with j
  exact datasetMollifierScale_pos j

private theorem datasetClipFunction_integrable {k m n : ℕ}
    {F : Dataset (Observation k m) n → ℝ} {a b A : ℝ}
    {μ : Measure (EuclideanSpace ℝ (DatasetCoordinate k m n))}
    [IsProbabilityMeasure μ]
    (hseg : DatasetLinearGrowthSegmentBound F a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) :
    Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
      clipValue A (F (datasetFromEuclidean x))) μ := by
  have hcontinuous := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hmeas : AEMeasurable
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
        clipValue A (F (datasetFromEuclidean x))) μ := by
    exact (continuous_clipValue A).comp_aestronglyMeasurable
      hcontinuous.aestronglyMeasurable |>.aemeasurable
  apply Integrable.of_mem_Icc (-A) A hmeas
  filter_upwards [] with x
  exact Set.mem_Icc.mpr (clipValue_bounds (u := F (datasetFromEuclidean x)) hA)

private theorem datasetClipThenMollify_integrable {k m n : ℕ}
    {F : Dataset (Observation k m) n → ℝ} {a b A η : ℝ}
    {μ : Measure (EuclideanSpace ℝ (DatasetCoordinate k m n))}
    [IsProbabilityMeasure μ]
    (hseg : DatasetLinearGrowthSegmentBound F a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hη : 0 < η) :
    Integrable (datasetClipThenMollify F A η) μ := by
  have hcontinuous := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hmoll : ContDiff ℝ ∞ (datasetClipThenMollify F A η) := by
    simpa [datasetClipThenMollify] using
      (contDiff_clipThenMollify hcontinuous hη)
  have hmeas : AEMeasurable (datasetClipThenMollify F A η) μ :=
    hmoll.continuous.aestronglyMeasurable.aemeasurable
  apply Integrable.of_mem_Icc (-A) A hmeas
  filter_upwards [] with x
  exact Set.mem_Icc.mpr
    (datasetClipThenMollify_range hseg ha hb hA hη x)

private theorem centeredExp_fatou_tendsto_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (hmeans : IntegralMeansConverge μ f F) (lam : ℝ)
    (B : ℕ → ℝ≥0∞) (Blim : ℝ≥0∞)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (f j x - ∫ y, f j y ∂μ))) ∂μ ≤ B j)
    (hB : Tendsto B atTop (𝓝 Blim)) :
    ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (F x - ∫ y, F y ∂μ))) ∂μ ≤ Blim := by
  let phi : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (lam * t))
  have hphi : Continuous phi := by
    dsimp [phi]
    exact ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hfatou := centeredTransform_fatou hf hF hpoint hmeans phi hphi
  calc
    ∫⁻ x, ENNReal.ofReal
        (Real.exp (lam * (F x - ∫ y, F y ∂μ))) ∂μ =
        ∫⁻ x, phi (F x - ∫ y, F y ∂μ) ∂μ := by
      rfl
    _ ≤ atTop.liminf (fun j =>
        ∫⁻ x, phi (f j x - ∫ y, f j y ∂μ) ∂μ) := hfatou
    _ ≤ atTop.liminf B :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j => by
        simpa [phi] using hbound j)
    _ = Blim := hB.liminf_eq

/-- For any fixed real `λ`, centered exponential-integral bounds for the
actual radii `1 / (j + 1)` transfer to the fixed clipped function when their
upper-bound envelope converges. The premise is deliberately on
`datasetClipThenMollify`, rather than on an arbitrary approximating sequence. -/
theorem centeredExp_datasetClipThenMollify_bound {k m n : ℕ}
    {F : Dataset (Observation k m) n → ℝ} {a b A lam : ℝ}
    {μ : Measure (EuclideanSpace ℝ (DatasetCoordinate k m n))}
    [IsProbabilityMeasure μ] (B : ℕ → ℝ≥0∞) (Blim : ℝ≥0∞)
    (hseg : DatasetLinearGrowthSegmentBound F a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hSmooth : ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
        (datasetClipThenMollify F A (datasetMollifierScale j) x -
          ∫ y, datasetClipThenMollify F A (datasetMollifierScale j) y ∂μ))) ∂μ ≤ B j)
    (hB : Tendsto B atTop (𝓝 Blim)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
      (clipValue A (F (datasetFromEuclidean x)) -
        ∫ y, clipValue A (F (datasetFromEuclidean y)) ∂μ))) ∂μ ≤ Blim := by
  let f : ℕ → EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ :=
    fun j x => datasetClipThenMollify F A (datasetMollifierScale j) x
  let G : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ :=
    fun x => clipValue A (F (datasetFromEuclidean x))
  have hf : ∀ j, Integrable (f j) μ := by
    intro j
    exact datasetClipThenMollify_integrable hseg ha hb hA
      (datasetMollifierScale_pos j)
  have hG : Integrable G μ := by
    exact datasetClipFunction_integrable hseg ha hb hA
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (G x)) := by
    filter_upwards [] with x
    dsimp [f, G]
    simpa [Function.comp_def, datasetMollifierScale] using
      (datasetClipThenMollify_tendsto hseg ha hb (datasetFromEuclidean x)).comp
        datasetMollifierScale_tendsto
  have hmeans : IntegralMeansConverge μ f G := by
    change Tendsto (fun j => ∫ x, f j x ∂μ) atTop (𝓝 (∫ x, G x ∂μ))
    dsimp [f, G]
    exact (datasetClipThenMollify_integral_tendsto hseg ha hb hA).comp
      datasetMollifierScale_tendsto
  exact centeredExp_fatou_tendsto_bound hf hG hpoint hmeans lam B Blim
    (by
      intro j
      exact hSmooth j)
    hB

/-- For each mollifier index, a bound uniform over all nonnegative caps passes
to the clipped functions. If these cap-uniform bounds converge along the
mollifier indices, the actual `j + 1` clipping sequence transfers their limit
to the original dataset function. This is the exact uniform-in-cap premise
needed from a smooth-MGF producer. Integrability of the original function is
explicit because the source segment and finite-second-moment producer that
should establish it are not part of this module. -/
theorem centeredExp_datasetFunction_bound {k m n : ℕ}
    {F : Dataset (Observation k m) n → ℝ} {a b lam : ℝ}
    {μ : Measure (EuclideanSpace ℝ (DatasetCoordinate k m n))}
    [IsProbabilityMeasure μ] (B : ℕ → ℝ≥0∞) (Blim : ℝ≥0∞)
    (hseg : DatasetLinearGrowthSegmentBound F a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
      F (datasetFromEuclidean x)) μ)
    (hSmooth : ∀ A : ℝ, 0 ≤ A → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
        (datasetClipThenMollify F A (datasetMollifierScale j) x -
          ∫ y, datasetClipThenMollify F A (datasetMollifierScale j) y ∂μ))) ∂μ ≤ B j)
    (hB : Tendsto B atTop (𝓝 Blim)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
      (F (datasetFromEuclidean x) -
        ∫ y, F (datasetFromEuclidean y) ∂μ))) ∂μ ≤ Blim := by
  let G : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ :=
    fun x => F (datasetFromEuclidean x)
  have hclipInt : ∀ j : ℕ, Integrable (clipValueSequence G j) μ := by
    intro j
    let A : ℝ := (j : ℝ) + 1
    have hA : 0 ≤ A := by positivity
    have hmeas : AEMeasurable (clipValueSequence G j) μ := by
      change AEMeasurable (fun x => clipValue A (G x)) μ
      exact ((continuous_clipValue A).comp_aestronglyMeasurable hF.1).aemeasurable
    apply Integrable.of_mem_Icc (-A) A hmeas
    filter_upwards [] with x
    exact Set.mem_Icc.mpr (clipValue_bounds (u := G x) hA)
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun j => clipValueSequence G j x) atTop (𝓝 (G x)) := by
    filter_upwards [] with x
    exact clipValueSequence_tendsto G x
  have hmeans : IntegralMeansConverge μ (fun j => clipValueSequence G j) G := by
    simpa [IntegralMeansConverge] using clipValueSequence_integral_tendsto hF
  have hbound : ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
        (clipValueSequence G j x - ∫ y, clipValueSequence G j y ∂μ))) ∂μ ≤ Blim := by
    intro j
    let A : ℝ := (j : ℝ) + 1
    have hA : 0 ≤ A := by positivity
    have h := centeredExp_datasetClipThenMollify_bound B Blim hseg ha hb hA
      (hSmooth A hA) hB
    simpa [clipValueSequence, G, A] using h
  have hresult := centeredExp_fatou hclipInt hF hpoint hmeans lam Blim hbound
  simpa [G] using hresult

end LOOConcentration
