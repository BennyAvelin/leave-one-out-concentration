import LOOConcentration.FunctionalInequalities.VarianceTensorization

/-!
# Finite-product variance transport

This module records the coordinate insertion transport needed by the finite
Efron–Stein induction, with the zero-coordinate variance case treated
separately.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

private theorem square_norm_bound {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    ‖x ^ 2‖ ≤ B ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ B ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hB (abs_nonneg x))
      nlinarith [hprod]

private theorem integralVariance_section_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    Integrable (fun y => integralVariance μ (fun x => F (x, y))) ν := by
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let second : β → ℝ := fun y => ∫ x, F (x, y) ^ 2 ∂μ
  let variance : β → ℝ := fun y => integralVariance μ (fun x => F (x, y))
  have hF2 : Measurable (fun p : α × β => F p ^ 2) := hF.pow_const 2
  have hmeanStrong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hsecondStrong : StronglyMeasurable second := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ^ 2 ∂μ)
    exact hF2.stronglyMeasurable.integral_prod_left'
  have hmeanMeas : Measurable mean := hmeanStrong.measurable
  have hsecondMeas : Measurable second := hsecondStrong.measurable
  have hvarMeas : Measurable variance := by
    change Measurable (fun y => second y - mean y ^ 2)
    exact hsecondMeas.sub (hmeanMeas.pow_const 2)
  have hmeanBound (y : β) : |mean y| ≤ B := by
    have hsectionMeas : Measurable (fun x : α => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    have hsectionInt : Integrable (fun x : α => F (x, y)) μ :=
      bounded_measurable_integrable hsectionMeas B fun x => by
        simpa only [Real.norm_eq_abs] using hFbound (x, y)
    calc
      |mean y| ≤ ∫ x, |F (x, y)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : α, B ∂μ :=
        integral_mono hsectionInt.abs (integrable_const B) fun x => hFbound (x, y)
      _ = B := by simp
  have hsecondSectionInt (y : β) : Integrable (fun x : α => F (x, y) ^ 2) μ := by
    have hsqMeas : Measurable (fun x : α => F (x, y) ^ 2) :=
      hF2.comp (measurable_prodMk_right (y := y))
    exact bounded_measurable_integrable hsqMeas (B ^ 2) fun x => by
      exact square_norm_bound hB (hFbound (x, y))
  have hsecondNonneg (y : β) : 0 ≤ second y := by
    calc
      0 = ∫ _ : α, (0 : ℝ) ∂μ := by simp
      _ ≤ ∫ x, F (x, y) ^ 2 ∂μ :=
        integral_mono (by simp) (hsecondSectionInt y) fun x => sq_nonneg _
  have hsecondUpper (y : β) : second y ≤ B ^ 2 := by
    calc
      second y ≤ ∫ _ : α, B ^ 2 ∂μ :=
        integral_mono (hsecondSectionInt y) (integrable_const _) fun x => by
          have hprod := mul_nonneg
            (sub_nonneg.mpr (hFbound (x, y)))
            (add_nonneg hB (abs_nonneg (F (x, y))))
          nlinarith [hprod, sq_abs (F (x, y))]
      _ = B ^ 2 := by simp
  have hsecondBound (y : β) : |second y| ≤ B ^ 2 := by
    rw [abs_of_nonneg (hsecondNonneg y)]
    exact hsecondUpper y
  have hvariance_eq (y : β) : variance y = second y - mean y ^ 2 := by
    simp [variance, integralVariance, mean, second]
  have hvarianceBound (y : β) : ‖variance y‖ ≤ 2 * B ^ 2 := by
    rw [Real.norm_eq_abs, hvariance_eq]
    calc
      |second y - mean y ^ 2| ≤ |second y| + |mean y ^ 2| := abs_sub _ _
      _ ≤ B ^ 2 + B ^ 2 := add_le_add (hsecondBound y) (by
        rw [abs_of_nonneg (sq_nonneg (mean y))]
        have hprod := mul_nonneg
          (sub_nonneg.mpr (hmeanBound y))
          (add_nonneg hB (abs_nonneg (mean y)))
        nlinarith [hprod, sq_abs (mean y)])
      _ = 2 * B ^ 2 := by ring
  exact bounded_measurable_integrable hvarMeas (2 * B ^ 2) hvarianceBound

/-- The insertion of a first coordinate is a measure-preserving equivalence
between the product law and the finite product law. -/
theorem measurePreserving_piFin_insertZero
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
      (μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  simpa using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).symm

private theorem nested_insert_eq_deleted_succ
    {E : Type*} [MeasurableSpace E] {n : ℕ}
    (z₀ zⱼ : E) (tail₂ : Fin n → E) (j : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) 0).symm
        (z₀, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) j).symm
          (zⱼ, tail₂)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) j.succ).symm
        (zⱼ, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
          (z₀, tail₂)) := by
  let eFullZero : (Fin (n + 2) → E) ≃ᵐ E × (Fin (n + 1) → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) 0
  let eTailJ : (Fin (n + 1) → E) ≃ᵐ E × (Fin n → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) j
  let eFullJ : (Fin (n + 2) → E) ≃ᵐ E × (Fin (n + 1) → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) j.succ
  let eTailZero : (Fin (n + 1) → E) ≃ᵐ E × (Fin n → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0
  apply eFullJ.injective
  apply Prod.ext
  · simp [eFullJ, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth_zero']
  · funext q
    refine Fin.cases ?_ (fun q => ?_) q
    · simp [eFullJ, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero']
    · simp [eFullJ, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero']

/-- The iterated law obtained by first inserting coordinate zero and then
inserting coordinate `j` in the tail pushes forward to the law of the tail
deleted at full coordinate `j.succ`. -/
theorem integralVariance_piFin_jSucc_transport
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {n : ℕ} (f : (Fin (n + 2) → E) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hfbound : ∀ D, |f D| ≤ B) (j : Fin (n + 1)) :
    (∫ z₀, ∫ tail₂,
      integralVariance μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) 0).symm (z₀,
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => E) j).symm (zⱼ, tail₂))))
      ∂Measure.pi (fun _ : Fin n => μ) ∂μ) =
    ∫ tail,
      integralVariance μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) j.succ).symm (z, tail)))
      ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  let e : (Fin (n + 2) → E) ≃ᵐ E × (Fin (n + 1) → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) j.succ
  let G : E × (Fin (n + 1) → E) → ℝ := fun p => f (e.symm p)
  let K : (Fin (n + 1) → E) → ℝ := fun tail =>
    integralVariance μ (fun z => G (z, tail))
  let insertTail : E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
  have hG : Measurable G := hf.comp e.symm.measurable
  have hGbound (p : E × (Fin (n + 1) → E)) : |G p| ≤ B := hfbound (e.symm p)
  have hKint : Integrable K (Measure.pi fun _ : Fin (n + 1) => μ) := by
    change Integrable (fun tail => integralVariance μ (fun z => G (z, tail))) _
    exact integralVariance_section_integrable μ
      (Measure.pi fun _ : Fin (n + 1) => μ) G B hB hG hGbound
  have hInsertMeasurePreserving :
      MeasurePreserving insertTail
        (μ.prod (Measure.pi fun _ : Fin n => μ))
        (Measure.pi fun _ : Fin (n + 1) => μ) := by
    simpa [insertTail] using measurePreserving_piFin_insertZero μ n
  have hKcomp : Integrable (fun p => K (insertTail p))
      (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    change Integrable (K ∘ insertTail) (μ.prod (Measure.pi fun _ : Fin n => μ))
    apply (hInsertMeasurePreserving.integrable_comp_emb insertTail.measurableEmbedding).2
    exact hKint
  have hpoint (z₀ : E) (tail₂ : Fin n → E) :
      integralVariance μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) 0).symm (z₀,
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => E) j).symm (zⱼ, tail₂)))) =
      K (insertTail (z₀, tail₂)) := by
    apply congrArg (integralVariance μ)
    funext zⱼ
    dsimp [K, G, e, insertTail]
    exact congrArg f (nested_insert_eq_deleted_succ z₀ zⱼ tail₂ j)
  calc
    (∫ z₀, ∫ tail₂,
        integralVariance μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 2) => E) 0).symm (z₀,
            (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => E) j).symm (zⱼ, tail₂))))
        ∂Measure.pi (fun _ : Fin n => μ) ∂μ) =
      ∫ z₀, ∫ tail₂, K (insertTail (z₀, tail₂))
        ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with z₀
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun tail₂ => hpoint z₀ tail₂
    _ = ∫ p, K (insertTail p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      (integral_prod _ hKcomp).symm
    _ = ∫ tail, K tail ∂Measure.pi (fun _ : Fin (n + 1) => μ) :=
      hInsertMeasurePreserving.integral_comp' K
    _ = ∫ tail,
        integralVariance μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 2) => E) j.succ).symm (z, tail)))
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun tail => by
        change K tail = integralVariance μ (fun z => f (e.symm (z, tail)))
        rfl

/-- The variance on the empty-coordinate product vanishes; this is the
`r = 0` base case for finite product tensorization. -/
theorem integralVariance_piFin_zero_eq_zero
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : (Fin 0 → E) → ℝ) :
    integralVariance (Measure.pi fun _ : Fin 0 => μ) f = 0 := by
  classical
  let d : Fin 0 → E := Fin.elim0
  have hconst : f = fun _ : Fin 0 → E => f d := by
    funext x
    congr 1
    exact Subsingleton.elim x d
  have hfirst : (∫ x, f x ∂Measure.pi fun _ : Fin 0 => μ) = f d := by
    rw [hconst]
    simp [integral_const]
  have hsecond : (∫ x, f x ^ 2 ∂Measure.pi fun _ : Fin 0 => μ) = (f d) ^ 2 := by
    rw [hconst]
    simp [integral_const]
  simp [integralVariance, hfirst, hsecond]

#print axioms LOOConcentration.measurePreserving_piFin_insertZero
#print axioms LOOConcentration.integralVariance_piFin_jSucc_transport
#print axioms LOOConcentration.integralVariance_piFin_zero_eq_zero

end LOOConcentration
