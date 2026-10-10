import LOOConcentration.FunctionalInequalities.FiniteEntropyTensorization
import LOOConcentration.FunctionalInequalities.FiniteVarianceTensorization

/-!
# Finite entropy coordinate transport

This module proves bounded section-entropy admission and transports its
expected value through the reviewed first-coordinate insertion map.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem exists_mul_log_norm_bound (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Set.Icc (0 : ℝ) B, ‖x * Real.log x‖ ≤ K := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B) := isCompact_Icc
  have hcontinuous : Continuous (fun x : ℝ => ‖x * Real.log x‖) :=
    continuous_norm.comp Real.continuous_mul_log
  obtain ⟨K, hK0, hK⟩ :=
    hcompact.bddAbove_image hcontinuous.continuousOn |>.exists_ge 0
  refine ⟨K, hK0, ?_⟩
  intro x hx
  exact hK _ ⟨x, hx, rfl⟩

private theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

private theorem entropy_section_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α × β → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖entropy μ (fun x => F (x, y))‖ ≤ K := by
  obtain ⟨L, hL0, hL⟩ := exists_mul_log_norm_bound B
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let phiIntegral : β → ℝ := fun y =>
    ∫ x, F (x, y) * Real.log (F (x, y)) ∂μ
  have hphiMeas : Measurable (fun p : α × β => F p * Real.log (F p)) :=
    Real.continuous_mul_log.measurable.comp hF
  have hmeanStrong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hphiStrong : StronglyMeasurable phiIntegral := by
    change StronglyMeasurable
      (fun y => ∫ x, F (x, y) * Real.log (F (x, y)) ∂μ)
    exact hphiMeas.stronglyMeasurable.integral_prod_left'
  have hmeanMeas : Measurable mean := hmeanStrong.measurable
  have hphiMeas' : Measurable phiIntegral := hphiStrong.measurable
  have hkernelMeas :
      Measurable (fun y => entropy μ (fun x => F (x, y))) := by
    change Measurable (fun y => phiIntegral y - mean y * Real.log (mean y))
    exact hphiMeas'.sub
      (Real.continuous_mul_log.measurable.comp hmeanMeas)
  have hFphiBound (p : α × β) :
      ‖F p * Real.log (F p)‖ ≤ L := hL (F p) ⟨hF_nonneg p, hF_le p⟩
  have hsectionMeanBounds (y : β) : mean y ∈ Set.Icc 0 B := by
    have hsectionMeas : Measurable (fun x : α => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    have hsectionInt : Integrable (fun x : α => F (x, y)) μ :=
      Integrable.of_mem_Icc 0 B hsectionMeas.aemeasurable <|
        Filter.Eventually.of_forall fun x =>
          ⟨hF_nonneg (x, y), hF_le (x, y)⟩
    refine ⟨?_, ?_⟩
    · exact integral_nonneg fun x => hF_nonneg (x, y)
    · calc
        mean y ≤ ∫ _ : α, (B : ℝ) ∂μ :=
          integral_mono hsectionInt (integrable_const B) fun x => hF_le (x, y)
        _ = B := by simp
  have hphiSectionBound (y : β) : ‖phiIntegral y‖ ≤ L := by
    have hsectionInt : Integrable
        (fun x : α => F (x, y) * Real.log (F (x, y))) μ := by
      apply bounded_measurable_integrable
        (hphiMeas.comp (measurable_prodMk_right (y := y))) L
      intro x
      exact hFphiBound (x, y)
    calc
      ‖phiIntegral y‖ ≤ ∫ x, ‖F (x, y) * Real.log (F (x, y))‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _ : α, L ∂μ :=
        integral_mono hsectionInt.norm (integrable_const L) fun x => hFphiBound (x, y)
      _ = L := by simp
  refine ⟨2 * L, by positivity, ?_⟩
  intro y
  change ‖phiIntegral y - mean y * Real.log (mean y)‖ ≤ 2 * L
  calc
    ‖phiIntegral y - mean y * Real.log (mean y)‖ ≤
        ‖phiIntegral y‖ + ‖mean y * Real.log (mean y)‖ := norm_sub_le _ _
    _ ≤ L + L := add_le_add (hphiSectionBound y)
      (hL (mean y) (hsectionMeanBounds y))
    _ = 2 * L := by ring

/-- For measurable data, the entropy of a coordinate section is a measurable
function of the remaining coordinates. -/
theorem entropy_section_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α × β → ℝ) (hF : Measurable F) :
    Measurable (fun y => entropy μ (fun x => F (x, y))) := by
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let phiIntegral : β → ℝ := fun y =>
    ∫ x, F (x, y) * Real.log (F (x, y)) ∂μ
  have hphiMeas : Measurable (fun p : α × β => F p * Real.log (F p)) :=
    Real.continuous_mul_log.measurable.comp hF
  have hmeanStrong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hphiStrong : StronglyMeasurable phiIntegral := by
    change StronglyMeasurable
      (fun y => ∫ x, F (x, y) * Real.log (F (x, y)) ∂μ)
    exact hphiMeas.stronglyMeasurable.integral_prod_left'
  change Measurable (fun y => phiIntegral y - mean y * Real.log (mean y))
  exact hphiStrong.measurable.sub
    (Real.continuous_mul_log.measurable.comp hmeanStrong.measurable)

/-- The section-entropy kernel is integrable on every finite measure of the
remaining coordinates. Its uniform bound follows from continuity of
`x * log x` on `[0,B]`; no lower bound away from zero is needed. -/
theorem entropy_section_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hF_nonneg : ∀ p, 0 ≤ F p)
    (hF_le : ∀ p, F p ≤ B) :
    Integrable (fun y => entropy μ (fun x => F (x, y))) ν := by
  obtain ⟨K, hK0, hK⟩ := entropy_section_bound μ F B hB hF hF_nonneg hF_le
  exact bounded_measurable_integrable
    (entropy_section_measurable μ F hF) K hK

private theorem nested_insert_eq_deleted_succ_entropy
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

/-- Integrating the entropy in coordinate `j` after inserting a first
coordinate is exactly integration of the corresponding `j.succ` section.
The measure change is the reviewed coordinate insertion equivalence. -/
theorem entropy_piFin_jSucc_transport
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {n : ℕ} (f : (Fin (n + 2) → E) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hf_nonneg : ∀ D, 0 ≤ f D) (hf_le : ∀ D, f D ≤ B)
    (j : Fin (n + 1)) :
    (∫ z₀, ∫ tail₂,
      entropy μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) 0).symm (z₀,
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => E) j).symm (zⱼ, tail₂))))
      ∂Measure.pi (fun _ : Fin n => μ) ∂μ) =
    ∫ tail,
      entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) j.succ).symm (z, tail)))
      ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  let e : (Fin (n + 2) → E) ≃ᵐ E × (Fin (n + 1) → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) j.succ
  let G : E × (Fin (n + 1) → E) → ℝ := fun p => f (e.symm p)
  let K : (Fin (n + 1) → E) → ℝ := fun tail =>
    entropy μ (fun z => G (z, tail))
  let insertTail : E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
  have hG : Measurable G := hf.comp e.symm.measurable
  have hG_nonneg (p : E × (Fin (n + 1) → E)) : 0 ≤ G p := hf_nonneg (e.symm p)
  have hG_le (p : E × (Fin (n + 1) → E)) : G p ≤ B := hf_le (e.symm p)
  have hKint : Integrable K (Measure.pi fun _ : Fin (n + 1) => μ) := by
    change Integrable (fun tail => entropy μ (fun z => G (z, tail))) _
    exact entropy_section_integrable μ (Measure.pi fun _ : Fin (n + 1) => μ)
      G B hB hG hG_nonneg hG_le
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
      entropy μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) 0).symm (z₀,
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => E) j).symm (zⱼ, tail₂)))) =
      K (insertTail (z₀, tail₂)) := by
    apply congrArg (entropy μ)
    funext zⱼ
    dsimp [K, G, e, insertTail]
    exact congrArg f (nested_insert_eq_deleted_succ_entropy z₀ zⱼ tail₂ j)
  calc
    (∫ z₀, ∫ tail₂,
        entropy μ (fun zⱼ => f ((MeasurableEquiv.piFinSuccAbove
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
        entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 2) => E) j.succ).symm (z, tail)))
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun tail => by
        change K tail = entropy μ (fun z => f (e.symm (z, tail)))
        rfl

/-- Entropy of a function on the empty-coordinate product is zero, since that
product is a singleton probability space and every such function is constant. -/
theorem entropy_piFin_zero_eq_zero
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : (Fin 0 → E) → ℝ) :
    entropy (Measure.pi fun _ : Fin 0 => μ) f = 0 := by
  classical
  let d : Fin 0 → E := Fin.elim0
  have hconst : f = fun _ : Fin 0 → E => f d := by
    funext x
    congr 1
    exact Subsingleton.elim x d
  have hfirst :
      (∫ x, f x ∂Measure.pi fun _ : Fin 0 => μ) = f d := by
    rw [hconst]
    simp [integral_const]
  have hsecond :
      (∫ x, f x * Real.log (f x) ∂Measure.pi fun _ : Fin 0 => μ) =
        f d * Real.log (f d) := by
    rw [hconst]
    simp [integral_const]
  simp [entropy, hfirst, hsecond]

#print axioms LOOConcentration.entropy_section_measurable
#print axioms LOOConcentration.entropy_section_integrable
#print axioms LOOConcentration.entropy_piFin_jSucc_transport
#print axioms LOOConcentration.entropy_piFin_zero_eq_zero

end LOOConcentration
