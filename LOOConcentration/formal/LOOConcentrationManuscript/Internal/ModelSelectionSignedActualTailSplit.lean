import LOOConcentrationManuscript.Internal.ModelSelectionSignedBiasDecomposition
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory LOOConcentration

private theorem actual_three_component_signed_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H I₁ I₂ I₃ : Ω → ℝ) (bias δ₃ u v w ε : ℝ)
    (hEq : ∀ D, H D = I₁ D + I₂ D + I₃ D + bias)
    (hBias : bias ≤ δ₃) (hLevels : δ₃ + u + v + w ≤ ε) :
    P.real {D | H D > ε} ≤
      P.real {D | I₁ D > u} + P.real {D | I₂ D > v} + P.real {D | I₃ D > w} := by
  have hSubset : {D | H D > ε} ⊆
      ({D | I₁ D > u} ∪ {D | I₂ D > v}) ∪ {D | I₃ D > w} := by
    intro D hD
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hn
    have he := hEq D
    change ε < H D at hD
    linarith only [hn.1.1, hn.1.2, hn.2, he, hBias, hLevels, hD]
  exact (measureReal_mono hSubset).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) (le_refl _)))

/-- Both actual signed-error splits, deriving the bias and decomposition from the source inputs. -/
theorem modelSelection_actual_signed_main_and_simplified_tail_split {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
        Observation k m => fittedLoss (T₀ n) L p.1 p.2 -
          fittedLoss (T₁ n) L p.1 p.2))
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ))
    (δ₃ : ℝ)
    (hBias : ∀ i : Fin (n + 2),
      |(∫ D : Dataset (Observation k m) (n + 2),
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i))
          ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (fittedLoss (T₀ (n + 1)) L p.1 p.2 -
            fittedLoss (T₁ (n + 1)) L p.1 p.2)
          ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃) (ε : ℝ) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let f : Observation k m → ℝ := fun z => ∫ D,
      (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
    let V : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
    let E : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let R : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let I₁ := fun D => V D - E D
    let I₂ := fun D => (∫ E, V E ∂P) - V D
    let I₃ := fun D => R D - ∫ E, R E ∂P
    (P.real {D | R D - E D > ε} ≤ P.real {D | I₁ D > ε/3} +
        P.real {D | I₂ D > ε/3} + P.real {D | I₃ D > ε/3-δ₃} ∧
      P.real {D | E D - R D > ε} ≤ P.real {D | -I₁ D > ε/3} +
        P.real {D | -I₂ D > ε/3} + P.real {D | -I₃ D > ε/3-δ₃}) ∧
    (P.real {D | R D - E D > ε} ≤ P.real {D | I₁ D > (ε-δ₃)/3} +
        P.real {D | I₂ D > (ε-δ₃)/3} + P.real {D | I₃ D > (ε-δ₃)/3} ∧
      P.real {D | E D - R D > ε} ≤ P.real {D | -I₁ D > (ε-δ₃)/3} +
        P.real {D | -I₂ D > (ε-δ₃)/3} + P.real {D | -I₃ D > (ε-δ₃)/3}) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let f : Observation k m → ℝ := fun z => ∫ D, (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
  let V : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
  let E : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let R : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let I₁ := fun D => V D - E D
  let I₂ := fun D => (∫ E, V E ∂P) - V D
  let I₃ := fun D => R D - ∫ E, R E ∂P
  let bias := (∫ D, R D ∂P) - ∫ D, V D ∂P
  have h := modelSelection_actual_signed_bias_decomposition μ T₀ T₁ L hf₀ hf₁ hMeas hHeld δ₃ hBias
  dsimp only at h
  have hB : |bias| ≤ δ₃ := h.2.2.2.2.2.2.2.2.2.1
  have hEq : ∀ D, R D - E D = I₁ D + I₂ D + I₃ D + bias :=
    h.2.2.2.2.2.2.2.2.2.2.1
  have hNeg : ∀ D, E D - R D = -I₁ D + -I₂ D + -I₃ D + -bias := by
    intro D
    have hh : E D - R D = -I₁ D + -I₂ D + -I₃ D - bias :=
      h.2.2.2.2.2.2.2.2.2.2.2 D
    exact hh.trans (by ring)
  have hUpper : bias ≤ δ₃ := (le_abs_self _).trans hB
  have hLower : -bias ≤ δ₃ := (neg_le_abs _).trans hB
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact actual_three_component_signed_tail P (fun D => R D - E D) I₁ I₂ I₃ bias δ₃
      (ε/3) (ε/3) (ε/3-δ₃) ε hEq hUpper (by ring_nf; exact le_rfl)
  · exact actual_three_component_signed_tail P (fun D => E D - R D)
      (fun D => -I₁ D) (fun D => -I₂ D) (fun D => -I₃ D) (-bias) δ₃
      (ε/3) (ε/3) (ε/3-δ₃) ε hNeg hLower (by ring_nf; exact le_rfl)
  · exact actual_three_component_signed_tail P (fun D => R D - E D) I₁ I₂ I₃ bias δ₃
      ((ε-δ₃)/3) ((ε-δ₃)/3) ((ε-δ₃)/3) ε hEq hUpper (by ring_nf; exact le_rfl)
  · exact actual_three_component_signed_tail P (fun D => E D - R D)
      (fun D => -I₁ D) (fun D => -I₂ D) (fun D => -I₃ D) (-bias) δ₃
      ((ε-δ₃)/3) ((ε-δ₃)/3) ((ε-δ₃)/3) ε hNeg hLower (by ring_nf; exact le_rfl)

end LOOConcentration.Manuscript.Internal
