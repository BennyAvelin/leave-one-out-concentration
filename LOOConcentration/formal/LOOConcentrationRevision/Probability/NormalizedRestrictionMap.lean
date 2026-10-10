import LOOConcentrationRevision.Probability.ConditionalMeanShift

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Mapping the actual inverse-mass restriction preserves its normalization and
conditioning event, including arbitrary source and target measurable carriers. -/
theorem normalizedRestriction_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (A : Set β) (hA : MeasurableSet A) :
    (normalizedRestriction μ (f ⁻¹' A)).map f = normalizedRestriction (μ.map f) A := by
  simp only [normalizedRestriction, Measure.map_smul, Measure.map_apply hf hA,
    Measure.restrict_map hf hA]

end LOOConcentration.Revision
