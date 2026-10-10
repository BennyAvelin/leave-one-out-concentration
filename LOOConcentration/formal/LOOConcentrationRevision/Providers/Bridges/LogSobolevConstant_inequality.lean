import LOOConcentrationRevision.FunctionalInequalities.ZeroEnergyPerturbation
import LOOConcentrationRevision.FunctionalInequalities.PositiveEnergyGenerator
import LOOConcentrationRevision.Probability.ZeroDimensional

set_option autoImplicit false
namespace LOOConcentration.Revision.Providers
open MeasureTheory
open scoped ENNReal

/-- Full all-pairs estimate at the literal finite optimal constant.
The positive-energy witness is constructed internally and empty coordinates are covered directly. -/
theorem logSobolevConstant_inequality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (_hfinite : logSobolevConstant μ < ⊤) (u : SobolevPair μ) :
    squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * logSobolevConstant μ * sobolevEnergy μ u := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    exact logSobolev_inequality_of_empty_coordinates μ u
  · let := hι
    by_cases hu : sobolevEnergy μ u = 0
    · obtain ⟨v, hv⟩ := positiveEnergyGenerator μ
      rw [squareEntropy_eq_zero_of_energy_zero_and_witness _hfinite u v hu hv]
      exact bot_le
    · exact squareEntropy_le_of_energy_pos u (pos_iff_ne_zero.mpr hu)

end LOOConcentration.Revision.Providers
