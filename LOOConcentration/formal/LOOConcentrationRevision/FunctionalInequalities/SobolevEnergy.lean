import LOOConcentrationRevision.Frozen.Definitions.SobolevEnergy

/-!
# Finiteness and vanishing of the approved Sobolev energy

These facts follow from the gradient component's L² membership. Vanishing
energy identifies a zero gradient component; it does not yet imply constant
function values for a possibly singular observation law.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

theorem sobolevEnergy_lt_top (u : SobolevPair μ) : sobolevEnergy μ u < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (Lp.memLp (WithLp.ofLp u.val).2).eLpNorm_lt_top
  simpa only [sobolevEnergy, ENNReal.toReal_ofNat, ENNReal.rpow_two] using h

theorem sobolevEnergy_eq_zero_iff (u : SobolevPair μ) :
    sobolevEnergy μ u = 0 ↔ (WithLp.ofLp u.val).2 = 0 := by
  rw [sobolevEnergy, lintegral_eq_zero_iff'
    ((Lp.aestronglyMeasurable (WithLp.ofLp u.val).2).enorm.pow_const 2),
    Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    filter_upwards [h] with x hx
    simpa only [Pi.zero_apply, pow_eq_zero_iff (by decide : 2 ≠ 0), enorm_eq_zero] using hx
  · intro h
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, enorm_zero, zero_pow (by decide : 2 ≠ 0)]

end LOOConcentration.Revision
