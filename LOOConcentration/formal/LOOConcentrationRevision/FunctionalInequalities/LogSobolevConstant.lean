import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergy

/-!
# Bounds from the approved optimal log-Sobolev constant

The supremum gives the inequality for positive gradient energy. The separate
zero-energy perturbation argument required by the frozen bridge remains open.
No unproved bridge or registered provider is imported here.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

theorem entropy_div_energy_le_logSobolevConstant (u : SobolevPair μ)
    (henergy : 0 < sobolevEnergy μ u) :
    squareEntropy μ (WithLp.ofLp u.val).1 / (2 * sobolevEnergy μ u) ≤
      logSobolevConstant μ := by
  exact le_iSup_of_le u (le_iSup_of_le henergy le_rfl)

theorem squareEntropy_le_of_energy_pos (u : SobolevPair μ)
    (henergy : 0 < sobolevEnergy μ u) :
    squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * logSobolevConstant μ * sobolevEnergy μ u := by
  have hzero : (2 : ℝ≥0∞) * sobolevEnergy μ u ≠ 0 :=
    mul_ne_zero (by norm_num) henergy.ne'
  have htop : (2 : ℝ≥0∞) * sobolevEnergy μ u ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (sobolevEnergy_lt_top u).ne
  have h := (ENNReal.div_le_iff hzero htop).mp
    (entropy_div_energy_le_logSobolevConstant u henergy)
  simpa only [mul_left_comm, mul_assoc] using h

theorem squareEntropy_lt_top_of_energy_pos
    (hfinite : logSobolevConstant μ < ⊤) (u : SobolevPair μ)
    (henergy : 0 < sobolevEnergy μ u) :
    squareEntropy μ (WithLp.ofLp u.val).1 < ⊤ := by
  exact (squareEntropy_le_of_energy_pos u henergy).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hfinite.ne) (sobolevEnergy_lt_top u).ne))

/-- Upper bounds on the supremum need only control its positive-energy quotients. -/
theorem logSobolevConstant_le_iff (C : ℝ≥0∞) :
    logSobolevConstant μ ≤ C ↔
      ∀ u : SobolevPair μ, 0 < sobolevEnergy μ u →
        squareEntropy μ (WithLp.ofLp u.val).1 ≤ 2 * C * sobolevEnergy μ u := by
  constructor
  · intro h u hu
    exact (squareEntropy_le_of_energy_pos u hu).trans
      (mul_le_mul' (mul_le_mul' le_rfl h) le_rfl)
  · intro h
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply (ENNReal.div_le_iff
      (mul_ne_zero (by norm_num) hu.ne')
      (ENNReal.mul_ne_top (by norm_num) (sobolevEnergy_lt_top u).ne)).mpr
    simpa only [mul_left_comm, mul_assoc] using h u hu

end LOOConcentration.Revision
