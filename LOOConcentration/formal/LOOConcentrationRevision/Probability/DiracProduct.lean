import LOOConcentrationRevision.FunctionalInequalities.SquareEntropy
import LOOConcentrationRevision.Frozen.Definitions.SobolevPair
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

/-! Finite product and entropy facts for a Dirac observation law. -/

/-- A finite product of copies of a Dirac measure is the Dirac measure at the
constant ordered tuple. -/
theorem measure_pi_dirac {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) :
    Measure.pi (fun _ : ι => Measure.dirac a) = Measure.dirac (fun _ : ι => a) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' (fun _ : ι => a) (MeasurableSet.univ_pi hs)]
  by_cases h : ∀ i, a ∈ s i
  · simp [Set.mem_pi, h]
  · have hex : ∃ i, a ∉ s i := not_forall.mp h
    obtain ⟨i, hi⟩ := hex
    have himem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have hzero : Measure.dirac a (s i) = 0 := by
      rw [Measure.dirac_apply' a (hs i)]
      simp [hi]
    have hnotmem : (fun _ : ι => a) ∉ Set.univ.pi s := by
      intro hm
      exact hi (hm i (Set.mem_univ i))
    rw [Finset.prod_eq_zero (s := Finset.univ) himem hzero]
    simp only [Set.indicator_apply, hnotmem, if_false]

/-- For an integrable measurable scalar statistic on a Dirac space, its
almost-everywhere value is its expectation. -/
theorem dirac_integrable_statistic_ae_eq_mean {α : Type*} [MeasurableSpace α]
    {a : α} {H : α → ℝ} (hH : Measurable H) (hHint : Integrable H (Measure.dirac a)) :
    H =ᵐ[Measure.dirac a] (fun _ => ∫ x, H x ∂Measure.dirac a) ∧
      Integrable (fun x => H x - ∫ y, H y ∂Measure.dirac a) (Measure.dirac a) := by
  have hmean : (∫ x, H x ∂Measure.dirac a) = H a :=
    integral_dirac' H a hH.stronglyMeasurable
  constructor
  · rw [hmean]
    exact ae_eq_dirac' hH
  · exact hHint.sub (integrable_const _)

/-- The literal square entropy vanishes under a Dirac law for every `L²`
function. -/
theorem squareEntropy_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (f : Lp ℝ 2 (Measure.dirac a)) :
    squareEntropy (Measure.dirac a) f = 0 := by
  let c : ℝ := f a
  have hfc : f =ᵐ[Measure.dirac a] fun _ => c := by
    filter_upwards [ae_eq_dirac f] with x hx
    simpa only [Function.const_apply, c] using hx
  have hsq : (fun x => (f x) ^ 2) =ᵐ[Measure.dirac a] fun _ => c ^ 2 :=
    hfc.fun_comp fun x : ℝ => x ^ 2
  have hpos :
      (fun x => ENNReal.ofReal ((f x) ^ 2 * Real.log ((f x) ^ 2))) =ᵐ[Measure.dirac a]
        fun _ => ENNReal.ofReal (c ^ 2 * Real.log (c ^ 2)) :=
    hfc.fun_comp fun x : ℝ => ENNReal.ofReal (x ^ 2 * Real.log (x ^ 2))
  have hneg :
      (fun x => ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2)))) =ᵐ[Measure.dirac a]
        fun _ => ENNReal.ofReal (-(c ^ 2 * Real.log (c ^ 2))) :=
    hfc.fun_comp fun x : ℝ => ENNReal.ofReal (-(x ^ 2 * Real.log (x ^ 2)))
  have hq : (∫ x, (f x) ^ 2 ∂Measure.dirac a) = c ^ 2 := by
    rw [integral_congr_ae hsq, integral_dirac]
  have hp :
      (∫⁻ x, ENNReal.ofReal ((f x) ^ 2 * Real.log ((f x) ^ 2)) ∂Measure.dirac a) =
        ENNReal.ofReal (c ^ 2 * Real.log (c ^ 2)) := by
    rw [lintegral_congr_ae hpos, lintegral_dirac]
  have hn :
      (∫⁻ x, ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2))) ∂Measure.dirac a) =
        ENNReal.ofReal (-(c ^ 2 * Real.log (c ^ 2))) := by
    rw [lintegral_congr_ae hneg, lintegral_dirac]
  rw [squareEntropy, hq, hp, hn]
  let q : ℝ := c ^ 2 * Real.log (c ^ 2)
  change ((((ENNReal.ofReal q : ℝ≥0∞) : EReal) -
      ((ENNReal.ofReal (-q) : ℝ≥0∞) : EReal) - (q : EReal)).toENNReal) = 0
  by_cases hqnonneg : 0 ≤ q
  · simp [EReal.coe_ennreal_ofReal, hqnonneg]
  · have hqneg : q < 0 := lt_of_not_ge hqnonneg
    simp [EReal.coe_ennreal_ofReal, max_eq_right hqneg.le,
      max_eq_left (le_of_lt (neg_pos.mpr hqneg))]

/-- The zero-entropy conclusion used by the Dirac branch of the zero-energy
Sobolev-pair consumer. -/
theorem squareEntropy_sobolevPair_zero_of_dirac {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι)
    (u : SobolevPair (Measure.dirac x)) :
    squareEntropy (Measure.dirac x) (WithLp.ofLp u.val).1 = 0 :=
  squareEntropy_dirac x (WithLp.ofLp u.val).1

end LOOConcentration.Revision
