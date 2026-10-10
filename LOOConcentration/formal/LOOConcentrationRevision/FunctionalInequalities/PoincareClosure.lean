import LOOConcentrationRevision.FunctionalInequalities.EntropyLimit
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Sequences

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology

/-- The actual integral mean is continuous in the scalar L² carrier. -/
theorem tendsto_integral_of_tendsto_L2
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  let one : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top μ Set.univ) (1 : ℝ)
  have heq (v : Lp ℝ 2 μ) : inner ℝ one v = ∫ x, v x ∂μ := by
    simpa only [one, setIntegral_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ Set.univ) v
  have hi : Tendsto (fun n => inner ℝ one (f n)) atTop (𝓝 (inner ℝ one g)) :=
    tendsto_const_nhds.inner h
  simpa only [heq] using hi

/-- Strong scalar L² convergence retains the actual centered square integral. -/
theorem tendsto_centered_square_integral_of_tendsto_L2
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ x, (f n x - ∫ y, f n y ∂μ)^2 ∂μ) atTop
      (𝓝 (∫ x, (g x - ∫ y, g y ∂μ)^2 ∂μ)) := by
  have heq (v : Lp ℝ 2 μ) : (∫ x, (v x - ∫ y, v y ∂μ)^2 ∂μ) =
      (∫ x, (v x)^2 ∂μ) - (∫ x, v x ∂μ)^2 := by
    rw [← ProbabilityTheory.variance_eq_integral ((Lp.aestronglyMeasurable v).aemeasurable),
      ProbabilityTheory.variance_eq_sub (Lp.memLp v)]
    rfl
  simp_rw [heq]
  exact (tendsto_integral_sq_of_tendsto_Lp f g h).sub
    ((tendsto_integral_of_tendsto_L2 μ f g h).pow 2)

/-- The literal completed scalar/retained-gradient carrier inherits the generator
variance bound. Its universal generator premise needs an actual LSI producer. -/
theorem completed_pair_poincare_of_generator_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ)
    (hSmooth : ∀ p : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ),
      p ∈ smoothSobolevPairs μ →
      (∫ x, ((WithLp.ofLp p).1 x - ∫ y, (WithLp.ofLp p).1 y ∂μ)^2 ∂μ) ≤
        C * ‖(WithLp.ofLp p).2‖^2)
    (u : SobolevPair μ) :
    (∫ x, ((WithLp.ofLp u.val).1 x - ∫ y, (WithLp.ofLp u.val).1 y ∂μ)^2 ∂μ) ≤
      C * (sobolevEnergy μ u).toReal := by
  obtain ⟨f, hf, hfu⟩ := mem_closure_iff_seq_limit.mp u.property
  let P := (ContinuousLinearMap.fst ℝ (Lp ℝ 2 μ) (Lp (EuclideanSpace ℝ ι) 2 μ)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 μ)
      (Lp (EuclideanSpace ℝ ι) 2 μ)).toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (Lp ℝ 2 μ) (Lp (EuclideanSpace ℝ ι) 2 μ)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 μ)
      (Lp (EuclideanSpace ℝ ι) 2 μ)).toContinuousLinearMap
  have hscalar : Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop
      (𝓝 (WithLp.ofLp u.val).1) := P.continuous.tendsto _ |>.comp hfu
  have hgrad : Tendsto (fun n => (WithLp.ofLp (f n)).2) atTop
      (𝓝 (WithLp.ofLp u.val).2) := Q.continuous.tendsto _ |>.comp hfu
  have hlim := tendsto_centered_square_integral_of_tendsto_L2 μ _ _ hscalar
  have hrhs := (hgrad.norm.pow 2).const_mul C
  rw [sobolevEnergy_eq_ofReal_norm_sq, ENNReal.toReal_ofReal (sq_nonneg _)]
  exact le_of_tendsto_of_tendsto hlim hrhs (Eventually.of_forall fun n => hSmooth (f n) (hf n))

end LOOConcentration.Revision
