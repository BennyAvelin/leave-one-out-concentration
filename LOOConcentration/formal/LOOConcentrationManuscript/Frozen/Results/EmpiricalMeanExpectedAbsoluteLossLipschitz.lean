import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_expectedAbsoluteLoss_lipschitz
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) :
    LipschitzWith 1 (fun z : ℝ =>
      ∫ ω, |empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z| ∂P)
:= by
  let : IsProbabilityMeasure P := hInd.isProbabilityMeasure
  have hIdLp : MemLp (id : ℝ → ℝ) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hSecond
  have hXInt : ∀ i, Integrable (X i) P :=
    fun i => ((hLaw i).memLp_iff.mpr hIdLp).integrable one_le_two
  let f : Ω → ℝ := fun ω => empiricalMean r (WithLp.toLp 2 (fun i => X i ω))
  have hf : Integrable f P := by
    simpa [f, empiricalMean] using
      (integrable_finsetSum Finset.univ (fun i _ => hXInt i)).const_mul (r + 1 : ℝ)⁻¹
  have hLoss (z : ℝ) : Integrable (fun ω => |f ω - z|) P :=
    (hf.sub (integrable_const z)).abs
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change |(∫ ω, |f ω - z| ∂P) - (∫ ω, |f ω - w| ∂P)| ≤
    (1 : ℝ) * |z - w|
  rw [one_mul, ← integral_sub (hLoss z) (hLoss w)]
  have hBound : ∀ᵐ ω ∂P, ‖|f ω - z| - |f ω - w|‖ ≤ |z - w| := by
    filter_upwards with ω
    change |(|f ω - z| - |f ω - w|)| ≤ |z - w|
    have hh := abs_abs_sub_abs_le_abs_sub (f ω - z) (f ω - w)
    have heq : (f ω - z) - (f ω - w) = -(z - w) := by ring
    simpa only [heq, abs_neg] using hh
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const hBound)


end LOOConcentration.Manuscript
