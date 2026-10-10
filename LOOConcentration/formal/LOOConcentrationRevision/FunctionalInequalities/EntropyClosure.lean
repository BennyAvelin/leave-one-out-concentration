import LOOConcentrationRevision.FunctionalInequalities.EntropyLimit
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- A finite entropy envelope passes to an actual scalar L2 limit, using Fatou
for the positive density and continuity of its uniformly bounded negative part. -/
theorem squareEntropy_le_of_tendsto_envelope
    (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hmean : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop
      (nhds (∫ x, (g x)^2 ∂μ)))
    (s : ℕ → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hs : ∀ n, 0 ≤ s n) (hlim : Tendsto s atTop (nhds K))
    (hb : ∀ n, squareEntropy μ (f n) ≤ ENNReal.ofReal (s n)) :
    squareEntropy μ g ≤ ENNReal.ofReal K := by
  let P : Lp ℝ 2 μ → ℝ≥0∞ := fun v =>
    ∫⁻ x, ENNReal.ofReal ((v x)^2 * Real.log ((v x)^2)) ∂μ
  let N : Lp ℝ 2 μ → ℝ≥0∞ := fun v =>
    ∫⁻ x, ENNReal.ofReal (-((v x)^2 * Real.log ((v x)^2))) ∂μ
  let M : Lp ℝ 2 μ → ℝ := fun v =>
    (∫ x, (v x)^2 ∂μ) * Real.log (∫ x, (v x)^2 ∂μ)
  have hi (n : ℕ) : Integrable (fun x => (f n x)^2 * Real.log ((f n x)^2)) μ :=
    (squareEntropy_lt_top_iff_integrable_density (f n)).mp
      ((hb n).trans_lt ENNReal.ofReal_lt_top)
  have hpfinite (n : ℕ) : P (f n) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (hi n).2).ne
  have hnfinite (v : Lp ℝ 2 μ) : N v ≠ ⊤ := (squareEntropy_negative_part_lt_top v).ne
  have hidentity (n : ℕ) : (P (f n)).toReal =
      (squareEntropy μ (f n)).toReal + (N (f n)).toReal + M (f n) := by
    have h := positive_density_eq_entropy_add_negative (f n) (hi n)
    rw [← EReal.coe_ennreal_toReal (hpfinite n),
      ← EReal.coe_ennreal_toReal ((hb n).trans_lt ENNReal.ofReal_lt_top).ne,
      ← EReal.coe_ennreal_toReal (hnfinite (f n)), ← EReal.coe_add,
      ← EReal.coe_add] at h
    exact EReal.coe_injective h
  have hbound (n : ℕ) : (P (f n)).toReal ≤ s n + (N (f n)).toReal + M (f n) := by
    rw [hidentity]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb n)
    rw [ENNReal.toReal_ofReal (hs n)] at h
    linarith only [h]
  have hN : Tendsto (fun n => (N (f n)).toReal) atTop (nhds ((N g).toReal)) :=
    (ENNReal.tendsto_toReal (hnfinite g)).comp (tendsto_negative_density_integral f g hfg)
  have hM : Tendsto (fun n => M (f n)) atTop (nhds (M g)) :=
    (Real.continuous_mul_log.tendsto (∫ x, (g x)^2 ∂μ)).comp hmean
  have hU := (hlim.add hN).add hM
  have hUnonneg (n : ℕ) : 0 ≤ s n + (N (f n)).toReal + M (f n) :=
    ENNReal.toReal_nonneg.trans (hbound n)
  have hUpos : 0 ≤ K + (N g).toReal + M g :=
    ge_of_tendsto hU (Eventually.of_forall hUnonneg)
  have hPbound (n : ℕ) : P (f n) ≤ ENNReal.ofReal
      (s n + (N (f n)).toReal + M (f n)) := by
    rw [← ENNReal.ofReal_toReal (hpfinite n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hpoint : ∀ᵐ x ∂μ, Tendsto
      (fun n => ENNReal.ofReal ((f n x)^2 * Real.log ((f n x)^2))) atTop
      (nhds (ENNReal.ofReal ((g x)^2 * Real.log ((g x)^2)))) := by
    filter_upwards [hfg] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_mul_log.tendsto ((g x)^2)).comp (hx.pow 2))
  have hFatou : P g ≤ ENNReal.ofReal (K + (N g).toReal + M g) := by
    calc
      P g = ∫⁻ x, liminf
          (fun n => ENNReal.ofReal ((f n x)^2 * Real.log ((f n x)^2))) atTop ∂μ :=
        lintegral_congr_ae (hpoint.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => P (f n)) atTop := lintegral_liminf_le' fun n =>
        (Real.continuous_mul_log.comp_aestronglyMeasurable
          (integrable_sq (f n)).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      _ ≤ liminf (fun n => ENNReal.ofReal
          (s n + (N (f n)).toReal + M (f n))) atTop :=
        liminf_le_liminf (Eventually.of_forall hPbound)
      _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hU).liminf_eq
  have hg := integrable_density_of_positive_part_ne_top g
    ((hFatou.trans_lt ENNReal.ofReal_lt_top).ne)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [ENNReal.toReal_ofReal hUpos] at hreal
  rw [squareEntropy_eq_of_integrable_density g hg]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  change (P g).toReal - (N g).toReal - M g ≤ K
  linarith only [hreal]

/-- The literal completed pair carrier inherits a finite entropy-energy bound
from actual smooth generators. The smooth LSI producer remains an internal input. -/
theorem all_pairs_lsi_bound_of_smooth_generators
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (C : ℝ) (hC : 0 ≤ C)
    (hSmooth : ∀ p : WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν),
      p ∈ smoothSobolevPairs ν → squareEntropy ν (WithLp.ofLp p).1 ≤
        ENNReal.ofReal (2 * C * ‖(WithLp.ofLp p).2‖ ^ 2))
    (u : SobolevPair ν) :
    squareEntropy ν (WithLp.ofLp u.val).1 ≤
      ENNReal.ofReal (2 * C * ‖(WithLp.ofLp u.val).2‖ ^ 2) := by
  obtain ⟨f, hf, hfu⟩ := mem_closure_iff_seq_limit.mp u.property
  let P := (ContinuousLinearMap.fst ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ ι) 2 ν)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ ι) 2 ν)).toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ ι) 2 ν)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ ι) 2 ν)).toContinuousLinearMap
  have hscalar : Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop
      (nhds (WithLp.ofLp u.val).1) := P.continuous.tendsto _ |>.comp hfu
  have hgradient : Tendsto (fun n => (WithLp.ofLp (f n)).2) atTop
      (nhds (WithLp.ofLp u.val).2) := Q.continuous.tendsto _ |>.comp hfu
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hscalar).exists_seq_tendsto_ae
  have hscalarφ := hscalar.comp hφ.tendsto_atTop
  have hgradientφ := hgradient.comp hφ.tendsto_atTop
  let s : ℕ → ℝ := fun n => 2 * C * ‖(WithLp.ofLp (f (φ n))).2‖ ^ 2
  let K : ℝ := 2 * C * ‖(WithLp.ofLp u.val).2‖ ^ 2
  have hs (n : ℕ) : 0 ≤ s n := by dsimp [s]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim : Tendsto s atTop (nhds K) := (hgradientφ.norm.pow 2).const_mul (2 * C)
  exact squareEntropy_le_of_tendsto_envelope
    (fun n => (WithLp.ofLp (f (φ n))).1) (WithLp.ofLp u.val).1 hae
    (tendsto_integral_sq_of_tendsto_Lp _ _ hscalarφ) s K hK hs hlim
    (fun n => hSmooth (f (φ n)) (hf (φ n)))

end LOOConcentration.Revision
