import LOOConcentrationRevision.FunctionalInequalities.GradientSegment
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter Set
open scoped Topology Gradient

/-- A volume-a.e. polynomial gradient bound controls the function on every
closed ball. The proof uses the translated-segment argument, so it does not
pull an ambient null set back through a clipping map. -/
theorem polynomialGradient_lipschitzOn_closedBall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F)
    (A q R : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hgrad : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖gradient F w‖ ≤ A * ‖w‖ ^ q)
    (x y : EuclideanSpace ℝ ι)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |F x - F y| ≤ A * R ^ q * ‖x - y‖ := by
  let path (z : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
    (1 - t) • x + t • y + z
  let affine (z : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
    x + z + t • (y - x)
  have hpath (z : EuclideanSpace ℝ ι) (t : ℝ) : path z t = affine z t := by
    dsimp [path, affine]
    rw [sub_smul, one_smul, smul_sub]
    abel
  let left : EuclideanSpace ℝ ι → ℝ := fun z => |F (y + z) - F (x + z)|
  have hleftCont : Continuous left := by
    have hFc : Continuous F := hF.continuous
    dsimp [left]
    exact continuous_abs.comp
      ((hFc.comp (continuous_const.add continuous_id)).sub
        (hFc.comp (continuous_const.add continuous_id)))

  have hbound (ε : ℝ) (hε : 0 < ε) :
      |F x - F y| ≤ A * (R + ε) ^ q * ‖y - x‖ := by
    let source (w : EuclideanSpace ℝ ι) : Prop :=
      DifferentiableAt ℝ F w ∧ ‖gradient F w‖ ≤ A * ‖w‖ ^ q
    have haeDiff :=
      LOOConcentration.Revision.locallyLipschitz_ae_differentiableAt F hF
    have hsource : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ ι)), source w := by
      filter_upwards [haeDiff, hgrad] with w hdiff hnorm
      exact ⟨hdiff, hnorm⟩
    have hshift := LOOConcentration.Revision.ae_shifted_segment_of_ae
      source hsource x y
    have hQae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)),
        z ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ε →
          left z ≤ A * (R + ε) ^ q * ‖y - x‖ := by
      filter_upwards [hshift] with z hz
      intro hzSmall
      let g (t : ℝ) : ℝ := F (path z t)
      have hgammaLip : LipschitzWith ‖y - x‖₊ (affine z) := by
        apply lipschitzWith_iff_dist_le_mul.mpr
        intro s t
        have hdiff : affine z s - affine z t = (s - t) • (y - x) := by
          dsimp [affine]
          rw [add_sub_add_left_eq_sub, ← sub_smul]
        rw [dist_eq_norm, dist_eq_norm, hdiff, norm_smul, coe_nnnorm]
        ring_nf
        exact le_rfl
      have hgammaLoc : LocallyLipschitz (affine z) := hgammaLip.locallyLipschitz
      have hgLoc : LocallyLipschitz g := by
        have hc := hF.comp hgammaLoc
        simpa [g, Function.comp_def, path, hpath] using hc
      have hgLocOn : LocallyLipschitzOn (Icc (0 : ℝ) 1) g :=
        hgLoc.locallyLipschitzOn
      obtain ⟨K, hK⟩ :=
        LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hgLocOn
      have hac : AbsolutelyContinuousOnInterval g 0 1 := by
        have hK' : LipschitzOnWith K g (uIcc (0 : ℝ) 1) := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hK
        exact hK'.absolutelyContinuousOnInterval
      have hgammaDeriv' (t : ℝ) :
          HasDerivAt (path z) ((-1 : ℝ) • x + (1 : ℝ) • y) t := by
        have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
          (hasDerivAt_id t).const_sub (1 : ℝ)
        have hsum := (h1.smul_const x).add ((hasDerivAt_id t).smul_const y)
        have hsum' := hsum.add_const z
        simpa [path] using hsum'
      have hv : (-1 : ℝ) • x + (1 : ℝ) • y = y - x := by
        simp [sub_eq_add_neg, add_comm]
      have hgammaDeriv (t : ℝ) : HasDerivAt (path z) (y - x) t := by
        rw [← hv]
        exact hgammaDeriv' t
      have hpathNorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          ‖path z t‖ ≤ R + ε := by
        rcases ht with ⟨ht0, ht1⟩
        have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
        have hcomb : ‖(1 - t) • x + t • y‖ ≤ R := by
          calc
            ‖(1 - t) • x + t • y‖ ≤ (1 - t) * ‖x‖ + t * ‖y‖ := by
              calc
                _ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
                _ = (1 - t) * ‖x‖ + t * ‖y‖ := by
                  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                    abs_of_nonneg h1t, abs_of_nonneg ht0]
            _ ≤ (1 - t) * R + t * R := by gcongr
            _ = R := by ring
        calc
          ‖path z t‖ ≤ ‖(1 - t) • x + t • y‖ + ‖z‖ := norm_add_le _ _
          _ ≤ R + ε := by
            have hzNorm : ‖z‖ < ε := by
              have hzDist : dist z (0 : EuclideanSpace ℝ ι) < ε :=
                Metric.mem_ball.mp hzSmall
              rw [dist_eq_norm, sub_zero] at hzDist
              exact hzDist
            exact add_le_add hcomb hzNorm.le
      have hderiv : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          |deriv g t| ≤ ‖y - x‖ * (A * (R + ε) ^ q) := by
        filter_upwards [hz, ae_restrict_mem measurableSet_Icc] with t htgood ht
        rcases htgood with ⟨hdiff, hgradAt⟩
        have hchain : HasDerivAt (fun s => F (path z s))
            (fderiv ℝ F (path z t) (y - x)) t :=
          hdiff.hasFDerivAt.comp_hasDerivAt t (hgammaDeriv t)
        have hderivEq : deriv g t = fderiv ℝ F (path z t) (y - x) := by
          change deriv (fun s => F (path z s)) t = _
          exact hchain.deriv
        have hGradNorm : ‖gradient F (path z t)‖ =
            ‖fderiv ℝ F (path z t)‖ := by
          rw [gradient,
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
        have hpow : ‖path z t‖ ^ q ≤ (R + ε) ^ q :=
          Real.rpow_le_rpow (norm_nonneg _) (hpathNorm t ht) hq
        calc
          |deriv g t| = ‖fderiv ℝ F (path z t) (y - x)‖ := by
            rw [Real.norm_eq_abs, hderivEq]
          _ ≤ ‖fderiv ℝ F (path z t)‖ * ‖y - x‖ :=
            (fderiv ℝ F (path z t)).le_opNorm (y - x)
          _ = ‖gradient F (path z t)‖ * ‖y - x‖ := by rw [hGradNorm]
          _ ≤ (A * ‖path z t‖ ^ q) * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right hgradAt (norm_nonneg _)
          _ ≤ (A * (R + ε) ^ q) * ‖y - x‖ := by
            gcongr
          _ = ‖y - x‖ * (A * (R + ε) ^ q) := by ring
      have hsegment := LOOConcentration.Revision.interval_abs_sub_le_shifted_segment_growth
        g x y z (A * (R + ε) ^ q) 0 hac (by norm_num) (by
          simpa only [zero_mul, add_zero] using hderiv)
      have hseg' : |F (y + z) - F (x + z)| ≤
          A * (R + ε) ^ q * ‖y - x‖ := by
        calc
          |F (y + z) - F (x + z)| ≤ ‖y - x‖ * (A * (R + ε) ^ q) := by
            simpa [g, path, zero_mul, add_zero] using hsegment
          _ = A * (R + ε) ^ q * ‖y - x‖ := by ring
      simpa only [left] using hseg'

    have hbad : (volume : Measure (EuclideanSpace ℝ ι))
        {z | ¬ (z ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ε →
          left z ≤ A * (R + ε) ^ q * ‖y - x‖)} = 0 := ae_iff.mp hQae
    have hzero : left (0 : EuclideanSpace ℝ ι) ≤ A * (R + ε) ^ q * ‖y - x‖ := by
      by_contra hnot
      have hstrict : A * (R + ε) ^ q * ‖y - x‖ < left 0 := lt_of_not_ge hnot
      let U : Set (EuclideanSpace ℝ ι) := Metric.ball (0 : EuclideanSpace ℝ ι) ε ∩
        {z | A * (R + ε) ^ q * ‖y - x‖ < left z}
      have hUopen : IsOpen U :=
        IsOpen.inter Metric.isOpen_ball (isOpen_lt continuous_const hleftCont)
      have hU0 : (0 : EuclideanSpace ℝ ι) ∈ U := by
        refine ⟨Metric.mem_ball_self hε, ?_⟩
        simpa [left, zero_add] using hstrict
      have hUpos : (volume : Measure (EuclideanSpace ℝ ι)) U ≠ 0 :=
        hUopen.measure_ne_zero volume ⟨0, hU0⟩
      have hUsub : U ⊆ {z | ¬ (z ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ε →
          left z ≤ A * (R + ε) ^ q * ‖y - x‖)} := by
        rintro z ⟨hzBall, hzBad⟩ himp
        exact (not_le_of_gt hzBad) (himp hzBall)
      have hUzero : (volume : Measure (EuclideanSpace ℝ ι)) U = 0 :=
        measure_mono_null hUsub hbad
      exact hUpos hUzero
    simpa only [left, add_zero, abs_sub_comm] using hzero

  let rhs : ℝ → ℝ := fun ε => A * (R + ε) ^ q * ‖x - y‖
  have hrhsCont : ContinuousAt rhs 0 := by
    dsimp [rhs]
    have hbase : ContinuousAt (fun ε : ℝ => R + ε) 0 :=
      continuousAt_const.add continuousAt_id
    have houter : ContinuousAt (fun s : ℝ => s ^ q) (R + 0) := by
      simpa only [add_zero] using Real.continuousAt_rpow_const R q (Or.inr hq)
    have hpow : ContinuousAt (fun ε : ℝ => (R + ε) ^ q) 0 :=
      by simpa only [Function.comp_def] using houter.comp hbase
    exact (continuousAt_const.mul hpow).mul continuousAt_const
  have hrhsLimit : Tendsto rhs (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (A * R ^ q * ‖x - y‖)) := by
    have h := hrhsCont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa [rhs] using h
  have hboundEventually : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ),
      |F x - F y| ≤ rhs ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [rhs, norm_sub_rev] using hbound ε hε
  have hfinal := le_of_tendsto_of_tendsto tendsto_const_nhds hrhsLimit hboundEventually
  simpa only [norm_sub_rev] using hfinal

end LOOConcentration.Manuscript.Internal
