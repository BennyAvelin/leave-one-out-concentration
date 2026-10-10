import LOOConcentration.FunctionalInequalities.EntropyTensorization
import LOOConcentrationRevision.FunctionalInequalities.EntropyClosure
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import LOOConcentrationRevision.FunctionalInequalities.EntropyComputation

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal

/-- Convert an actual bounded-generator inequality to the literal completed
pair inequality. The generator producer is an internal assembly premise. -/
theorem all_pairs_lsi_of_bounded_generator_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hGenerator : ∀ (F : EuclideanSpace ℝ ι → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) →
      LOOConcentration.entropy μ (fun x => (F x)^2) ≤
        2 * C * ∫ x, ‖gradient F x‖^2 ∂μ)
    (u : SobolevPair μ) :
    squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * ENNReal.ofReal C * sobolevEnergy μ u := by
  have hSmooth (p : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ))
      (hp : p ∈ smoothSobolevPairs μ) :
      squareEntropy μ (WithLp.ofLp p).1 ≤
        ENNReal.ofReal (2 * C * ‖(WithLp.ofLp p).2‖^2) := by
    obtain ⟨F, hF, ⟨B, hB, hbound⟩, hf, hg, rfl⟩ := hp
    have hsq (x : EuclideanSpace ℝ ι) : (F x)^2 ≤ B^2 := by
      rw [sq_le_sq, abs_of_nonneg hB]
      exact (hbound x).1
    obtain ⟨M, _, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (B^2))).bddAbove_image
      (continuous_norm.comp Real.continuous_mul_log).continuousOn |>.exists_ge 0
    have hDensity : Integrable (fun x => (F x)^2 * Real.log ((F x)^2)) μ := by
      refine Integrable.of_bound
        (Real.continuous_mul_log.measurable.comp (hF.continuous.measurable.pow_const 2)).aestronglyMeasurable M ?_
      exact Eventually.of_forall fun x => hM _ ⟨(F x)^2, ⟨sq_nonneg _, hsq x⟩, rfl⟩
    have hDensityLp : Integrable (fun x => (hf.toLp F x)^2 * Real.log ((hf.toLp F x)^2)) μ :=
      hDensity.congr (hf.coeFn_toLp.symm.mono fun x hx => by simpa only using congrArg (fun y : ℝ => y^2 * Real.log (y^2)) hx)
    rw [squareEntropy_eq_of_integrable_density _ hDensityLp]
    have hScalar : (∫ x, (hf.toLp F x)^2 ∂μ) = ∫ x, (F x)^2 ∂μ :=
      integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simpa only using congrArg (fun y : ℝ => y^2) hx)
    have hPhi : (∫ x, (hf.toLp F x)^2 * Real.log ((hf.toLp F x)^2) ∂μ) =
        ∫ x, (F x)^2 * Real.log ((F x)^2) ∂μ :=
      integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simpa only using congrArg (fun y : ℝ => y^2 * Real.log (y^2)) hx)
    have hEnergy : (∫ x, ‖gradient F x‖^2 ∂μ) = ‖hg.toLp (gradient F)‖^2 := by
      calc
        _ = ∫ x, ‖hg.toLp (gradient F) x‖^2 ∂μ :=
          integral_congr_ae (hg.coeFn_toLp.symm.mono fun x hx => by simpa only using congrArg (fun y => ‖y‖^2) hx)
        _ = _ := by
          rw [← real_inner_self_eq_norm_sq, L2.inner_def]
          simp only [real_inner_self_eq_norm_sq]
    rw [hScalar, hPhi]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [LOOConcentration.entropy, hEnergy] using hGenerator F hF B hB hbound)
  have h := all_pairs_lsi_bound_of_smooth_generators μ C hC hSmooth u
  rw [sobolevEnergy_eq_ofReal_norm_sq]
  convert h using 1
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The supremum-defined intrinsic constant inherits the actual generator
bound after completed-pair closure. No optimal-constant premise is supplied. -/
theorem logSobolevConstant_le_of_bounded_generator_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hGenerator : ∀ (F : EuclideanSpace ℝ ι → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B) →
      LOOConcentration.entropy μ (fun x => (F x)^2) ≤
        2 * C * ∫ x, ‖gradient F x‖^2 ∂μ) :
    logSobolevConstant μ ≤ ENNReal.ofReal C := by
  unfold logSobolevConstant
  refine iSup_le fun u => iSup_le fun hu => ?_
  have hE0 : 2 * sobolevEnergy μ u ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hu)
  have hEt : 2 * sobolevEnergy μ u ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (sobolevEnergy_lt_top u).ne
  rw [ENNReal.div_le_iff hE0 hEt]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    all_pairs_lsi_of_bounded_generator_bound μ C hC hGenerator u

end LOOConcentration.Revision
