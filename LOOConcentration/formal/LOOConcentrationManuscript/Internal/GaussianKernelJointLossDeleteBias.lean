import LOOConcentrationManuscript.Internal.GaussianKernelAbsoluteLossDeleteConsumer
import LOOConcentrationManuscript.Internal.KernelDeleteBiasEnvelopeIntegralConsumer
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory

/-- The actual stabilized Gaussian absolute fitted losses are integrable under
the joint training-sample and independent-test law, and their expected
delete-one difference is bounded by the manuscript's exact envelope. -/
theorem gaussianKernel_actual_joint_absoluteLoss_delete_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (i : Fin (r+2)) :
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let Q := P.prod μ
    let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let Tfull := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0)/
        ((∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ)
    let Tdel := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)*(p.1 (i.succAbove j)).2 0)/
        ((∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ)
    let Lfull := fun p => |Tfull p-(p.2.2 0)|
    let Ldel := fun p => |Tdel p-(p.2.2 0)|
    Integrable Lfull Q ∧ Integrable Ldel Q ∧
      Integrable (fun p => |Lfull p-Ldel p|) Q ∧
      (∫ p, |Lfull p-Ldel p| ∂Q) ≤ C*m/(r+2 : ℝ)*(2+C) ∧
      |(∫ p, Lfull p ∂Q)-(∫ p, Ldel p ∂Q)| ≤ C*m/(r+2 : ℝ)*(2+C) := by
  intro P Q C m Kh Tfull Tdel Lfull Ldel
  let Mdel := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    (∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)
  let Mfull := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    (∑ j : Fin (r+2), |(D j).2 0|)/((r+1 : ℝ)+1)
  let R := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*Mdel D)
  have hIID := iidResponse_full_and_deleted_absolute_mean μ hSecond
  have hYμ : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ := hIID.1
  have hFullStats := hIID.2.1 (r+1)
  have hDelStats := hIID.2.2 r i
  have hFullMean : Integrable Mfull P := by
    simpa only [Mfull, P, Nat.cast_add, Nat.cast_one] using hFullStats.1
  have hDelMean : Integrable Mdel P := by
    simpa only [Mdel, P] using hDelStats.1
  have hFullMeanQ : Integrable (fun p => Mfull p.1) Q := by
    exact hFullMean.comp_fst μ
  have hDelMeanQ : Integrable (fun p => Mdel p.1) Q := by
    exact hDelMean.comp_fst μ
  have hYQ : Integrable (fun p => |p.2.2 0|) Q := by
    exact hYμ.comp_snd P

  have hKhCont : Continuous Kh := (gaussianScaledKernel_value_and_derivative_bounds h hh).1.continuous
  have hKhNonneg : ∀ x, 0 ≤ Kh x :=
    (gaussianScaledKernel_value_and_derivative_bounds h hh).2.1
  have hFullWeight (j : Fin (r+2)) :
      Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 => Kh (p.2.1 0-(p.1 j).1 0)) := by
    exact hKhCont.comp (by fun_prop)
  have hDelWeight (j : Fin (r+1)) :
      Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 => Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)) := by
    exact hKhCont.comp (by fun_prop)
  have hFullNum : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        ∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0) := by
    exact continuous_finsetSum Finset.univ (fun j _ => (hFullWeight j).mul (by fun_prop))
  have hFullDen : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ) := by
    exact (continuous_finsetSum Finset.univ (fun j _ => hFullWeight j)).add continuous_const
  have hDelNum : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        ∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)*(p.1 (i.succAbove j)).2 0) := by
    exact continuous_finsetSum Finset.univ (fun j _ => (hDelWeight j).mul (by fun_prop))
  have hDelDen : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ) := by
    exact (continuous_finsetSum Finset.univ (fun j _ => hDelWeight j)).add continuous_const
  have hFullDenPos (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      0 < (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ := by
    apply add_pos_of_nonneg_of_pos
    · exact Finset.sum_nonneg (fun j _ => hKhNonneg _)
    · exact mul_pos (by positivity) hδ
  have hDelDenPos (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      0 < (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ := by
    apply add_pos_of_nonneg_of_pos
    · exact Finset.sum_nonneg (fun j _ => hKhNonneg _)
    · exact mul_pos (by positivity) hδ
  have hTfullCont : Continuous Tfull := by
    exact hFullNum.div hFullDen (fun p => ne_of_gt (hFullDenPos p))
  have hTdelCont : Continuous Tdel := by
    exact hDelNum.div hDelDen (fun p => ne_of_gt (hDelDenPos p))
  have hTestYCont : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 => p.2.2 0) := by fun_prop
  have hLfullMeas : Measurable Lfull := by
    dsimp [Lfull]
    exact (continuous_abs.measurable.comp (hTfullCont.sub hTestYCont).measurable)
  have hLdelMeas : Measurable Ldel := by
    dsimp [Ldel]
    exact (continuous_abs.measurable.comp (hTdelCont.sub hTestYCont).measurable)

  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFullPredictorBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Tfull p| ≤ C*Mfull p.1 := by
    have hb := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ (r+1) p.1 (p.2.1 0)
    have hSize : (r+2 : ℝ) = (r+1 : ℝ)+1 := by
      exact_mod_cast (show r+2 = (r+1)+1 by omega)
    simpa [Tfull, Mfull, Kh, C, hSize] using hb
  have hDelPredictorBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Tdel p| ≤ C*Mdel p.1 := by
    have hb := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r
      (fun j => p.1 (i.succAbove j)) (p.2.1 0)
    simpa [Tdel, Mdel, Kh, C, Nat.add_assoc] using hb
  have hFullLossBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      |Lfull p| ≤ C*Mfull p.1+|p.2.2 0| := by
    calc
      _ = |Tfull p-p.2.2 0| := by simp [Lfull]
      _ ≤ |Tfull p|+|p.2.2 0| := abs_sub _ _
      _ ≤ C*Mfull p.1+|p.2.2 0| := add_le_add (hFullPredictorBound p) le_rfl
  have hDelLossBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      |Ldel p| ≤ C*Mdel p.1+|p.2.2 0| := by
    calc
      _ = |Tdel p-p.2.2 0| := by simp [Ldel]
      _ ≤ |Tdel p|+|p.2.2 0| := abs_sub _ _
      _ ≤ C*Mdel p.1+|p.2.2 0| := add_le_add (hDelPredictorBound p) le_rfl
  have hFullMajorant : Integrable (fun p => C*Mfull p.1+|p.2.2 0|) Q :=
    (hFullMeanQ.const_mul C).add hYQ
  have hDelMajorant : Integrable (fun p => C*Mdel p.1+|p.2.2 0|) Q :=
    (hDelMeanQ.const_mul C).add hYQ
  have hLfullInt : Integrable Lfull Q := hFullMajorant.mono' hLfullMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hFullLossBound p)
  have hLdelInt : Integrable Ldel Q := hDelMajorant.mono' hLdelMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hDelLossBound p)
  have hLossDiffInt : Integrable (fun p => Lfull p-Ldel p) Q := hLfullInt.sub hLdelInt
  have hLossAbsDiffInt : Integrable (fun p => |Lfull p-Ldel p|) Q := by
    simpa only [Real.norm_eq_abs] using hLossDiffInt.norm

  have hEnvelopeStats := gaussianKernel_delete_bias_envelope_integral μ hSecond h δ hh hδ r i
  have hEnvelopeP : Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
      C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*Mdel D)) P := by
    simpa [C, Mdel, P] using hEnvelopeStats.1
  have hEnvelopeQ : Integrable (fun p => R p.1) Q := by
    simpa [R] using hEnvelopeP.comp_fst μ
  have hEnvelopePointwise (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Lfull p-Ldel p| ≤ R p.1 := by
    have hb := gaussianKernel_actualDataset_absoluteLoss_delete_bound h δ hh hδ r p.1
      (p.2.1 0) (p.2.2 0) i
    simpa [Lfull, Ldel, Tfull, Tdel, R, Mdel, Kh, C, Nat.add_assoc] using hb
  have hEnvelopeIntegralP :
      (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2),
        C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*Mdel D) ∂P) = C*m/(r+2 : ℝ)*(2+C) := by
    simpa [C, Mdel, P, m] using hEnvelopeStats.2.2
  have hEnvelopeIntegralQ : (∫ p, R p.1 ∂Q) = C*m/(r+2 : ℝ)*(2+C) := by
    calc
      _ = ∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2),
          C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*Mdel D) ∂P := by
        rw [integral_prod _ hEnvelopeQ]
        simp [R, Mdel]
      _ = C*m/(r+2 : ℝ)*(2+C) := hEnvelopeIntegralP
  have hDiffIntegralBound :
      (∫ p, |Lfull p-Ldel p| ∂Q) ≤ C*m/(r+2 : ℝ)*(2+C) := by
    calc
      _ ≤ ∫ p, R p.1 ∂Q := integral_mono hLossAbsDiffInt hEnvelopeQ
        (fun p => hEnvelopePointwise p)
      _ = C*m/(r+2 : ℝ)*(2+C) := hEnvelopeIntegralQ
  have hRiskDifferenceBound :
      |(∫ p, Lfull p ∂Q)-(∫ p, Ldel p ∂Q)| ≤ C*m/(r+2 : ℝ)*(2+C) := by
    calc
      _ = |∫ p, (Lfull p-Ldel p) ∂Q| := by rw [integral_sub hLfullInt hLdelInt]
      _ ≤ ∫ p, |Lfull p-Ldel p| ∂Q := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
            LOOConcentration.Observation 1 1 => Lfull p-Ldel p)
      _ ≤ C*m/(r+2 : ℝ)*(2+C) := hDiffIntegralBound
  exact ⟨hLfullInt, hLdelInt, hLossAbsDiffInt, hDiffIntegralBound, hRiskDifferenceBound⟩

end LOOConcentration.Manuscript.Internal
