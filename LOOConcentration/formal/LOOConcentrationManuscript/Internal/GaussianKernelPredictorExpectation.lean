import LOOConcentrationManuscript.Internal.GaussianKernelResponseMeanBound
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean
import LOOConcentrationManuscript.Internal.GaussianKernelDeleteIdentity
import LOOConcentrationManuscript.Internal.KernelDeleteBiasEnvelopeIntegralConsumer
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory

/-- At every fixed query, the source Gaussian predictor has absolute expectation
at most the response first moment times its common kernel constant. -/
theorem gaussianKernel_predictor_fixed_query_first_moment
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∀ (r : ℕ) (x : ℝ),
    let P := Measure.pi (fun _ : Fin (r+1) => μ)
    let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let T := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ j : Fin (r+1), Kh (x-(D j).1 0)*(D j).2 0)/
        ((∑ j : Fin (r+1), Kh (x-(D j).1 0))+(r+1 : ℝ)*δ)
    Integrable T P ∧ Integrable (fun D => |T D|) P ∧
      (∫ D, |T D| ∂P) ≤ C*m := by
  classical
  intro r x P C m Kh T
  let M := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
    (∑ j : Fin (r+1), |(D j).2 0|)/(r+1 : ℝ)
  have hIID := iidResponse_full_and_deleted_absolute_mean μ hSecond
  have hStats := hIID.2.1 r
  have hMInt : Integrable M P := by simpa [M, P] using hStats.1
  have hMMean : (∫ D, M D ∂P) = m := by simpa [M, P, m] using hStats.2.1
  have hKhCont : Continuous Kh := (gaussianScaledKernel_value_and_derivative_bounds h hh).1.continuous
  have hKhNonneg : ∀ t, 0 ≤ Kh t := (gaussianScaledKernel_value_and_derivative_bounds h hh).2.1
  have hWeight (j : Fin (r+1)) : Continuous
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
        Kh (x-(D j).1 0)) := hKhCont.comp (by fun_prop)
  have hNum : Continuous (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      ∑ j : Fin (r+1), Kh (x-(D j).1 0)*(D j).2 0) :=
    continuous_finsetSum Finset.univ (fun j _ => (hWeight j).mul (by fun_prop))
  have hDen : Continuous (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ j : Fin (r+1), Kh (x-(D j).1 0))+(r+1 : ℝ)*δ) :=
    (continuous_finsetSum Finset.univ (fun j _ => hWeight j)).add continuous_const
  have hDenPos (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) :
      0 < (∑ j : Fin (r+1), Kh (x-(D j).1 0))+(r+1 : ℝ)*δ :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => hKhNonneg _)
      (mul_pos (by positivity) hδ)
  have hTCont : Continuous T := by
    dsimp [T]
    exact hNum.div hDen (fun D => ne_of_gt (hDenPos D))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) :
      |T D| ≤ C*M D := by
    have hb := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r D x
    simpa [T, M, Kh, C, Nat.add_assoc] using hb
  have hMajorant : Integrable (fun D => C*M D) P := hMInt.const_mul C
  have hTInt : Integrable T P := hMajorant.mono' hTCont.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun D => by
      rw [Real.norm_eq_abs]
      exact hBound D)
  have hAbsInt : Integrable (fun D => |T D|) P := by
    simpa only [Real.norm_eq_abs] using hTInt.norm
  refine ⟨hTInt, hAbsInt, ?_⟩
  calc
    (∫ D, |T D| ∂P) ≤ ∫ D, C*M D ∂P :=
      integral_mono hAbsInt hMajorant (fun D => hBound D)
    _ = C*m := by rw [integral_const_mul, hMMean]

/-- Under the actual joint training and independent-test law, both the full
and every ordered deleted predictor have integrable absolute value and first
moment at most the same source constant times the response first moment. -/
theorem gaussianKernel_actual_joint_predictor_first_moments
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
    Integrable Tfull Q ∧ Integrable Tdel Q ∧
      Integrable (fun p => |Tfull p|) Q ∧ (∫ p, |Tfull p| ∂Q) ≤ C*m ∧
      Integrable (fun p => |Tdel p|) Q ∧ (∫ p, |Tdel p| ∂Q) ≤ C*m := by
  classical
  intro P Q C m Kh Tfull Tdel
  let Mfull := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    (∑ j : Fin (r+2), |(D j).2 0|)/((r+1 : ℝ)+1)
  let Mdel := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    (∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)
  have hIID := iidResponse_full_and_deleted_absolute_mean μ hSecond
  have hFullStats := hIID.2.1 (r+1)
  have hDelStats := hIID.2.2 r i
  have hFullMean : Integrable Mfull P ∧ (∫ D, Mfull D ∂P) = m := by
    refine ⟨?_, ?_⟩
    · simpa only [Mfull, P, Nat.cast_add, Nat.cast_one] using hFullStats.1
    · simpa only [Mfull, P, Nat.cast_add, Nat.cast_one, m] using hFullStats.2.1
  have hDelMean : Integrable Mdel P ∧ (∫ D, Mdel D ∂P) = m := by
    simpa only [Mdel, P, m] using hDelStats
  have hFullMeanQ : Integrable (fun p => Mfull p.1) Q := hFullMean.1.comp_fst μ
  have hDelMeanQ : Integrable (fun p => Mdel p.1) Q := hDelMean.1.comp_fst μ
  have hKhCont : Continuous Kh := (gaussianScaledKernel_value_and_derivative_bounds h hh).1.continuous
  have hKhNonneg : ∀ t, 0 ≤ Kh t := (gaussianScaledKernel_value_and_derivative_bounds h hh).2.1
  have hFullWeight (j : Fin (r+2)) : Continuous
      (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 => Kh (p.2.1 0-(p.1 j).1 0)) :=
    hKhCont.comp (by fun_prop)
  have hDelWeight (j : Fin (r+1)) : Continuous
      (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 => Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)) :=
    hKhCont.comp (by fun_prop)
  have hFullNum : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        ∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0) :=
    continuous_finsetSum Finset.univ (fun j _ => (hFullWeight j).mul (by fun_prop))
  have hFullDen : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ) :=
    (continuous_finsetSum Finset.univ (fun j _ => hFullWeight j)).add continuous_const
  have hDelNum : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        ∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)*(p.1 (i.succAbove j)).2 0) :=
    continuous_finsetSum Finset.univ (fun j _ => (hDelWeight j).mul (by fun_prop))
  have hDelDen : Continuous (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1 =>
        (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ) :=
    (continuous_finsetSum Finset.univ (fun j _ => hDelWeight j)).add continuous_const
  have hFullDenPos (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      0 < (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => hKhNonneg _)
      (mul_pos (by positivity) hδ)
  have hDelDenPos (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) :
      0 < (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => hKhNonneg _)
      (mul_pos (by positivity) hδ)
  have hTfullCont : Continuous Tfull := by
    exact hFullNum.div hFullDen (fun p => ne_of_gt (hFullDenPos p))
  have hTdelCont : Continuous Tdel := by
    exact hDelNum.div hDelDen (fun p => ne_of_gt (hDelDenPos p))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFullBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Tfull p| ≤ C*Mfull p.1 := by
    have hb := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ (r+1) p.1 (p.2.1 0)
    have hSize : (r+2 : ℝ) = (r+1 : ℝ)+1 := by exact_mod_cast (show r+2 = (r+1)+1 by omega)
    simpa [Tfull, Mfull, Kh, C, hSize] using hb
  have hDelBound (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Tdel p| ≤ C*Mdel p.1 := by
    have hb := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r
      (fun j => p.1 (i.succAbove j)) (p.2.1 0)
    simpa [Tdel, Mdel, Kh, C, Nat.add_assoc] using hb
  have hFullMaj : Integrable (fun p => C*Mfull p.1) Q := hFullMeanQ.const_mul C
  have hDelMaj : Integrable (fun p => C*Mdel p.1) Q := hDelMeanQ.const_mul C
  have hTfullInt : Integrable Tfull Q := hFullMaj.mono' hTfullCont.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hFullBound p)
  have hTdelInt : Integrable Tdel Q := hDelMaj.mono' hTdelCont.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hDelBound p)
  have hAbsFull : Integrable (fun p => |Tfull p|) Q := by
    simpa only [Real.norm_eq_abs] using hTfullInt.norm
  have hAbsDel : Integrable (fun p => |Tdel p|) Q := by
    simpa only [Real.norm_eq_abs] using hTdelInt.norm
  have hFullMeanQExact : (∫ p, Mfull p.1 ∂Q) = m := by
    calc
      _ = ∫ D, Mfull D ∂P := by
        rw [integral_prod _ hFullMeanQ]
        simp
      _ = m := hFullMean.2
  have hDelMeanQExact : (∫ p, Mdel p.1 ∂Q) = m := by
    calc
      _ = ∫ D, Mdel D ∂P := by
        rw [integral_prod _ hDelMeanQ]
        simp
      _ = m := hDelMean.2
  refine ⟨hTfullInt, hTdelInt, hAbsFull, ?_, hAbsDel, ?_⟩
  · calc
      (∫ p, |Tfull p| ∂Q) ≤ ∫ p, C*Mfull p.1 ∂Q :=
        integral_mono hAbsFull hFullMaj (fun p => hFullBound p)
      _ = C*m := by rw [integral_const_mul, hFullMeanQExact]
  · calc
      (∫ p, |Tdel p| ∂Q) ≤ ∫ p, C*Mdel p.1 ∂Q :=
        integral_mono hAbsDel hDelMaj (fun p => hDelBound p)
      _ = C*m := by rw [integral_const_mul, hDelMeanQExact]

/-- The actual predictor difference is integrable under the joint test law;
the accepted delete identity and envelope integral give its exact source rate. -/
theorem gaussianKernel_actual_joint_predictor_difference_first_moment
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
    let Mdel := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
      (∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)
    let R := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
      C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*Mdel D)
    Integrable (fun p => |Tfull p-Tdel p|) Q ∧
      (∀ p, |Tfull p-Tdel p| ≤ R p.1) ∧
      (∫ p, |Tfull p-Tdel p| ∂Q) ≤ C*m/(r+2 : ℝ)*(2+C) := by
  classical
  intro P Q C m Kh Tfull Tdel Mdel R
  have hFirst := gaussianKernel_actual_joint_predictor_first_moments μ hSecond h δ hh hδ r i
  have hDiffInt : Integrable (fun p => Tfull p-Tdel p) Q := hFirst.1.sub hFirst.2.1
  have hAbsDiffInt : Integrable (fun p => |Tfull p-Tdel p|) Q := by
    simpa only [Real.norm_eq_abs] using hDiffInt.norm
  have hEnvelope := gaussianKernel_delete_bias_envelope_integral μ hSecond h δ hh hδ r i
  have hRP : Integrable R P := by simpa [R, C, Mdel, P] using hEnvelope.1
  have hRQ : Integrable (fun p => R p.1) Q := hRP.comp_fst μ
  have hPoint (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
      LOOConcentration.Observation 1 1) : |Tfull p-Tdel p| ≤ R p.1 := by
    change |Tfull p-Tdel p| ≤ C/(r+2 : ℝ)*
      (|(p.1 i).2 0|+(1+C)*Mdel p.1)
    have hId := gaussianKernel_actualDataset_delete_identity_and_bound h δ hh hδ r p.1
      (p.2.1 0) i
    have hRaw : |Tfull p-Tdel p| ≤
        (((Real.sqrt (2*Real.pi))⁻¹/h)*|(p.1 i).2 0|+
          (((Real.sqrt (2*Real.pi))⁻¹/h)+δ)*|Tdel p|)/((r+2 : ℝ)*δ) := by
      simpa [Tfull, Tdel, Kh] using hId.2
    have hPred := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r
      (fun j => p.1 (i.succAbove j)) (p.2.1 0)
    have hDelPred : |Tdel p| ≤ C*Mdel p.1 := by
      simpa [Tdel, Mdel, Kh, C, Nat.add_assoc] using hPred
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hNδ : 0 < (r+2 : ℝ)*δ := mul_pos (by positivity) hδ
    have hRel : ((Real.sqrt (2*Real.pi))⁻¹/h) = C*δ := by dsimp [C]; field_simp
    rw [hRel] at hRaw
    calc
      _ ≤ (C*δ*|(p.1 i).2 0|+(C*δ+δ)*|Tdel p|)/((r+2 : ℝ)*δ) := hRaw
      _ ≤ (C*δ*|(p.1 i).2 0|+(C*δ+δ)*(C*Mdel p.1))/((r+2 : ℝ)*δ) :=
        div_le_div_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hDelPred (by positivity))) hNδ.le
      _ = R p.1 := by
        dsimp [R]
        have hN : (0 : ℝ) < (r+2 : ℝ) := by positivity
        field_simp [ne_of_gt hδ, ne_of_gt hN]
        ring
  refine ⟨hAbsDiffInt, hPoint, ?_⟩
  have hIntegralR : (∫ p, R p.1 ∂Q) = C*m/(r+2 : ℝ)*(2+C) := by
    calc
      _ = ∫ D, R D ∂P := by rw [integral_prod _ hRQ]; simp [R, Mdel]
      _ = C*m/(r+2 : ℝ)*(2+C) := by simpa [R, C, Mdel, P, m] using hEnvelope.2.2
  calc
    (∫ p, |Tfull p-Tdel p| ∂Q) ≤ ∫ p, R p.1 ∂Q :=
      integral_mono hAbsDiffInt hRQ (fun p => hPoint p)
    _ = C*m/(r+2 : ℝ)*(2+C) := hIntegralR

end LOOConcentration.Manuscript.Internal
