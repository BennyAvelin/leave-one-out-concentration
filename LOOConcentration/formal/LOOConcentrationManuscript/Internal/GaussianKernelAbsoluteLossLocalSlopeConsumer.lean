import LOOConcentrationManuscript.Internal.GaussianKernelAbsoluteLossLocalSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

/-- A downstream consumer can use one source constant simultaneously at two
sample sizes, with the same literal absolute fitted loss on every data point. -/
theorem gaussianKernel_absoluteLoss_localSlope_twoSizes
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) (x y : ℝ),
      ∃ fr : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
      ∃ fs : LOOConcentration.LocallyLipschitzDataFunction 0 0 s,
        (∀ D : LOOConcentration.DataCarrier 0 0 r,
          fr.1 D = abs
            ((∑ i : Fin (r + 1),
                (ProbabilityTheory.gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) * (D i).2 0) /
              ((∑ i : Fin (r + 1),
                ProbabilityTheory.gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) +
                (r + 1 : ℝ) * δ) - y)) ∧
        (∀ D : LOOConcentration.DataCarrier 0 0 r,
          LOOConcentration.datasetLocalSlope fr D ≤
            C / Real.sqrt (r + 1 : ℝ) +
              C * LOOConcentration.datasetNorm D / (r + 1 : ℝ)) ∧
        (∀ D : LOOConcentration.DataCarrier 0 0 s,
          fs.1 D = abs
            ((∑ i : Fin (s + 1),
                (ProbabilityTheory.gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) * (D i).2 0) /
              ((∑ i : Fin (s + 1),
                ProbabilityTheory.gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) +
                (s + 1 : ℝ) * δ) - y)) ∧
        (∀ D : LOOConcentration.DataCarrier 0 0 s,
          LOOConcentration.datasetLocalSlope fs D ≤
            C / Real.sqrt (s + 1 : ℝ) +
              C * LOOConcentration.datasetNorm D / (s + 1 : ℝ)) := by
  obtain ⟨C, hC, hBound⟩ :=
    gaussianKernel_actual_absoluteLoss_localSlope_bound h δ hh hδ
  refine ⟨C, hC, ?_⟩
  intro r s x y
  obtain ⟨fr, hfrValue, hfrSlope⟩ := hBound r x y
  obtain ⟨fs, hfsValue, hfsSlope⟩ := hBound s x y
  exact ⟨fr, fs, hfrValue, hfrSlope, hfsValue, hfsSlope⟩

end LOOConcentration.Manuscript.Internal
