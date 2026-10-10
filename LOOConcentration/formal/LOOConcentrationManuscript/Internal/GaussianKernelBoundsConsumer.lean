import LOOConcentrationManuscript.Internal.GaussianKernelBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory
open scoped ContDiff

/-- The source bandwidth convention gives an everywhere smooth Gaussian kernel
with explicit uniform value and derivative bounds at every positive bandwidth. -/
theorem gaussianScaledKernel_value_and_derivative_bounds (h : ℝ) (hh : 0 < h) :
    let K := gaussianPDFReal 0 1
    let W := (Real.sqrt (2 * Real.pi))⁻¹
    let Kh := fun x : ℝ => K (x / h) / h
    ContDiff ℝ ∞ Kh ∧ (∀ x, 0 ≤ Kh x) ∧ (∀ x, |Kh x| ≤ W / h) ∧
      (∀ x, HasDerivAt Kh (-(x) / h ^ 2 * Kh x) x ∧ |deriv Kh x| ≤ W / h ^ 2) := by
  intro K W Kh
  obtain ⟨hSmooth, hNonneg, _hInt, _hNorm, _hL2, hBound, hDeriv⟩ :=
    gaussianKernel_normalization_and_bounds
  have hRaw (x : ℝ) : HasDerivAt Kh
      ((-(x / h) * K (x / h)) * h⁻¹ / h) x := by
    have hInner : HasDerivAt (fun t : ℝ => t / h) h⁻¹ x := by
      simpa only [one_div] using (hasDerivAt_id' (𝕜 := ℝ) x).div_const h
    simpa only [Function.comp_def] using ((hDeriv (x / h)).1.comp x hInner).div_const h
  have hCoeff (x : ℝ) : ((-(x / h) * K (x / h)) * h⁻¹ / h) =
      -(x) / h ^ 2 * Kh x := by
    dsimp [Kh]
    field_simp
  refine ⟨?_, (fun x => div_nonneg (hNonneg (x / h)) hh.le), ?_, ?_⟩
  · exact (hSmooth.comp (contDiff_id.div_const h)).div_const h
  · intro x
    simpa only [Kh, abs_div, abs_of_pos hh] using
      (div_le_div_of_nonneg_right (hBound (x / h)) hh.le)
  · intro x
    refine ⟨?_, ?_⟩
    · simpa only [hCoeff x] using hRaw x
    · rw [(hRaw x).deriv, abs_div, abs_mul, abs_inv, abs_of_pos hh]
      have hBase : |-(x / h) * K (x / h)| ≤ W := by
        simpa only [((hDeriv (x / h)).1).deriv] using (hDeriv (x / h)).2
      calc
        _ ≤ (W * h⁻¹) / h :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBase (inv_nonneg.mpr hh.le)) hh.le
        _ = W / h ^ 2 := by ring

/-- The actual Gaussian weight derivative over the stabilized finite-sample
kernel denominator, with its source O(1/N) constant made explicit. -/
theorem gaussianKernel_stabilized_weight_derivative_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (X : Fin (r + 1) → ℝ) (x : ℝ) (j : Fin (r + 1)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t / h) / h
    let W := (Real.sqrt (2 * Real.pi))⁻¹
    let B := (∑ i : Fin (r + 1), Kh (x - X i)) + (r + 1 : ℝ) * δ
    0 < B ∧
      |deriv Kh (x - X j) / B| =
        (|x - X j| / h ^ 2) * (Kh (x - X j) / B) ∧
      |deriv Kh (x - X j) / B| ≤ (W / h ^ 2) / ((r + 1 : ℝ) * δ) := by
  intro Kh W B
  obtain ⟨_hSmooth, hNonneg, _hVal, hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hLower : (r + 1 : ℝ) * δ ≤ B :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => hNonneg (x - X i))
  have hN : 0 < (r + 1 : ℝ) * δ := mul_pos (by positivity) hδ
  have hB : 0 < B := lt_of_lt_of_le hN hLower
  refine ⟨hB, ?_, ?_⟩
  · rw [((hDeriv (x - X j)).1).deriv, abs_div, abs_mul, abs_div,
      abs_neg, abs_of_nonneg (sq_nonneg h), abs_of_nonneg (hNonneg (x - X j)), abs_of_pos hB]
    ring
  · rw [abs_div, abs_of_pos hB]
    calc
      _ ≤ (W / h ^ 2) / B := div_le_div_of_nonneg_right (hDeriv (x - X j)).2 hB.le
      _ ≤ (W / h ^ 2) / ((r + 1 : ℝ) * δ) :=
        div_le_div_of_nonneg_left (div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (sq_nonneg h)) hN hLower

end LOOConcentration.Manuscript.Internal
