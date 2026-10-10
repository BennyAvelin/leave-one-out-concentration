import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

private theorem kernel_shift_integrable (K : ℝ → ℝ) (h x : ℝ)
    (hh : 0 < h) (hK : Integrable K) :
    Integrable (fun z : ℝ => K ((z - x) / h)) := by
  have hscale : Integrable (fun z : ℝ => K (z / h)) := hK.comp_div hh.ne'
  simpa [sub_eq_add_neg, add_comm] using hscale.comp_add_left (-x)

private theorem kernel_shift_integral (K : ℝ → ℝ) (h x : ℝ)
    (hh : 0 < h) :
    (∫ z : ℝ, K ((z - x) / h)) = h * (∫ z : ℝ, K z) := by
  have hshift : (∫ z : ℝ, K ((z - x) / h)) = ∫ z : ℝ, K (z / h) := by
    simpa [sub_eq_add_neg, add_comm] using
      (integral_add_left_eq_self (μ := volume) (fun z : ℝ => K (z / h)) (-x))
  rw [hshift, Measure.integral_comp_div]
  simp [abs_of_pos hh, smul_eq_mul]

private theorem kernel_shift_scaled_integral (K : ℝ → ℝ) (h x : ℝ)
    (hh : 0 < h) (hK : ∫ z : ℝ, K z = 1) :
    (∫ z : ℝ, K ((z - x) / h) / h) = 1 := by
  rw [integral_div h, kernel_shift_integral K h x hh, hK]
  simp [hh.ne']

/-- A nonnegative bounded normalized kernel gives an integrable, normalized,
square-integrable literal KDE for every finite sample and every positive
bandwidth. Integrability of the kernel is derived from its nonzero integral. -/
theorem genericKernelDensityEstimator_facts
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (r : ℕ) (X : Fin (r + 1) → ℝ) :
    let f := (fun z : ℝ => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)
    Integrable f ∧ (∀ z, 0 ≤ f z) ∧ (∫ z : ℝ, f z = 1) ∧ MemLp f 2 volume := by
  dsimp only
  let f : ℝ → ℝ := (fun z : ℝ => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)
  have hKint : Integrable K := integrable_of_integral_eq_one hK_integral
  have hC : 0 ≤ C := (abs_nonneg (K 0)).trans (hK_bound 0)
  have hCscale : 0 ≤ C / h := div_nonneg hC hh.le
  have hAtomInt (j : Fin (r + 1)) :
      Integrable (fun z : ℝ => K ((z - X j) / h) / h) :=
    (kernel_shift_integrable K h (X j) hh hKint).div_const h
  have hAtomsInt :
      Integrable (fun z : ℝ => ∑ j : Fin (r + 1), K ((z - X j) / h) / h) := by
    exact integrable_finsetSum Finset.univ (by
      intro j hj
      exact hAtomInt j)
  have hfInt : Integrable f := by
    dsimp [f]
    exact hAtomsInt.const_mul ((r + 1 : ℝ)⁻¹)
  have hfNonneg : ∀ z, 0 ≤ f z := by
    intro z
    dsimp [f]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hK_nonneg _) hh.le
  have hTermBound (z : ℝ) (j : Fin (r + 1)) :
      K ((z - X j) / h) / h ≤ C / h := by
    apply div_le_div_of_nonneg_right
    · exact (le_abs_self _).trans (hK_bound _)
    · exact hh.le
  have hSumBound (z : ℝ) :
      (∑ j : Fin (r + 1), K ((z - X j) / h) / h) ≤
        (r + 1 : ℝ) * (C / h) := by
    calc
      _ ≤ ∑ _j : Fin (r + 1), C / h :=
        Finset.sum_le_sum (fun j _ => hTermBound z j)
      _ = (r + 1 : ℝ) * (C / h) := by simp
  have hfBound (z : ℝ) : f z ≤ C / h := by
    dsimp [f]
    calc
      _ ≤ (r + 1 : ℝ)⁻¹ * ((r + 1 : ℝ) * (C / h)) :=
        mul_le_mul_of_nonneg_left (hSumBound z) (by positivity)
      _ = C / h := by
        have hr : (r + 1 : ℝ) ≠ 0 := by positivity
        calc
          _ = ((r + 1 : ℝ)⁻¹ * (r + 1 : ℝ)) * (C / h) := by ring
          _ = C / h := by rw [inv_mul_cancel₀ hr, one_mul]
  have hfBoundAbs (z : ℝ) : |f z| ≤ |C / h| := by
    rw [abs_of_nonneg (hfNonneg z), abs_of_nonneg hCscale]
    exact hfBound z
  have hIntegral : (∫ z : ℝ, f z) = 1 := by
    dsimp [f]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (by
      intro j hj
      exact hAtomInt j)]
    simp only [kernel_shift_scaled_integral K h _ hh hK_integral]
    simp
    have hr : (r + 1 : ℝ) ≠ 0 := by positivity
    exact inv_mul_cancel₀ hr
  have hfSq : Integrable (fun z : ℝ => f z ^ 2) := by
    have hmul := hfInt.bdd_mul hfInt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact hfBoundAbs z)
    simpa only [pow_two] using hmul
  have hfMem : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hfInt.aestronglyMeasurable).2 hfSq
  exact ⟨hfInt, hfNonneg, hIntegral, hfMem⟩

/-- For an `L²` target, the literal KDE loss is integrable and has the finite
integrated expansion into its target square, cross term, and estimator square. -/
theorem genericKernelDensityEstimator_finite_integrated_loss_expansion
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (r : ℕ) (X : Fin (r + 1) → ℝ) (g : ℝ → ℝ) (hg : MemLp g 2 volume) :
    Integrable (fun z : ℝ =>
      (g z - ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) ∧
    (∫ z : ℝ,
        (g z - ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) =
      (∫ z : ℝ, g z ^ 2) -
        2 * (∫ z : ℝ, g z * ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) +
        (∫ z : ℝ, (((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)) ^ 2) := by
  let f := (fun z : ℝ => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((z - X j) / h) / h)
  obtain ⟨_hfInt, _hfNonneg, _hfIntegral, hf⟩ :=
    genericKernelDensityEstimator_facts K h hh hK_nonneg C hK_bound hK_integral r X
  have hdiff : MemLp (fun z : ℝ => g z - f z) 2 volume := hg.sub hf
  have hgSq : Integrable (fun z : ℝ => g z ^ 2) := hg.integrable_sq
  have hfSq : Integrable (fun z : ℝ => f z ^ 2) := hf.integrable_sq
  have hcross : Integrable (fun z : ℝ => g z * f z) := hg.integrable_mul hf
  have hcross2 : Integrable (fun z : ℝ => 2 * (g z * f z)) := hcross.const_mul 2
  have hleft : Integrable (fun z : ℝ => g z ^ 2 - 2 * (g z * f z)) := hgSq.sub hcross2
  have hLoss : Integrable (fun z : ℝ => (g z - f z) ^ 2) := hdiff.integrable_sq
  have hAlgebra :
      (fun z : ℝ => (g z - f z) ^ 2) =
        fun z => g z ^ 2 - 2 * (g z * f z) + f z ^ 2 := by
    funext z
    ring
  constructor
  · simpa only [f] using hLoss
  · calc
      (∫ z : ℝ, (g z - f z) ^ 2) =
          ∫ z : ℝ, g z ^ 2 - 2 * (g z * f z) + f z ^ 2 := by rw [hAlgebra]
      _ = (∫ z : ℝ, g z ^ 2 - 2 * (g z * f z)) +
          (∫ z : ℝ, f z ^ 2) := integral_add hleft hfSq
      _ = (∫ z : ℝ, g z ^ 2) - 2 * (∫ z : ℝ, g z * f z) +
          (∫ z : ℝ, f z ^ 2) := by
        rw [integral_sub hgSq hcross2, integral_const_mul]

end LOOConcentration.Manuscript.Internal
