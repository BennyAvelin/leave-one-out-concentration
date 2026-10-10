import LOOConcentrationManuscript.Internal.KernelDensityQueryRegularityConsumer
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Under the actual ordered IID law, the KDE's absolute fitted loss has the
single-kernel expectation, independently of sample size, with the source query
Lipschitz constant M/h². All integrability is proved from the kernel bound. -/
theorem genericKDE_actual_expected_loss_and_query_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (K : ℝ → ℝ) (hK : ContDiff ℝ 1 K)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ) (hC : ∀ x, |K x| ≤ C)
    (M : ℝ) (hM : ∀ t : ℝ, |deriv K t| ≤ M) (h : ℝ) (hh : 0 < h) :
    ∀ (r : ℕ) (z : ℝ),
      let P := Measure.pi (fun _ : Fin (r+1) => μ)
      let f := fun (X : Fin (r+1) → ℝ) (t : ℝ) =>
        (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((t-X j)/h)/h
      Integrable (fun X => |f X z|) P ∧
      (∫ X, |f X z| ∂P) = ∫ x : ℝ, K ((z-x)/h)/h ∂μ ∧
      (∀ z' : ℝ, |(∫ X, |f X z| ∂P)-(∫ X, |f X z'| ∂P)| ≤ (M/h^2)*|z-z'|) := by
  intro r z P f
  have hKCont : Continuous K := hK.continuous
  have hAtom (t : ℝ) : Integrable (fun x : ℝ => K ((t-x)/h)/h) μ := by
    apply (integrable_const (C/h)).mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hh]
    exact div_le_div_of_nonneg_right (hC _) hh.le
  have hCoord (t : ℝ) (j : Fin (r+1)) :
      Integrable (fun X : Fin (r+1) → ℝ => K ((t-X j)/h)/h) P ∧
      (∫ X : Fin (r+1) → ℝ, K ((t-X j)/h)/h ∂P) =
        ∫ x : ℝ, K ((t-x)/h)/h ∂μ := by
    have hMP := measurePreserving_eval (fun _ : Fin (r+1) => μ) j
    refine ⟨hMP.integrable_comp_of_integrable (hAtom t),?_⟩
    have hMapMeas : AEStronglyMeasurable (fun x : ℝ => K ((t-x)/h)/h)
        (Measure.map (Function.eval j) P) := by
      rw [hMP.map_eq]
      exact (hAtom t).aestronglyMeasurable
    have hMap := integral_map hMP.measurable.aemeasurable hMapMeas
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hNonneg (X : Fin (r+1) → ℝ) (t : ℝ) : 0 ≤ f X t := by
    dsimp [f]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => div_nonneg (hK_nonneg _) hh.le))
  have hAbsEq (t : ℝ) : (fun X => |f X t|) = (fun X => f X t) := by
    funext X
    exact abs_of_nonneg (hNonneg X t)
  have hFInt (t : ℝ) : Integrable (fun X => f X t) P :=
    (integrable_finsetSum Finset.univ (fun j _ => (hCoord t j).1)).const_mul _
  refine ⟨?_,?_,?_⟩
  · rw [hAbsEq z]
    exact hFInt z
  · rw [hAbsEq z]
    change (∫ X : Fin (r+1) → ℝ, (r+1 : ℝ)⁻¹*∑ j : Fin (r+1), K ((z-X j)/h)/h ∂P) = _
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => (hCoord z j).1)]
    simp only [(hCoord z _).2,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hN : (r+1 : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one]
    rw [← mul_assoc,inv_mul_cancel₀ hN,one_mul]
  · intro z'
    rw [hAbsEq z,hAbsEq z',← integral_sub (hFInt z) (hFInt z')]
    have hDiffInt : Integrable (fun X => f X z-f X z') P := (hFInt z).sub (hFInt z')
    calc
      _ ≤ ∫ X : Fin (r+1) → ℝ, |f X z-f X z'| ∂P := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun X => f X z-f X z')
      _ ≤ ∫ _X : Fin (r+1) → ℝ, (M/h^2)*|z-z'| ∂P :=
        integral_mono hDiffInt.abs
          (integrable_const _) (fun X => genericKDE_actual_query_lipschitz K hK M hM h hh r X z z')
      _ = (M/h^2)*|z-z'| := by
        rw [integral_const]
        simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

end LOOConcentration.Manuscript.Internal
