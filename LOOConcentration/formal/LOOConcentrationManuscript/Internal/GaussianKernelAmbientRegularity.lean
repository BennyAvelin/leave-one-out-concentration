import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory
open scoped ContDiff

/-- The literal stabilized Gaussian predictor is smooth on the whole paired
Euclidean dataset, with every denominator gate derived from source parameters. -/
theorem gaussianKernel_predictor_ambient_contDiff
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    ContDiff ℝ ∞ (fun D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
      (∑ i : Fin (r+1), Kh (x-D (i,Sum.inl 0))*D (i,Sum.inr 0)) /
        ((∑ i : Fin (r+1), Kh (x-D (i,Sum.inl 0)))+(r+1 : ℝ)*δ)) := by
  intro Kh
  obtain ⟨hSmooth,hNonneg,_hBound,_hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hWeight (i : Fin (r+1)) :
      ContDiff ℝ ∞ (fun D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
        Kh (x-D (i,Sum.inl 0))) := by
    have hProj := (PiLp.proj 2 (fun _ : Fin (r+1) × (Fin 1 ⊕ Fin 1) => ℝ)
      (𝕜:=ℝ) (i,Sum.inl 0)).contDiff (n:=∞)
    exact hSmooth.comp ((contDiff_const (c:=x)).sub hProj)
  have hResponse (i : Fin (r+1)) :
      ContDiff ℝ ∞ (fun D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
        D (i,Sum.inr 0)) :=
    (PiLp.proj 2 (fun _ : Fin (r+1) × (Fin 1 ⊕ Fin 1) => ℝ)
      (𝕜:=ℝ) (i,Sum.inr 0)).contDiff (n:=∞)
  have hNum := ContDiff.sum (s:=Finset.univ) (fun i _ => (hWeight i).mul (hResponse i))
  have hDen := (ContDiff.sum (s:=Finset.univ) (fun i _ => hWeight i)).add
    (contDiff_const (c:=(r+1 : ℝ)*δ))
  apply hNum.div hDen
  intro D
  exact ne_of_gt (add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg (fun i _ => hNonneg _)) (mul_pos (by positivity) hδ))

end LOOConcentration.Manuscript.Internal
