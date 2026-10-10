import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentration.Geometry.NormTransport
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- Conditional finite-weight calculation; the actual Gaussian consumer supplies
all weight hypotheses from positive source parameters. -/
private theorem boundedWeight_stabilizedPredictor_value_bound
    (r : ℕ) (w Y : Fin (r+1) → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) (δ : ℝ) (hδ : 0 < δ) :
    |(∑ i : Fin (r+1), w i*Y i)/((∑ i : Fin (r+1), w i)+(r+1 : ℝ)*δ)| ≤
      (W/δ)*‖WithLp.toLp 2 Y‖/Real.sqrt (r+1 : ℝ) := by
  classical
  let B := (∑ i : Fin (r+1), w i)+(r+1 : ℝ)*δ
  have hN : 0 < (r+1 : ℝ) := by positivity
  have hLower : (r+1 : ℝ)*δ ≤ B := le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => hw i))
  have hDen : 0 < (r+1 : ℝ)*δ := mul_pos hN hδ
  have hB : 0 < B := lt_of_lt_of_le hDen hLower
  have hAbs : |∑ i : Fin (r+1), w i*Y i| ≤ W*∑ i : Fin (r+1), |Y i| := by
    calc
      _ ≤ ∑ i : Fin (r+1), |w i*Y i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin (r+1), w i*|Y i| := by simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ i : Fin (r+1), W*|Y i| :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hwW i) (abs_nonneg _))
      _ = _ := by rw [Finset.mul_sum]
  have hSum : (∑ i : Fin (r+1), |Y i|) ≤
      Real.sqrt (r+1 : ℝ)*‖WithLp.toLp 2 Y‖ := by
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _i : Fin (r+1) => (1 : ℝ))
      (fun i => |Y i|)
    simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hc
  have hSqrt : 0 < Real.sqrt (r+1 : ℝ) := Real.sqrt_pos.2 hN
  change |(∑ i : Fin (r+1), w i*Y i)/B| ≤ _
  rw [abs_div, abs_of_pos hB]
  calc
    _ ≤ (W*∑ i : Fin (r+1), |Y i|)/B := div_le_div_of_nonneg_right hAbs hB.le
    _ ≤ (W*∑ i : Fin (r+1), |Y i|)/((r+1 : ℝ)*δ) :=
      div_le_div_of_nonneg_left (mul_nonneg hW (Finset.sum_nonneg fun i _ => abs_nonneg _)) hDen hLower
    _ ≤ (W*(Real.sqrt (r+1 : ℝ)*‖WithLp.toLp 2 Y‖))/((r+1 : ℝ)*δ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSum hW) hDen.le
    _ = _ := by
      have hn : (r+1 : ℝ) = (Real.sqrt (r+1 : ℝ))^2 := (Real.sq_sqrt hN.le).symm
      conv_lhs => rhs; lhs; rw [hn]
      field_simp

/-- The source Gaussian predictor has the explicit O(norm responses/sqrt N)
value bound, uniformly in all raw feature coordinates and test queries. -/
theorem gaussianKernel_predictor_value_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (X Y : Fin (r+1) → ℝ) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹
    |(∑ i : Fin (r+1), Kh (x-X i)*Y i)/
      ((∑ i : Fin (r+1), Kh (x-X i))+(r+1 : ℝ)*δ)| ≤
        ((W/h)/δ)*‖WithLp.toLp 2 Y‖/Real.sqrt (r+1 : ℝ) := by
  intro Kh W
  obtain ⟨_hSmooth,hNonneg,hBound,_hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  exact boundedWeight_stabilizedPredictor_value_bound r (fun i => Kh (x-X i)) Y (W/h)
    (by dsimp [W]; positivity) (fun i => hNonneg _) (fun i => (le_abs_self _).trans (hBound _)) δ hδ

/-- The same value estimate on the actual paired dataset uses its exact frozen
Euclidean norm, without changing constants or discarding sample dimensions. -/
theorem gaussianKernel_actualDataset_predictor_value_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹
    |(∑ i : Fin (r+1), Kh (x-(D i).1 0)*(D i).2 0)/
      ((∑ i : Fin (r+1), Kh (x-(D i).1 0))+(r+1 : ℝ)*δ)| ≤
        ((W/h)/δ)*LOOConcentration.datasetNorm D/Real.sqrt (r+1 : ℝ) := by
  intro Kh W
  have hYnorm : ‖WithLp.toLp 2 (fun i : Fin (r+1) => (D i).2 0)‖ ≤ LOOConcentration.datasetNorm D := by
    rw [LOOConcentration.datasetNorm_eq_euclidean, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    change (∑ i : Fin (r+1), ‖(D i).2 0‖^2) ≤
      ∑ q : LOOConcentration.DatasetCoordinate 1 1 (r+1),
        ‖Sum.elim (D q.1).1 (D q.1).2 q.2‖^2
    simp only [Real.norm_eq_abs, sq_abs]
    simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_one]
    exact Finset.sum_le_sum (fun i _ => le_add_of_nonneg_left (sq_nonneg ((D i).1 0)))
  have hs := gaussianKernel_predictor_value_bound h δ hh hδ r
    (fun i => (D i).1 0) (fun i => (D i).2 0) x
  exact hs.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYnorm
    (by positivity)) (Real.sqrt_nonneg _))

end LOOConcentration.Manuscript.Internal
