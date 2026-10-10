import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelPredictorValueBound
import LOOConcentration.Geometry.NormTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

private theorem norm_toLp_diagonal_le {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (f g : Fin n → ℝ) (hfg : ∀ i, |f i| ≤ c * |g i|) :
    ‖WithLp.toLp 2 f‖ ≤ c * ‖WithLp.toLp 2 g‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  apply (Real.sqrt_le_iff).2
  constructor
  · exact mul_nonneg hc (Real.sqrt_nonneg _)
  · have hsq (i : Fin n) : |f i| ^ 2 ≤ (c * |g i|) ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hc (abs_nonneg _))).2 (hfg i)
    calc
      ∑ i, |f i| ^ 2 ≤ ∑ i, (c * |g i|) ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = c ^ 2 * ∑ i, |g i| ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (c * Real.sqrt (∑ i, |g i| ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (|g i|))]

private theorem norm_toLp_const_le (n : ℕ) (a : ℝ) :
    ‖WithLp.toLp 2 (fun _ : Fin n => a)‖ ≤ Real.sqrt (n : ℝ) * |a| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg n) (|a| ^ 2), Real.sqrt_sq_eq_abs]
  simp only [abs_abs]
  rfl

private theorem norm_toLp_paired_le {n : ℕ} (f g : Fin n → ℝ) :
    ‖WithLp.toLp 2 (fun q : Fin n × (Fin 1 ⊕ Fin 1) =>
      Sum.elim (fun _ : Fin 1 => f q.1) (fun _ : Fin 1 => g q.1) q.2)‖ ≤
      ‖WithLp.toLp 2 f‖ + ‖WithLp.toLp 2 g‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_one,
    Sum.elim_inl, Sum.elim_inr]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hf : 0 ≤ ∑ i : Fin n, |f i| ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hg : 0 ≤ ∑ i : Fin n, |g i| ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc
      ∑ i : Fin n, (|f i| ^ 2 + |g i| ^ 2) =
          (∑ i : Fin n, |f i| ^ 2) + ∑ i : Fin n, |g i| ^ 2 := Finset.sum_add_distrib
      _ ≤ (Real.sqrt (∑ i : Fin n, |f i| ^ 2) +
          Real.sqrt (∑ i : Fin n, |g i| ^ 2)) ^ 2 := by
        rw [add_sq, Real.sq_sqrt hf, Real.sq_sqrt hg]
        nlinarith [mul_nonneg (Real.sqrt_nonneg (∑ i : Fin n, |f i| ^ 2))
          (Real.sqrt_nonneg (∑ i : Fin n, |g i| ^ 2))]

/-- The actual Gaussian source coefficient vector has the explicit finite-
coordinate Euclidean norm bound obtained from the feature and response
coefficients. This is an analytic coefficient estimate; it makes no claim that
the vector is an ambient or Fréchet gradient. -/
theorem gaussianKernel_actualDataset_coefficient_vector_norm_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (x : ℝ) :
    let Kh := fun t : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 (t / h) / h
    let W := (Real.sqrt (2 * Real.pi))⁻¹
    let B := (∑ i : Fin (r + 1), Kh (x - (D i).1 0)) + (r + 1 : ℝ) * δ
    let T := (∑ i : Fin (r + 1), Kh (x - (D i).1 0) * (D i).2 0) / B
    let G : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) :=
      WithLp.toLp 2 (fun q => Sum.elim
        (fun _ : Fin 1 => deriv Kh (x - (D q.1).1 0) / B * (-(D q.1).2 0 + T))
        (fun _ : Fin 1 => Kh (x - (D q.1).1 0) / B) q.2)
    ‖G‖ ≤ ((W / h) / δ) / Real.sqrt (r + 1 : ℝ) +
      ((W / h ^ 2) / δ) * (1 + (W / h) / δ) *
        LOOConcentration.datasetNorm D / (r + 1 : ℝ) := by
  classical
  intro Kh W B T G
  let N : ℝ := (r + 1 : ℝ)
  let Cx : ℝ := (W / h ^ 2) / δ
  let Cy : ℝ := (W / h) / δ
  have hN : 0 < N := by dsimp [N]; positivity
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hCx : 0 ≤ Cx := by
    dsimp [Cx]
    exact div_nonneg (div_nonneg hW (sq_nonneg h)) (le_of_lt hδ)
  have hCy : 0 ≤ Cy := by
    dsimp [Cy]
    exact div_nonneg (div_nonneg hW (le_of_lt hh)) (le_of_lt hδ)
  obtain ⟨_hSmooth, hKhNonneg, hKhBound, _hKhDeriv⟩ :=
    gaussianScaledKernel_value_and_derivative_bounds h hh
  have hLower : N * δ ≤ B := by
    dsimp [B, N]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => hKhNonneg _)
  have hND : 0 < N * δ := mul_pos hN hδ
  have hB : 0 < B := lt_of_lt_of_le hND hLower
  have hFeatureCoeff (i : Fin (r + 1)) :
      |deriv Kh (x - (D i).1 0) / B| ≤ Cx / N := by
    obtain ⟨_hB, _hRatio, hRatio⟩ := gaussianKernel_stabilized_weight_derivative_bound
      h δ hh hδ r (fun j => (D j).1 0) x i
    calc
      _ ≤ (W / h ^ 2) / (N * δ) := by simpa [Kh, W, B, N] using hRatio
      _ = Cx / N := by
        dsimp [Cx]
        field_simp
  have hResponseCoeff (i : Fin (r + 1)) :
      |Kh (x - (D i).1 0) / B| ≤ Cy / N := by
    calc
      _ = |Kh (x - (D i).1 0)| / B := by rw [abs_div, abs_of_pos hB]
      _ ≤ (W / h) / B := div_le_div_of_nonneg_right (hKhBound _) hB.le
      _ ≤ (W / h) / (N * δ) :=
        div_le_div_of_nonneg_left (div_nonneg hW (le_of_lt hh)) hND hLower
      _ = Cy / N := by
        dsimp [Cy]
        field_simp
  have hT : |T| ≤ Cy * LOOConcentration.datasetNorm D / Real.sqrt N := by
    simpa [T, B, Kh, W, Cy, N] using
      gaussianKernel_actualDataset_predictor_value_bound h δ hh hδ r D x
  let Y : Fin (r + 1) → ℝ := fun i => (D i).2 0
  let V : EuclideanSpace ℝ (Fin (r + 1)) := WithLp.toLp 2 Y
  have hYnorm : ‖V‖ ≤ LOOConcentration.datasetNorm D := by
    rw [LOOConcentration.datasetNorm_eq_euclidean, EuclideanSpace.norm_eq,
      EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    change (∑ i : Fin (r + 1), ‖(D i).2 0‖ ^ 2) ≤
      ∑ q : LOOConcentration.DatasetCoordinate 1 1 (r + 1),
        ‖Sum.elim (D q.1).1 (D q.1).2 q.2‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_one]
    exact Finset.sum_le_sum (fun i _ =>
      le_add_of_nonneg_left (sq_nonneg ((D i).1 0)))
  have hConstT :
      ‖WithLp.toLp 2 (fun _ : Fin (r + 1) => T)‖ ≤ Cy * LOOConcentration.datasetNorm D := by
    calc
      _ ≤ Real.sqrt N * |T| := by
        simpa [N] using norm_toLp_const_le (r + 1) T
      _ ≤ Real.sqrt N * (Cy * LOOConcentration.datasetNorm D / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hT (Real.sqrt_nonneg _)
      _ = Cy * LOOConcentration.datasetNorm D := by
        field_simp [ne_of_gt hsqrtN]
  let S : Fin (r + 1) → ℝ := fun i => -Y i + T
  have hShiftEq : WithLp.toLp 2 S = -V + WithLp.toLp 2 (fun _ : Fin (r + 1) => T) := by
    apply PiLp.ext
    intro i
    simp [S, V, Y]
  have hShift : ‖WithLp.toLp 2 S‖ ≤ (1 + Cy) * LOOConcentration.datasetNorm D := by
    calc
      _ = ‖-V + WithLp.toLp 2 (fun _ : Fin (r + 1) => T)‖ := by rw [hShiftEq]
      _ ≤ ‖V‖ + ‖WithLp.toLp 2 (fun _ : Fin (r + 1) => T)‖ := by
        calc
          _ ≤ ‖-V‖ + ‖WithLp.toLp 2 (fun _ : Fin (r + 1) => T)‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      _ ≤ LOOConcentration.datasetNorm D + Cy * LOOConcentration.datasetNorm D :=
        add_le_add hYnorm hConstT
      _ = (1 + Cy) * LOOConcentration.datasetNorm D := by ring
  let F : Fin (r + 1) → ℝ := fun i =>
    (deriv Kh (x - (D i).1 0) / B) * S i
  let R : Fin (r + 1) → ℝ := fun i => Kh (x - (D i).1 0) / B
  have hFbound :
      ‖WithLp.toLp 2 F‖ ≤ Cx * (1 + Cy) * LOOConcentration.datasetNorm D / N := by
    calc
      _ ≤ (Cx / N) * ‖WithLp.toLp 2 S‖ := norm_toLp_diagonal_le (Cx / N)
        (div_nonneg hCx hN.le) F S (fun i => by
          change |(deriv Kh (x - (D i).1 0) / B) * S i| ≤ _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hFeatureCoeff i) (abs_nonneg _))
      _ ≤ (Cx / N) * ((1 + Cy) * LOOConcentration.datasetNorm D) :=
        mul_le_mul_of_nonneg_left hShift (div_nonneg hCx hN.le)
      _ = Cx * (1 + Cy) * LOOConcentration.datasetNorm D / N := by ring
  have hRbound :
      ‖WithLp.toLp 2 R‖ ≤ Cy / Real.sqrt N := by
    calc
      _ ≤ (Cy / N) * ‖WithLp.toLp 2 (fun _ : Fin (r + 1) => (1 : ℝ))‖ :=
        norm_toLp_diagonal_le (Cy / N) (div_nonneg hCy hN.le) R
          (fun _ => 1) (fun i => by
            change |Kh (x - (D i).1 0) / B| ≤ (Cy / N) * |(1 : ℝ)|
            simpa only [abs_one, mul_one] using hResponseCoeff i)
      _ ≤ (Cy / N) * Real.sqrt N := by
        have hc : ‖WithLp.toLp 2 (fun _ : Fin (r + 1) => (1 : ℝ))‖ ≤ Real.sqrt N := by
          simpa [N, abs_one] using norm_toLp_const_le (r + 1) (1 : ℝ)
        exact mul_le_mul_of_nonneg_left hc (div_nonneg hCy hN.le)
      _ = Cy / Real.sqrt N := by
        have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
        calc
          (Cy / N) * Real.sqrt N = Cy * Real.sqrt N / N := by ring
          _ = Cy / Real.sqrt N := by
            rw [← hsquare]
            field_simp [ne_of_gt hsqrtN]
            rw [Real.sqrt_sq (le_of_lt hsqrtN)]
  change ‖WithLp.toLp 2 (fun q : Fin (r + 1) × (Fin 1 ⊕ Fin 1) =>
    Sum.elim (fun _ : Fin 1 => F q.1) (fun _ : Fin 1 => R q.1) q.2)‖ ≤ _
  calc
    _ ≤ ‖WithLp.toLp 2 F‖ + ‖WithLp.toLp 2 R‖ := norm_toLp_paired_le F R
    _ ≤ Cx * (1 + Cy) * LOOConcentration.datasetNorm D / N + Cy / Real.sqrt N :=
      add_le_add hFbound hRbound
    _ = Cy / Real.sqrt N + Cx * (1 + Cy) * LOOConcentration.datasetNorm D / N := by ring

end LOOConcentration.Manuscript.Internal
