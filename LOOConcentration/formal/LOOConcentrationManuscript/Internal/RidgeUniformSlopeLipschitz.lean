import LOOConcentrationManuscript.Internal.RidgePredictorQueryFeature
import LOOConcentrationManuscript.Internal.RidgePredictorTrainingRegularity
import LOOConcentrationManuscript.Internal.RidgeSlopeBound
import LOOConcentrationManuscript.Internal.EuclideanClipping
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedLinearEstimator
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The public stabilized scalar Ridge beta, viewed as the actual public
training predictor at query 1 minus its value at query 0. The copied private
finite-difference proof is mapped to the accepted predictor source in
`evidence/ridge-private-source-blocks.json`.
-/

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped RealInnerProductSpace

private noncomputable abbrev ridgeTrainMean {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ i, X i) / (N : ℝ)

private noncomputable abbrev ridgeTrainCentered {N : ℕ} (X : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => X i - ridgeTrainMean X)

private noncomputable abbrev ridgeTrainNormalizedCenter {N : ℕ} (X : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  (Real.sqrt (N : ℝ))⁻¹ • ridgeTrainCentered X

private noncomputable abbrev ridgeTrainVariance {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - ridgeTrainMean X) ^ 2) / (N : ℝ)

private noncomputable abbrev ridgeTrainCovariance {N : ℕ}
    (X U : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - ridgeTrainMean X) * (U i - ridgeTrainMean U)) / (N : ℝ)

private theorem ridgeTrain_centered_sum_zero {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) :
    ∑ i, (X i - ridgeTrainMean X) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hconst : ∑ _i : Fin N, ridgeTrainMean X = (N : ℝ) * ridgeTrainMean X := by simp
  rw [hconst, ridgeTrainMean]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN0]
  ring

private theorem ridgeTrain_variance_nonneg {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) : 0 ≤ ridgeTrainVariance X := by
  unfold ridgeTrainVariance
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (X i - ridgeTrainMean X))
    (by exact_mod_cast hN.le)

private theorem ridgeTrain_centered_norm_sq {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) :
    ‖ridgeTrainCentered X‖ ^ 2 =
      (∑ i, X i ^ 2) - (N : ℝ) * (ridgeTrainMean X) ^ 2 := by
  have hmean : ∑ i, X i = (N : ℝ) * ridgeTrainMean X := by
    dsimp [ridgeTrainMean]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp [hN0]
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (X i - ridgeTrainMean X) ^ 2) = _
  calc
    _ = ∑ i, (X i ^ 2 - 2 * X i * ridgeTrainMean X + (ridgeTrainMean X) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, X i ^ 2) - 2 * ridgeTrainMean X * (∑ i, X i) +
        (N : ℝ) * (ridgeTrainMean X) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hfactor : (∑ i : Fin N, 2 * X i * ridgeTrainMean X) =
          2 * ridgeTrainMean X * (∑ i, X i) := by
        calc
          _ = ∑ i : Fin N, (2 * ridgeTrainMean X) * X i := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [Finset.mul_sum]
      rw [hfactor]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by rw [hmean]; ring

private theorem ridgeTrain_centered_contract {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) : ‖ridgeTrainCentered X‖ ≤ ‖WithLp.toLp 2 X‖ := by
  have hsquares : ‖ridgeTrainCentered X‖ ^ 2 ≤ ‖WithLp.toLp 2 X‖ ^ 2 := by
    rw [ridgeTrain_centered_norm_sq hN X, EuclideanSpace.real_norm_sq_eq]
    exact sub_le_self _ (mul_nonneg (by exact_mod_cast hN.le) (sq_nonneg _))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquares

private theorem ridgeTrain_centered_sub {N : ℕ} (_hN : 0 < N)
    (X Y : Fin N → ℝ) :
    ridgeTrainCentered X - ridgeTrainCentered Y =
      ridgeTrainCentered (fun i => X i - Y i) := by
  apply PiLp.ext
  intro i
  change (X i - ridgeTrainMean X) - (Y i - ridgeTrainMean Y) =
    (X i - Y i) - ridgeTrainMean (fun i => X i - Y i)
  simp only [ridgeTrainMean]
  rw [Finset.sum_sub_distrib]
  ring

private theorem ridgeTrain_normalized_center_norm_sq {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) :
    ‖ridgeTrainNormalizedCenter X‖ ^ 2 = ridgeTrainVariance X := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [ridgeTrainNormalizedCenter, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hNr)), mul_pow, inv_pow,
    Real.sq_sqrt hNr.le, ridgeTrainVariance]
  rw [ridgeTrainCentered, EuclideanSpace.real_norm_sq_eq]
  rw [div_eq_mul_inv]
  ring

private theorem ridgeTrain_normalized_center_contract {N : ℕ} (hN : 0 < N)
    (X Y : Fin N → ℝ) :
    ‖ridgeTrainNormalizedCenter X - ridgeTrainNormalizedCenter Y‖ ≤
      ‖WithLp.toLp 2 (fun i => X i - Y i)‖ / Real.sqrt (N : ℝ) := by
  rw [ridgeTrainNormalizedCenter, ridgeTrainNormalizedCenter, ← smul_sub,
    ridgeTrain_centered_sub hN]
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsqrt)]
  calc
    (Real.sqrt (N : ℝ))⁻¹ * ‖ridgeTrainCentered (fun i => X i - Y i)‖ ≤
        (Real.sqrt (N : ℝ))⁻¹ * ‖WithLp.toLp 2 (fun i => X i - Y i)‖ :=
      mul_le_mul_of_nonneg_left (ridgeTrain_centered_contract hN _) (inv_nonneg.mpr hsqrt.le)
    _ = ‖WithLp.toLp 2 (fun i => X i - Y i)‖ / Real.sqrt (N : ℝ) := by ring

private theorem ridgeTrain_normalized_inner_eq_covariance {N : ℕ} (hN : 0 < N)
    (X U : Fin N → ℝ) :
    ⟪ridgeTrainNormalizedCenter X, ridgeTrainNormalizedCenter U⟫ =
      ridgeTrainCovariance X U := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [ridgeTrainNormalizedCenter, ridgeTrainNormalizedCenter]
  simp only [inner_smul_left, inner_smul_right]
  calc
    (Real.sqrt (N : ℝ))⁻¹ *
        ((Real.sqrt (N : ℝ))⁻¹ *
          ⟪ridgeTrainCentered X, ridgeTrainCentered U⟫) =
      ((Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹) *
        ⟪ridgeTrainCentered X, ridgeTrainCentered U⟫ := by ring
    _ = (N : ℝ)⁻¹ * ⟪ridgeTrainCentered X, ridgeTrainCentered U⟫ := by
      have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
      field_simp [hsqrt.ne', hNr.ne']
      rw [Real.sq_sqrt hNr.le]
      exact mul_comm (⟪ridgeTrainCentered X, ridgeTrainCentered U⟫) (N : ℝ)
    _ = ridgeTrainCovariance X U := by
      rw [ridgeTrainCovariance]
      unfold ridgeTrainCentered
      simp only [PiLp.inner_apply, Real.inner_apply]
      rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem ridgeTrain_raw_energy_le_paired_norm_sq (r : ℕ)
    (E F : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    (∑ j : Fin (r + 1), (E (j, Sum.inl 0) - F (j, Sum.inl 0)) ^ 2) +
      (∑ j : Fin (r + 1), (E (j, Sum.inr 0) - F (j, Sum.inr 0)) ^ 2) ≤
        ‖E - F‖ ^ 2 := by
  let v : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) := E - F
  rw [EuclideanSpace.real_norm_sq_eq]
  dsimp [v]
  have hsum :
      (∑ j : Fin (r + 1), (v (j, Sum.inl 0)) ^ 2) +
          (∑ j : Fin (r + 1), (v (j, Sum.inr 0)) ^ 2) =
        ∑ p : Fin (r + 1) × (Fin 1 ⊕ Fin 1), v p ^ 2 := by
    calc
      _ = ∑ j : Fin (r + 1),
          ((v (j, Sum.inl 0)) ^ 2 + (v (j, Sum.inr 0)) ^ 2) := by rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin (r + 1), ∑ s : Fin 1 ⊕ Fin 1, v (j, s) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Fintype.sum_sum_type]
        simp
      _ = ∑ p : Fin (r + 1) × (Fin 1 ⊕ Fin 1), v p ^ 2 := by
        rw [Fintype.sum_prod_type]
  have hsum' :
      (∑ j : Fin (r + 1), (E (j, Sum.inl 0) - F (j, Sum.inl 0)) ^ 2) +
        (∑ j : Fin (r + 1), (E (j, Sum.inr 0) - F (j, Sum.inr 0)) ^ 2) =
      ∑ p : Fin (r + 1) × (Fin 1 ⊕ Fin 1), (E p - F p) ^ 2 := by
    simpa [v] using hsum
  rw [hsum']

private theorem ridgeTrain_coordinate_norm_le (r : ℕ)
    (E F : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (which : Sum (Fin 1) (Fin 1)) :
    ‖WithLp.toLp 2 (fun j : Fin (r + 1) => E (j, which) - F (j, which))‖ ≤ ‖E - F‖ := by
  have hpart :
      (∑ j : Fin (r + 1), (E (j, which) - F (j, which)) ^ 2) ≤ ‖E - F‖ ^ 2 := by
    have h := ridgeTrain_raw_energy_le_paired_norm_sq r E F
    cases which with
    | inl i =>
        cases i using Fin.cases with
        | zero =>
            have hother : 0 ≤ ∑ j : Fin (r + 1),
                (E (j, Sum.inr 0) - F (j, Sum.inr 0)) ^ 2 :=
              Finset.sum_nonneg fun j _ => sq_nonneg _
            exact (le_add_of_nonneg_right hother).trans h
        | succ i => exact Fin.elim0 i
    | inr i =>
        cases i using Fin.cases with
        | zero =>
            have hother : 0 ≤ ∑ j : Fin (r + 1),
                (E (j, Sum.inl 0) - F (j, Sum.inl 0)) ^ 2 :=
              Finset.sum_nonneg fun j _ => sq_nonneg _
            exact (le_add_of_nonneg_left hother).trans h
        | succ i => exact Fin.elim0 i
  have hsquares :
      ‖WithLp.toLp 2 (fun j : Fin (r + 1) => E (j, which) - F (j, which))‖ ^ 2 ≤
        ‖E - F‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa only [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp] using hpart
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquares

private theorem ridgeTrain_mean_norm_bound {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) :
    |ridgeTrainMean X| ≤ ‖WithLp.toLp 2 X‖ / Real.sqrt (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ X (fun _ : Fin N => (1 : ℝ))
  have hcs' : (∑ i : Fin N, X i) ^ 2 ≤
      ‖WithLp.toLp 2 X‖ ^ 2 * (N : ℝ) := by
    simpa [EuclideanSpace.real_norm_sq_eq] using hcs
  have hsum : |∑ i : Fin N, X i| ≤ ‖WithLp.toLp 2 X‖ * Real.sqrt (N : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).1
    calc
      |∑ i : Fin N, X i| ^ 2 = (∑ i : Fin N, X i) ^ 2 := sq_abs _
      _ ≤ ‖WithLp.toLp 2 X‖ ^ 2 * (N : ℝ) := hcs'
      _ = (‖WithLp.toLp 2 X‖ * Real.sqrt (N : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNr.le]
  rw [ridgeTrainMean, abs_div, abs_of_pos hNr]
  apply (div_le_div_iff₀ hNr (Real.sqrt_pos.2 hNr)).2
  calc
    |∑ i : Fin N, X i| * Real.sqrt (N : ℝ) ≤
        (‖WithLp.toLp 2 X‖ * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) :=
      mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _)
    _ = ‖WithLp.toLp 2 X‖ * (N : ℝ) := by
      calc
        _ = ‖WithLp.toLp 2 X‖ * (Real.sqrt (N : ℝ)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hNr.le]

private theorem ridgeTrain_mean_difference_bound {N : ℕ} (hN : 0 < N)
    (X Y : Fin N → ℝ) :
    |ridgeTrainMean X - ridgeTrainMean Y| ≤
      ‖WithLp.toLp 2 (fun i => X i - Y i)‖ / Real.sqrt (N : ℝ) := by
  have heq : ridgeTrainMean X - ridgeTrainMean Y =
      ridgeTrainMean (fun i => X i - Y i) := by
    simp only [ridgeTrainMean, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact ridgeTrain_mean_norm_bound hN _

private noncomputable abbrev ridgeTrainFeature {r : ℕ}
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : Fin (r + 1) → ℝ :=
  fun j => E (j, Sum.inl 0)

private noncomputable abbrev ridgeTrainResponse {r : ℕ}
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : Fin (r + 1) → ℝ :=
  fun j => E (j, Sum.inr 0)

private noncomputable abbrev ridgeTrainClippedResponse {r : ℕ}
    (b : ℝ) (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    Fin (r + 1) → ℝ :=
  fun j => max (min (ridgeTrainResponse E j) b) (-b)

private noncomputable abbrev ridgeTrainSlope {r : ℕ} (b δ : ℝ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : ℝ :=
  ridgeTrainCovariance (ridgeTrainFeature E) (ridgeTrainClippedResponse b E) /
    (ridgeTrainVariance (ridgeTrainFeature E) + δ)

private theorem ridge_hilbert_rational_factor (p q δ : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hδ : 0 < δ) :
    q * (p + q) / ((p ^ 2 + δ) * (q ^ 2 + δ)) ≤ 2 / δ := by
  have hps : 0 < p ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hqs : 0 < q ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hpBound : p / (p ^ 2 + δ) ≤ 1 / (2 * Real.sqrt δ) := by
    apply (div_le_div_iff₀ hps (by positivity : 0 < 2 * Real.sqrt δ)).2
    nlinarith [sq_nonneg (p - Real.sqrt δ), Real.sq_sqrt hδ.le]
  have hqBound : q / (q ^ 2 + δ) ≤ 1 / (2 * Real.sqrt δ) := by
    apply (div_le_div_iff₀ hqs (by positivity : 0 < 2 * Real.sqrt δ)).2
    nlinarith [sq_nonneg (q - Real.sqrt δ), Real.sq_sqrt hδ.le]
  have hpInv : 1 / (p ^ 2 + δ) ≤ 1 / δ := by
    apply (div_le_div_iff₀ hps hδ).2
    nlinarith [sq_nonneg p]
  have hqSq : q ^ 2 / (q ^ 2 + δ) ≤ 1 := by
    apply (div_le_iff₀ hqs).2
    nlinarith [sq_nonneg q]
  have hA : 0 ≤ p / (p ^ 2 + δ) := div_nonneg hp hps.le
  have hB : 0 ≤ q / (q ^ 2 + δ) := div_nonneg hq hqs.le
  have hC : 0 ≤ 1 / (p ^ 2 + δ) := by positivity
  have hD : 0 ≤ q ^ 2 / (q ^ 2 + δ) := by positivity
  have hsplit :
      q * (p + q) / ((p ^ 2 + δ) * (q ^ 2 + δ)) =
        (p / (p ^ 2 + δ)) * (q / (q ^ 2 + δ)) +
        (1 / (p ^ 2 + δ)) * (q ^ 2 / (q ^ 2 + δ)) := by
    field_simp [hps.ne', hqs.ne']
  rw [hsplit]
  calc
    _ ≤ (1 / (2 * Real.sqrt δ)) * (1 / (2 * Real.sqrt δ)) + (1 / δ) * 1 :=
      add_le_add (mul_le_mul hpBound hqBound hB (by positivity))
        (mul_le_mul hpInv hqSq hD (by positivity))
    _ ≤ 2 / δ := by
      have hsq : (2 * Real.sqrt δ) ^ 2 = 4 * δ := by
        rw [mul_pow, Real.sq_sqrt hδ.le]
        ring
      have hprod : (1 / (2 * Real.sqrt δ)) * (1 / (2 * Real.sqrt δ)) = 1 / (4 * δ) := by
        field_simp [hs.ne']
        rw [Real.sq_sqrt hδ.le]
        ring
      rw [hprod]
      have hδ0 : 0 < δ := hδ
      field_simp [hδ0.ne']
      norm_num

private theorem ridge_hilbert_slope_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 < δ)
    (a a' u u' : H) (hu : ‖u‖ ≤ b) :
    |⟪a, u⟫ / (‖a‖ ^ 2 + δ) - ⟪a', u'⟫ / (‖a'‖ ^ 2 + δ)| ≤
      (3 * b / δ) * ‖a - a'‖ + (1 / (2 * Real.sqrt δ)) * ‖u - u'‖ := by
  have hd (x : H) : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hBeta (x w : H) :
      |⟪x, w⟫ / (‖x‖ ^ 2 + δ)| ≤ ‖x‖ * ‖w‖ / (‖x‖ ^ 2 + δ) := by
    rw [abs_div, abs_of_pos (hd x)]
    have hi : |⟪x, w⟫| ≤ ‖x‖ * ‖w‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x w)
    exact div_le_div_of_nonneg_right hi (le_of_lt (hd x))
  have hBetaBound :
      |⟪a', u⟫ / (‖a'‖ ^ 2 + δ)| ≤ b * ‖a'‖ / (‖a'‖ ^ 2 + δ) := by
    calc
      _ ≤ ‖a'‖ * ‖u‖ / (‖a'‖ ^ 2 + δ) := hBeta a' u
      _ ≤ _ := by
        calc
          ‖a'‖ * ‖u‖ / (‖a'‖ ^ 2 + δ) ≤
              ‖a'‖ * b / (‖a'‖ ^ 2 + δ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu (norm_nonneg a')) (le_of_lt (hd a'))
          _ = b * ‖a'‖ / (‖a'‖ ^ 2 + δ) := by ring
  have hnormDiff : |‖a'‖ ^ 2 - ‖a‖ ^ 2| ≤ ‖a - a'‖ * (‖a‖ + ‖a'‖) := by
    calc
      _ = |‖a'‖ - ‖a‖| * (‖a‖ + ‖a'‖) := by
        rw [show ‖a'‖ ^ 2 - ‖a‖ ^ 2 = (‖a'‖ - ‖a‖) * (‖a'‖ + ‖a‖) by ring,
          abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        ring
      _ ≤ ‖a - a'‖ * (‖a‖ + ‖a'‖) := by
        have hnorm : |‖a'‖ - ‖a‖| ≤ ‖a - a'‖ := by
          calc
            |‖a'‖ - ‖a‖| = |‖a‖ - ‖a'‖| := by rw [abs_sub_comm]
            _ ≤ ‖a - a'‖ := abs_norm_sub_norm_le a a'
        exact mul_le_mul_of_nonneg_right hnorm (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hFeatureIdentity :
      ⟪a, u⟫ / (‖a‖ ^ 2 + δ) - ⟪a', u⟫ / (‖a'‖ ^ 2 + δ) =
        (⟪a - a', u⟫ +
          (⟪a', u⟫ / (‖a'‖ ^ 2 + δ)) * (‖a'‖ ^ 2 - ‖a‖ ^ 2)) /
          (‖a‖ ^ 2 + δ) := by
    field_simp [hd a, hd a']
    rw [inner_sub_left]
    ring
  have hFeature :
      |⟪a, u⟫ / (‖a‖ ^ 2 + δ) - ⟪a', u⟫ / (‖a'‖ ^ 2 + δ)| ≤
        (3 * b / δ) * ‖a - a'‖ := by
    rw [hFeatureIdentity, abs_div, abs_of_pos (hd a)]
    have hInner : |⟪a - a', u⟫| ≤ ‖a - a'‖ * b := by
      calc
        _ ≤ ‖a - a'‖ * ‖u‖ := by
          simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (a - a') u)
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    have hFactor := ridge_hilbert_rational_factor ‖a‖ ‖a'‖ δ
      (norm_nonneg _) (norm_nonneg _) hδ
    have hNum :
        |⟪a - a', u⟫ +
            (⟪a', u⟫ / (‖a'‖ ^ 2 + δ)) * (‖a'‖ ^ 2 - ‖a‖ ^ 2)| ≤
          b * ‖a - a'‖ +
            (b * ‖a'‖ / (‖a'‖ ^ 2 + δ)) *
              (‖a - a'‖ * (‖a‖ + ‖a'‖)) := by
      calc
        _ ≤ |⟪a - a', u⟫| +
            |(⟪a', u⟫ / (‖a'‖ ^ 2 + δ)) * (‖a'‖ ^ 2 - ‖a‖ ^ 2)| := abs_add_le _ _
        _ = |⟪a - a', u⟫| +
            |⟪a', u⟫ / (‖a'‖ ^ 2 + δ)| * |‖a'‖ ^ 2 - ‖a‖ ^ 2| := by rw [abs_mul]
        _ ≤ _ := by
          have hInner' : |⟪a - a', u⟫| ≤ b * ‖a - a'‖ := by
            calc
              _ ≤ ‖a - a'‖ * b := hInner
              _ = b * ‖a - a'‖ := by ring
          exact add_le_add hInner'
            (mul_le_mul hBetaBound hnormDiff (abs_nonneg _) (by positivity))
    have hNonneg : 0 ≤ ‖a - a'‖ := norm_nonneg _
    have hFinal :
        (b * ‖a - a'‖ +
          (b * ‖a'‖ / (‖a'‖ ^ 2 + δ)) *
            (‖a - a'‖ * (‖a‖ + ‖a'‖))) / (‖a‖ ^ 2 + δ) ≤
          (3 * b / δ) * ‖a - a'‖ := by
      have hDenA : δ ≤ ‖a‖ ^ 2 + δ := by nlinarith [sq_nonneg (‖a‖)]
      have hDenB : 0 < ‖a'‖ ^ 2 + δ := hd a'
      have hCoeff :
          b / (‖a‖ ^ 2 + δ) +
            b * ‖a'‖ * (‖a‖ + ‖a'‖) /
              ((‖a‖ ^ 2 + δ) * (‖a'‖ ^ 2 + δ)) ≤ 3 * b / δ := by
        have hFirst : b / (‖a‖ ^ 2 + δ) ≤ b / δ := by
          exact div_le_div_of_nonneg_left hb hδ hDenA
        have hSecond : b *
            (‖a'‖ * (‖a‖ + ‖a'‖) /
              ((‖a‖ ^ 2 + δ) * (‖a'‖ ^ 2 + δ))) ≤ b * (2 / δ) := by
          exact mul_le_mul_of_nonneg_left hFactor hb
        have hSecond' : b * ‖a'‖ * (‖a‖ + ‖a'‖) /
              ((‖a‖ ^ 2 + δ) * (‖a'‖ ^ 2 + δ)) ≤ b * (2 / δ) := by
          calc
            _ = b * (‖a'‖ * (‖a‖ + ‖a'‖) /
                ((‖a‖ ^ 2 + δ) * (‖a'‖ ^ 2 + δ))) := by ring
            _ ≤ _ := hSecond
        calc
          _ ≤ b / δ + b * (2 / δ) := add_le_add hFirst hSecond'
          _ = 3 * b / δ := by ring
      have hDenScale : 0 ≤ b / (‖a‖ ^ 2 + δ) := div_nonneg hb (le_of_lt (hd a))
      rw [show (b * ‖a - a'‖ +
          (b * ‖a'‖ / (‖a'‖ ^ 2 + δ)) *
            (‖a - a'‖ * (‖a‖ + ‖a'‖))) / (‖a‖ ^ 2 + δ) =
          (b / (‖a‖ ^ 2 + δ) +
            b * ‖a'‖ * (‖a‖ + ‖a'‖) /
              ((‖a‖ ^ 2 + δ) * (‖a'‖ ^ 2 + δ))) * ‖a - a'‖ by field_simp [hd a, hd a']]
      exact mul_le_mul_of_nonneg_right hCoeff hNonneg
    exact (le_trans (div_le_div_of_nonneg_right hNum (le_of_lt (hd a))) hFinal)
  have hResponse :
      |⟪a', u⟫ / (‖a'‖ ^ 2 + δ) - ⟪a', u'⟫ / (‖a'‖ ^ 2 + δ)| ≤
        (1 / (2 * Real.sqrt δ)) * ‖u - u'‖ := by
    rw [show ⟪a', u⟫ / (‖a'‖ ^ 2 + δ) - ⟪a', u'⟫ / (‖a'‖ ^ 2 + δ) =
        ⟪a', u - u'⟫ / (‖a'‖ ^ 2 + δ) by rw [inner_sub_right]; ring]
    rw [abs_div, abs_of_pos (hd a')]
    have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hAM : 2 * ‖a'‖ * Real.sqrt δ ≤ ‖a'‖ ^ 2 + δ := by
      nlinarith [sq_nonneg (‖a'‖ - Real.sqrt δ), Real.sq_sqrt hδ.le]
    have hInner : |⟪a', u - u'⟫| ≤ ‖a'‖ * ‖u - u'‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) a' (u - u'))
    have hCoeff : ‖a'‖ / (‖a'‖ ^ 2 + δ) ≤ 1 / (2 * Real.sqrt δ) := by
      apply (div_le_div_iff₀ (hd a') (by positivity : 0 < 2 * Real.sqrt δ)).2
      nlinarith [hAM]
    calc
      |⟪a', u - u'⟫| / (‖a'‖ ^ 2 + δ) ≤
          (‖a'‖ * ‖u - u'‖) / (‖a'‖ ^ 2 + δ) := by gcongr
      _ = (‖a'‖ / (‖a'‖ ^ 2 + δ)) * ‖u - u'‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
  calc
    _ = |(⟪a, u⟫ / (‖a‖ ^ 2 + δ) - ⟪a', u⟫ / (‖a'‖ ^ 2 + δ)) +
          (⟪a', u⟫ / (‖a'‖ ^ 2 + δ) - ⟪a', u'⟫ / (‖a'‖ ^ 2 + δ))| := by
      congr 1
      ring
    _ ≤ |⟪a, u⟫ / (‖a‖ ^ 2 + δ) - ⟪a', u⟫ / (‖a'‖ ^ 2 + δ)| +
        |⟪a', u⟫ / (‖a'‖ ^ 2 + δ) - ⟪a', u'⟫ / (‖a'‖ ^ 2 + δ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hFeature hResponse

private theorem ridgeTrain_actual_slope_lipschitz (r : ℕ) (b δ : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ)
    (E F : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    |ridgeTrainSlope b δ E - ridgeTrainSlope b δ F| ≤
      (3 * b / δ + 1 / (2 * Real.sqrt δ)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ) * ‖E - F‖ := by
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  have hN : 0 < r + 1 := by omega
  have hNr : 0 < N := by dsimp [N]; positivity
  let A := ridgeTrainNormalizedCenter (ridgeTrainFeature E)
  let A' := ridgeTrainNormalizedCenter (ridgeTrainFeature F)
  let U := ridgeTrainNormalizedCenter (ridgeTrainClippedResponse b E)
  let U' := ridgeTrainNormalizedCenter (ridgeTrainClippedResponse b F)
  have hU : ‖U‖ ≤ b := by
    have hclip := (euclideanClipping_lipschitz_and_norm (Fin (r + 1)) b hb).2
      (WithLp.toLp 2 (ridgeTrainResponse E))
    have hclip' : ‖WithLp.toLp 2 (ridgeTrainClippedResponse b E)‖ ≤ b * Real.sqrt N := by
      simpa [ridgeTrainClippedResponse, ridgeTrainResponse, Fintype.card_fin,
        Nat.cast_add, Nat.cast_one, N] using hclip
    have hcenter := ridgeTrain_centered_contract hN (ridgeTrainClippedResponse b E)
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    have hsqrtR : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
    have hbound : ‖ridgeTrainNormalizedCenter (ridgeTrainClippedResponse b E)‖ ≤ b := by
      rw [ridgeTrainNormalizedCenter, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hsqrtR)]
      calc
        (Real.sqrt N)⁻¹ * ‖ridgeTrainCentered (ridgeTrainClippedResponse b E)‖ ≤
            (Real.sqrt N)⁻¹ * ‖WithLp.toLp 2 (ridgeTrainClippedResponse b E)‖ :=
          mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hsqrt.le)
        _ ≤ (Real.sqrt N)⁻¹ * (b * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hclip' (inv_nonneg.mpr hsqrt.le)
        _ = b := by field_simp [hsqrtR.ne']
    exact hbound
  have hU' : ‖U'‖ ≤ b := by
    have hclip := (euclideanClipping_lipschitz_and_norm (Fin (r + 1)) b hb).2
      (WithLp.toLp 2 (ridgeTrainResponse F))
    have hclip' : ‖WithLp.toLp 2 (ridgeTrainClippedResponse b F)‖ ≤ b * Real.sqrt N := by
      simpa [ridgeTrainClippedResponse, ridgeTrainResponse, Fintype.card_fin,
        Nat.cast_add, Nat.cast_one, N] using hclip
    have hcenter := ridgeTrain_centered_contract hN (ridgeTrainClippedResponse b F)
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    have hsqrtR : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
    have hbound : ‖ridgeTrainNormalizedCenter (ridgeTrainClippedResponse b F)‖ ≤ b := by
      rw [ridgeTrainNormalizedCenter, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hsqrtR)]
      calc
        (Real.sqrt N)⁻¹ * ‖ridgeTrainCentered (ridgeTrainClippedResponse b F)‖ ≤
            (Real.sqrt N)⁻¹ * ‖WithLp.toLp 2 (ridgeTrainClippedResponse b F)‖ :=
          mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hsqrt.le)
        _ ≤ (Real.sqrt N)⁻¹ * (b * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hclip' (inv_nonneg.mpr hsqrt.le)
        _ = b := by field_simp [hsqrtR.ne']
    exact hbound
  have hclipLip : ‖WithLp.toLp 2 (ridgeTrainClippedResponse b E) -
      WithLp.toLp 2 (ridgeTrainClippedResponse b F)‖ ≤ ‖WithLp.toLp 2
      (fun j : Fin (r + 1) => ridgeTrainResponse E j - ridgeTrainResponse F j)‖ := by
    have h := ((euclideanClipping_lipschitz_and_norm (Fin (r + 1)) b hb).1).dist_le_mul
      (WithLp.toLp 2 (ridgeTrainResponse E)) (WithLp.toLp 2 (ridgeTrainResponse F))
    have h' :
        ‖WithLp.toLp 2 (fun j : Fin (r + 1) =>
          max (min (ridgeTrainResponse E j) b) (-b)) -
          WithLp.toLp 2 (fun j : Fin (r + 1) =>
          max (min (ridgeTrainResponse F j) b) (-b))‖ ≤
          ‖WithLp.toLp 2 (ridgeTrainResponse E) -
            WithLp.toLp 2 (ridgeTrainResponse F)‖ := by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h
    have hvec : WithLp.toLp 2
        (fun j : Fin (r + 1) => ridgeTrainResponse E j - ridgeTrainResponse F j) =
          WithLp.toLp 2 (ridgeTrainResponse E) - WithLp.toLp 2 (ridgeTrainResponse F) := by
      apply PiLp.ext
      intro j
      rfl
    rw [hvec]
    simpa [ridgeTrainClippedResponse, ridgeTrainResponse] using h'
  have hA : ‖A - A'‖ ≤ ‖E - F‖ / Real.sqrt N := by
    have hcenter := ridgeTrain_normalized_center_contract hN
      (ridgeTrainFeature E) (ridgeTrainFeature F)
    have hcoord := ridgeTrain_coordinate_norm_le r E F (Sum.inl 0)
    dsimp [A, A']
    have hcoord' :
        ‖WithLp.toLp 2 (fun i : Fin (r + 1) =>
          ridgeTrainFeature E i - ridgeTrainFeature F i)‖ ≤ ‖E - F‖ := by
      simpa [ridgeTrainFeature] using hcoord
    have hcenter' :
        ‖ridgeTrainNormalizedCenter (ridgeTrainFeature E) -
          ridgeTrainNormalizedCenter (ridgeTrainFeature F)‖ ≤
            ‖WithLp.toLp 2 (fun i : Fin (r + 1) =>
              ridgeTrainFeature E i - ridgeTrainFeature F i)‖ / Real.sqrt N := by
      simpa [N, Nat.cast_add, Nat.cast_one] using hcenter
    exact hcenter'.trans (div_le_div_of_nonneg_right hcoord'
      (Real.sqrt_nonneg _))
  have hUdiff : ‖U - U'‖ ≤ ‖E - F‖ / Real.sqrt N := by
    have hcenter := ridgeTrain_normalized_center_contract hN
      (ridgeTrainClippedResponse b E) (ridgeTrainClippedResponse b F)
    have hclipVec : WithLp.toLp 2
        (fun j : Fin (r + 1) => ridgeTrainClippedResponse b E j -
          ridgeTrainClippedResponse b F j) =
            WithLp.toLp 2 (ridgeTrainClippedResponse b E) -
              WithLp.toLp 2 (ridgeTrainClippedResponse b F) := by
      apply PiLp.ext
      intro j
      rfl
    have hcenter' : ‖U - U'‖ ≤
        ‖WithLp.toLp 2 (ridgeTrainClippedResponse b E) -
          WithLp.toLp 2 (ridgeTrainClippedResponse b F)‖ / Real.sqrt N := by
      simpa [U, U', N, Nat.cast_add, Nat.cast_one, hclipVec] using hcenter
    calc
      _ ≤ ‖WithLp.toLp 2 (ridgeTrainClippedResponse b E) -
          WithLp.toLp 2 (ridgeTrainClippedResponse b F)‖ / Real.sqrt N := hcenter'
      _ ≤ ‖WithLp.toLp 2
          (fun j : Fin (r + 1) => ridgeTrainResponse E j - ridgeTrainResponse F j)‖ /
            Real.sqrt N := by
        apply div_le_div_of_nonneg_right hclipLip (Real.sqrt_nonneg N)
      _ ≤ ‖E - F‖ / Real.sqrt N := by
        gcongr
        exact ridgeTrain_coordinate_norm_le r E F (Sum.inr 0)
  have hInnerE := ridgeTrain_normalized_inner_eq_covariance hN
    (ridgeTrainFeature E) (ridgeTrainClippedResponse b E)
  have hInnerF := ridgeTrain_normalized_inner_eq_covariance hN
    (ridgeTrainFeature F) (ridgeTrainClippedResponse b F)
  have hVarE := ridgeTrain_normalized_center_norm_sq hN (ridgeTrainFeature E)
  have hVarF := ridgeTrain_normalized_center_norm_sq hN (ridgeTrainFeature F)
  have hSlope := ridge_hilbert_slope_lipschitz b δ hb hδ A A' U U' hU
  change |ridgeTrainSlope b δ E - ridgeTrainSlope b δ F| ≤ _
  rw [ridgeTrainSlope, ridgeTrainSlope, ← hInnerE, ← hInnerF,
    ← hVarE, ← hVarF]
  have h := hSlope
  dsimp [A, A', U, U'] at h
  calc
    _ ≤ (3 * b / δ) * ‖A - A'‖ + (1 / (2 * Real.sqrt δ)) * ‖U - U'‖ := h
    _ ≤ (3 * b / δ) * (‖E - F‖ / Real.sqrt N) +
        (1 / (2 * Real.sqrt δ)) * (‖E - F‖ / Real.sqrt N) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hA (by positivity))
        (mul_le_mul_of_nonneg_left hUdiff (by positivity))
    _ = (3 * b / δ + 1 / (2 * Real.sqrt δ)) / Real.sqrt N * ‖E - F‖ := by
      ring
private theorem ridgeTrain_actual_predictor_formula (b δ : {t : ℝ // 0 < t})
    (r : ℕ) (x : ℝ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    stabilizedLinearEstimatorActualTrainingPredictor b δ r x E =
      ridgeTrainMean (ridgeTrainResponse E) +
          ridgeTrainSlope b.val δ.val E *
            (x - ridgeTrainMean (ridgeTrainFeature E)) := by
  classical
  simp [stabilizedLinearEstimatorActualTrainingPredictor,
    LOOConcentration.Manuscript.stabilizedLinearEstimator,
    LOOConcentration.Revision.datasetOfEuclidean,
    ridgeTrainSlope, ridgeTrainVariance, ridgeTrainCovariance,
    ridgeTrainFeature, ridgeTrainResponse, ridgeTrainClippedResponse,
    ridgeTrainMean]
  have hN : (r + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hN]

/-- The public stabilized Ridge slope as the actual predictor difference
between the two source queries 1 and 0. -/
noncomputable def stabilizedLinearEstimatorActualTrainingBeta
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
  fun E => stabilizedLinearEstimatorActualTrainingPredictor b δ r 1 E -
    stabilizedLinearEstimatorActualTrainingPredictor b δ r 0 E

private theorem ridgeTrain_actual_beta_eq_slope (b δ : {t : ℝ // 0 < t})
    (r : ℕ) (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    stabilizedLinearEstimatorActualTrainingBeta b δ r E =
      ridgeTrainSlope b.val δ.val E := by
  rw [stabilizedLinearEstimatorActualTrainingBeta,
    ridgeTrain_actual_predictor_formula b δ r 1 E,
    ridgeTrain_actual_predictor_formula b δ r 0 E]
  ring

/-- The literal public Ridge beta has one parameter-only uniform Lipschitz
constant. Its global Lipschitz constant, Euclidean gradient bound, and
almost-everywhere differentiability hold for every sample size `r + 1`.
The beta formula is established internally from the public predictor
difference, so callers supply no slope or differentiability assumptions. -/
theorem stabilizedLinearEstimator_actual_beta_uniform_lipschitz_gradient
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let rate : ℝ := C / Real.sqrt ((r + 1 : ℕ) : ℝ)
      let K : NNReal := Real.toNNReal rate
      LipschitzWith K (stabilizedLinearEstimatorActualTrainingBeta b δ r) ∧
        (K : ℝ) = rate ∧
        LocallyLipschitz (stabilizedLinearEstimatorActualTrainingBeta b δ r) ∧
        ∀ᵐ E ∂(volume : Measure
          (EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))),
          DifferentiableAt ℝ (stabilizedLinearEstimatorActualTrainingBeta b δ r) E ∧
            ‖gradient (stabilizedLinearEstimatorActualTrainingBeta b δ r) E‖ ≤ rate := by
  let C : ℝ := 3 * b.val / δ.val + 1 / (2 * Real.sqrt δ.val)
  have hδroot : 0 < Real.sqrt δ.val := Real.sqrt_pos.2 δ.property
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos
      (div_pos (mul_pos (by norm_num) b.property) δ.property)
      (div_pos (by norm_num) (mul_pos (by norm_num) hδroot))
  refine ⟨C, hC, ?_⟩
  intro r
  let rate : ℝ := C / Real.sqrt ((r + 1 : ℕ) : ℝ)
  let K : NNReal := Real.toNNReal rate
  have hN : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hroot : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hN
  have hrate : 0 ≤ rate := div_nonneg hC.le hroot.le
  have hK : (K : ℝ) = rate := by
    dsimp [K]
    exact Real.coe_toNNReal rate hrate
  have hLip : LipschitzWith K (stabilizedLinearEstimatorActualTrainingBeta b δ r) := by
    apply LipschitzWith.of_dist_le_mul
    intro E F
    rw [Real.dist_eq, dist_eq_norm, hK]
    change |stabilizedLinearEstimatorActualTrainingBeta b δ r E -
      stabilizedLinearEstimatorActualTrainingBeta b δ r F| ≤ rate * ‖E - F‖
    rw [ridgeTrain_actual_beta_eq_slope, ridgeTrain_actual_beta_eq_slope]
    simpa [rate, C, Nat.cast_add, Nat.cast_one] using
      ridgeTrain_actual_slope_lipschitz r b.val δ.val b.property.le δ.property E F
  have hLoc : LocallyLipschitz
      (stabilizedLinearEstimatorActualTrainingBeta b δ r) := hLip.locallyLipschitz
  refine ⟨hLip, hK, hLoc, ?_⟩
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean
    (stabilizedLinearEstimatorActualTrainingBeta b δ r) hLoc
  filter_upwards [hAE] with E hDiff
  refine ⟨hDiff, ?_⟩
  have hFderiv := norm_fderiv_le_of_lipschitz ℝ
    (x₀ := E) hLip
  have hDualNorm :
      ‖fderiv ℝ (stabilizedLinearEstimatorActualTrainingBeta b δ r) E‖ =
        ‖gradient (stabilizedLinearEstimatorActualTrainingBeta b δ r) E‖ := by
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ _).norm_map _
  calc
    ‖gradient (stabilizedLinearEstimatorActualTrainingBeta b δ r) E‖ =
        ‖fderiv ℝ (stabilizedLinearEstimatorActualTrainingBeta b δ r) E‖ := hDualNorm.symm
    _ ≤ K := hFderiv
    _ = rate := hK

end LOOConcentration.Manuscript.Internal
