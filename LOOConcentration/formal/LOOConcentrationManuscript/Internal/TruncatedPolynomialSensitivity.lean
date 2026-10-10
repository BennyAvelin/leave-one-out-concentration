import LOOConcentrationManuscript.Internal.PolynomialGradientLocalLipschitz
import LOOConcentrationManuscript.Internal.EuclideanClippingConsumer
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Topology Gradient

/-- The dimension and sample-size factors from the source polynomial gradient
bound combine exactly into the clipped sensitivity constant. All powers use
Lean's actual `Real.rpow` conventions, including exponent zero. -/
theorem truncationPolynomial_constant_identity
    (C q b : ℝ) (k m r : ℕ) (hb : 0 ≤ b) :
    (C / (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2))) *
        (b * Real.sqrt ((((k + m) * (r + 1) : ℕ) : ℝ))) ^ q =
      C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
        Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  have hN : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hd : 0 ≤ ((k + m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsqrtN : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hN
  have hsqrtNne : Real.sqrt ((r + 1 : ℕ) : ℝ) ≠ 0 := hsqrtN.ne'
  have hpowN :
      (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2)) =
        Real.sqrt ((r + 1 : ℕ) : ℝ) ^ (q + 1) := by
    exact Real.rpow_div_two_eq_sqrt (q + 1) (le_of_lt hN)
  have hpowN' :
      (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2)) =
        Real.sqrt ((r + 1 : ℕ) : ℝ) ^ q * Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    rw [hpowN, Real.rpow_add hsqrtN q 1, Real.rpow_one]
  have hrootProd :
      Real.sqrt ((((k + m) * (r + 1) : ℕ) : ℝ)) =
        Real.sqrt ((k + m : ℕ) : ℝ) * Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul hd]
  rw [hrootProd]
  have hsplit :
      (b * (Real.sqrt ((k + m : ℕ) : ℝ) * Real.sqrt ((r + 1 : ℕ) : ℝ))) ^ q =
        b ^ q * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q *
          (Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ q := by
    rw [Real.mul_rpow hb (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    ring
  rw [hsplit]
  rw [hpowN']
  have hpowSqrtPos :
      0 < Real.sqrt ((r + 1 : ℕ) : ℝ) ^ q :=
    Real.rpow_pos_of_pos hsqrtN q
  field_simp [hsqrtNne, ne_of_gt hpowSqrtPos]

/-- Uniform source polynomial gradient control implies the actual coordinate-
clipped composition is globally Lipschitz, with the manuscript's
`C (sqrt(k+m))^q b^q / sqrt(n)` sensitivity. The conclusion also gives its
volume-a.e. differentiability and gradient bound, and a punctured local
difference-quotient bound at every dataset. -/
theorem truncatedPolynomialSensitivity
    {ζ : Type*} (k m : ℕ) (b q C : ℝ)
    (hb : 0 ≤ b) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (F : ∀ r : ℕ, ζ →
      EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) → ℝ)
    (hLoc : ∀ r z, LocallyLipschitz (F r z))
    (hGrad : ∀ r z, ∀ᵐ D ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
      ‖gradient (F r z) D‖ ≤
        (C / (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2))) * ‖D‖ ^ q) :
    ∀ r z,
      LipschitzWith
          (Real.toNNReal (C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
            Real.sqrt ((r + 1 : ℕ) : ℝ)))
          (fun D : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              F r z (WithLp.toLp 2 (fun i => max (min (D i) b) (-b)))) ∧
      (∀ᵐ D ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
        DifferentiableAt ℝ
          (fun E : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              F r z (WithLp.toLp 2 (fun i => max (min (E i) b) (-b)))) D ∧
        ‖gradient
          (fun E : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              F r z (WithLp.toLp 2 (fun i => max (min (E i) b) (-b)))) D‖ ≤
          C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
            Real.sqrt ((r + 1 : ℕ) : ℝ)) ∧
      (∀ D : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m (r + 1)),
        ∀ᶠ E in 𝓝[≠] D,
          |F r z (WithLp.toLp 2 (fun i => max (min (E i) b) (-b))) -
            F r z (WithLp.toLp 2 (fun i => max (min (D i) b) (-b)))| /
              ‖E - D‖ ≤
            C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
              Real.sqrt ((r + 1 : ℕ) : ℝ)) := by
  classical
  intro r z
  let clip := fun D : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
    WithLp.toLp 2 (fun i => max (min (D i) b) (-b))
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let dim : ℝ := ((k + m : ℕ) : ℝ)
  let A : ℝ := C / (N ^ ((q + 1) / 2))
  let R : ℝ := b * Real.sqrt (dim * N)
  let B : ℝ := C * (Real.sqrt dim) ^ q * b ^ q / Real.sqrt N
  have hN : 0 < N := by positivity
  have hdim : 0 ≤ dim := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hN _))
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg hb (Real.sqrt_nonneg _)
  have hclip := datasetClipping_lipschitz_and_exact_dimension_bound k m r b hb
  have hclipLip : LipschitzWith 1 clip := by
    simpa only [clip] using hclip.1
  have hclipBound : ∀ D : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m (r + 1)), ‖clip D‖ ≤ R := by
    intro D
    have h := hclip.2 D
    simpa only [clip, R, dim, N, Nat.cast_mul] using h
  have hsourceGrad : ∀ᵐ D ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
      ‖gradient (F r z) D‖ ≤ A * ‖D‖ ^ q := by
    simpa only [A, N] using hGrad r z
  have hlocalBall := polynomialGradient_lipschitzOn_closedBall
    (F r z) (hLoc r z) A q R hA hq hsourceGrad
  have hboundEq : A * R ^ q = B := by
    dsimp [A, R, B, N, dim]
    simpa only [Nat.cast_mul] using
      truncationPolynomial_constant_identity C q b k m r hb
  have hBnonneg : 0 ≤ B := by rw [← hboundEq]; positivity
  have hBcoe : (Real.toNNReal B : ℝ) = B := Real.coe_toNNReal B hBnonneg
  let G : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m (r + 1)) → ℝ := fun D => F r z (clip D)
  have hLip : LipschitzWith (Real.toNNReal B) G := by
    refine LipschitzWith.of_dist_le_mul fun D E => ?_
    have hFD := hlocalBall (clip D) (clip E) (hclipBound D) (hclipBound E)
    have hclipDist := hclipLip.dist_le_mul D E
    have hscale : 0 ≤ A * R ^ q := mul_nonneg hA (Real.rpow_nonneg hR q)
    have hdist : ‖clip D - clip E‖ ≤ ‖D - E‖ := by
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hclipDist
    have hmain : |G D - G E| ≤ B * ‖D - E‖ := by
      calc
        |G D - G E| ≤ A * R ^ q * ‖clip D - clip E‖ := by
          simpa only [G, abs_sub_comm] using hFD
        _ ≤ A * R ^ q * ‖D - E‖ := mul_le_mul_of_nonneg_left hdist hscale
        _ = B * ‖D - E‖ := by rw [hboundEq]
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, hBcoe] using hmain
  have hLipAE :=
    LOOConcentration.Revision.lipschitzWith_ae_differentiableAt_gradient_norm_le hLip
  have hAEResult : ∀ᵐ D ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
      DifferentiableAt ℝ G D ∧ ‖gradient G D‖ ≤ B := by
    filter_upwards [hLipAE] with D hD
    refine ⟨hD.1, ?_⟩
    simpa only [hBcoe] using hD.2
  have hquot : ∀ D : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m (r + 1)),
      ∀ᶠ E in 𝓝[≠] D, |G E - G D| / ‖E - D‖ ≤ B := by
    intro D
    filter_upwards [self_mem_nhdsWithin] with E hED
    have hne : E ≠ D := by simpa using hED
    have hden : 0 < ‖E - D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hnum : |G E - G D| ≤ B * ‖E - D‖ := by
      have h := hLip.norm_sub_le E D
      simpa only [Real.norm_eq_abs, hBcoe] using h
    exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hnum)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [G, B] using hLip
  · simpa only [G, B] using hAEResult
  · intro D
    simpa only [G, B] using hquot D

end LOOConcentration.Manuscript.Internal
