import LOOConcentrationManuscript.Internal.TruncatedPolynomialSensitivity
import LOOConcentration.Concentration.SegmentEstimate
import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentration.Frozen.Foundations.FittedLoss

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

/-- The polynomial truncation theorem applied to the manuscript's actual
fitted loss on flattened training data. The assumptions are the source's
unclipped locally Lipschitz and volume-a.e. gradient-growth fields, uniform in
training size and query; the conclusion concerns the literal coordinate
truncator on the same dataset carrier. -/
theorem actualFittedLoss_truncatedPolynomialSensitivity
    {k m : ℕ}
    (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (b q C : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hLoc : ∀ r z, LocallyLipschitz
      (fun D : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
        LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean D) z))
    (hGrad : ∀ r z, ∀ᵐ D ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
      ‖gradient (fun E : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
        LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean E) z) D‖ ≤
        (C / (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2))) * ‖D‖ ^ q) :
    ∀ r z,
      LipschitzWith
          (Real.toNNReal (C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
            Real.sqrt ((r + 1 : ℕ) : ℝ)))
          (fun D : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean
                  (WithLp.toLp 2 (fun i => max (min (D i) b) (-b)))) z) ∧
      (∀ᵐ D ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)))),
        DifferentiableAt ℝ
          (fun E : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean
                  (WithLp.toLp 2 (fun i => max (min (E i) b) (-b)))) z) D ∧
        ‖gradient
          (fun E : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
              LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean
                  (WithLp.toLp 2 (fun i => max (min (E i) b) (-b)))) z) D‖ ≤
          C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
            Real.sqrt ((r + 1 : ℕ) : ℝ)) ∧
      (∀ D : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m (r + 1)),
        ∀ᶠ E in 𝓝[≠] D,
          |LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean
                  (WithLp.toLp 2 (fun i => max (min (E i) b) (-b)))) z -
            LOOConcentration.fittedLoss (T r) L
                (LOOConcentration.Revision.datasetOfEuclidean
                  (WithLp.toLp 2 (fun i => max (min (D i) b) (-b)))) z| /
              ‖E - D‖ ≤
            C * (Real.sqrt ((k + m : ℕ) : ℝ)) ^ q * b ^ q /
              Real.sqrt ((r + 1 : ℕ) : ℝ)) := by
  exact truncatedPolynomialSensitivity k m b q C hb hq hC
    (fun r z D => LOOConcentration.fittedLoss (T r) L
      (LOOConcentration.Revision.datasetOfEuclidean D) z) hLoc hGrad

/-- Pulling a Euclidean Lipschitz function back to the frozen dataset carrier
preserves its global Lipschitz bound in the source dataset norm. -/
private def euclideanLipschitzDatasetPullback
    {k m n : ℕ}
    (F : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hLip : LipschitzWith (Real.toNNReal B) F) :
    LOOConcentration.LocallyLipschitzDataFunction k m n := by
  refine ⟨fun E : LOOConcentration.DataCarrier k m n =>
      F (LOOConcentration.datasetToEuclidean E), ?_⟩
  intro E
  refine ⟨Set.univ, Filter.univ_mem, B, hB, ?_⟩
  intro E hE G hG
  have hcoordSub :
      LOOConcentration.datasetToEuclidean (E - G) =
        LOOConcentration.datasetToEuclidean E -
          LOOConcentration.datasetToEuclidean G := by
    apply PiLp.ext
    rintro ⟨i, j⟩
    cases j <;> rfl
  have hnorm : LOOConcentration.datasetNorm (E - G) =
      ‖LOOConcentration.datasetToEuclidean E -
        LOOConcentration.datasetToEuclidean G‖ := by
    rw [LOOConcentration.datasetNorm_eq_euclidean, hcoordSub]
  have hBcoe : (Real.toNNReal B : ℝ) = B := Real.coe_toNNReal B hB
  have hdist := hLip.dist_le_mul
    (LOOConcentration.datasetToEuclidean E)
    (LOOConcentration.datasetToEuclidean G)
  have hreal :
      |F (LOOConcentration.datasetToEuclidean E) -
        F (LOOConcentration.datasetToEuclidean G)| ≤
        B * ‖LOOConcentration.datasetToEuclidean E -
          LOOConcentration.datasetToEuclidean G‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, hBcoe] using hdist
  calc
    |F (LOOConcentration.datasetToEuclidean E) -
        F (LOOConcentration.datasetToEuclidean G)| ≤
        B * ‖LOOConcentration.datasetToEuclidean E -
          LOOConcentration.datasetToEuclidean G‖ := hreal
    _ = B * LOOConcentration.datasetNorm (E - G) := by rw [hnorm]

/-- A global source-norm Lipschitz bound controls the frozen punctured
limsup local slope at every dataset. -/
private theorem euclideanLipschitzDatasetPullback_localSlope_le
    {k m n : ℕ}
    (F : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hLip : LipschitzWith (Real.toNNReal B) F)
    (D : LOOConcentration.DataCarrier k m n) :
    LOOConcentration.datasetLocalSlope
      (euclideanLipschitzDatasetPullback F B hB hLip) D ≤ B := by
  let f := euclideanLipschitzDatasetPullback F B hB hLip
  let quotient : LOOConcentration.DataCarrier k m n → ℝ := fun E =>
    |f.1 E - f.1 D| / LOOConcentration.datasetNorm (E - D)
  have hbounded : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) quotient := by
    simpa only [quotient, f] using LOOConcentration.datasetSlope_bounded f D
  have hcobounded : (𝓝[≠] D).IsCoboundedUnder (· ≤ ·) quotient := by
    simpa only [quotient, f] using LOOConcentration.datasetSlope_cobounded f D
  rw [LOOConcentration.datasetLocalSlope]
  change limsup quotient (𝓝[≠] D) ≤ B
  apply (Filter.limsup_le_iff' hcobounded hbounded).2
  intro c hc
  filter_upwards [self_mem_nhdsWithin] with E hED
  have hne : E ≠ D := by simpa using hED
  have hden : 0 < LOOConcentration.datasetNorm (E - D) :=
    LOOConcentration.datasetNorm_sub_pos hne
  have hsource : |f.1 E - f.1 D| ≤ B * LOOConcentration.datasetNorm (E - D) := by
    have hcoordSub :
        LOOConcentration.datasetToEuclidean (E - D) =
          LOOConcentration.datasetToEuclidean E -
            LOOConcentration.datasetToEuclidean D := by
      apply PiLp.ext
      rintro ⟨i, j⟩
      cases j <;> rfl
    have hnorm : LOOConcentration.datasetNorm (E - D) =
        ‖LOOConcentration.datasetToEuclidean E -
          LOOConcentration.datasetToEuclidean D‖ := by
      rw [LOOConcentration.datasetNorm_eq_euclidean, hcoordSub]
    have hBcoe : (Real.toNNReal B : ℝ) = B := Real.coe_toNNReal B hB
    have hdist := hLip.dist_le_mul
      (LOOConcentration.datasetToEuclidean E)
      (LOOConcentration.datasetToEuclidean D)
    have hreal :
        |F (LOOConcentration.datasetToEuclidean E) -
          F (LOOConcentration.datasetToEuclidean D)| ≤
          B * ‖LOOConcentration.datasetToEuclidean E -
            LOOConcentration.datasetToEuclidean D‖ := by
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, hBcoe] using hdist
    calc
      |f.1 E - f.1 D| =
          |F (LOOConcentration.datasetToEuclidean E) -
            F (LOOConcentration.datasetToEuclidean D)| := rfl
      _ ≤ B * ‖LOOConcentration.datasetToEuclidean E -
          LOOConcentration.datasetToEuclidean D‖ := hreal
      _ = B * LOOConcentration.datasetNorm (E - D) := by rw [hnorm]
  have hnum : |f.1 E - f.1 D| ≤ c * LOOConcentration.datasetNorm (E - D) := by
    calc
      |f.1 E - f.1 D| ≤ B * LOOConcentration.datasetNorm (E - D) := hsource
      _ ≤ c * LOOConcentration.datasetNorm (E - D) :=
        mul_le_mul_of_nonneg_right (le_of_lt hc) (Real.sqrt_nonneg _)
  exact (div_le_iff₀ hden).2 hnum

/-- The actual clipped fitted loss has the manuscript sensitivity bound for
its frozen dataset local slope at every dataset and query. The theorem also
identifies the subtype's underlying function with the literal coordinate-clipped
fitted loss. -/
theorem actualFittedLoss_truncatedPolynomial_datasetLocalSlope
    {k m : ℕ}
    (T : ∀ r : ℕ, LOOConcentration.Estimator (k + 1) (m + 1) (r + 1))
    (L : LOOConcentration.Responses (m + 1) → LOOConcentration.Responses (m + 1) → ℝ)
    (b q C : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hLoc : ∀ r z, LocallyLipschitz
      (fun D : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (r + 1)) =>
        LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean D) z))
    (hGrad : ∀ r z, ∀ᵐ D ∂(volume : Measure
        (EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (r + 1)))),
      ‖gradient (fun E : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (r + 1)) =>
        LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean E) z) D‖ ≤
        (C / (((r + 1 : ℕ) : ℝ) ^ ((q + 1) / 2))) * ‖D‖ ^ q) :
    ∀ r z,
      ∃ f : LOOConcentration.LocallyLipschitzDataFunction k m r,
        (∀ E, f.1 E = LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean
            (WithLp.toLp 2 (fun i => max
              (min (LOOConcentration.datasetToEuclidean E i) b) (-b)))) z) ∧
        (∀ D, LOOConcentration.datasetLocalSlope f D ≤
          C * (Real.sqrt (((k + 1) + (m + 1) : ℕ) : ℝ)) ^ q * b ^ q /
            Real.sqrt ((r + 1 : ℕ) : ℝ)) := by
  intro r z
  let clip := fun x : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (r + 1)) =>
    WithLp.toLp 2 (fun i => max (min (x i) b) (-b))
  let F := fun x : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (r + 1)) =>
    LOOConcentration.fittedLoss (T r) L
      (LOOConcentration.Revision.datasetOfEuclidean (clip x)) z
  let B := C * (Real.sqrt (((k + 1) + (m + 1) : ℕ) : ℝ)) ^ q * b ^ q /
    Real.sqrt ((r + 1 : ℕ) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hLip : LipschitzWith (Real.toNNReal B) F := by
    simpa only [F, clip, B, Nat.cast_add] using
      (truncatedPolynomialSensitivity (k + 1) (m + 1) b q C hb hq hC
        (fun s z x => LOOConcentration.fittedLoss (T s) L
          (LOOConcentration.Revision.datasetOfEuclidean x) z)
        hLoc hGrad r z).1
  refine ⟨euclideanLipschitzDatasetPullback F B hB hLip, ?_, ?_⟩
  · intro E
    rfl
  · intro D
    exact euclideanLipschitzDatasetPullback_localSlope_le F B hB hLip D

end LOOConcentration.Manuscript.Internal
