import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Analysis.ClipMollify

/-!
# Clipping and mollification in frozen dataset coordinates

The finite-dimensional convolution acts on the flattened Euclidean space.
`datasetToEuclidean` and its explicit inverse identify that space with the
frozen dataset carrier without changing its unnormalized Euclidean norm.
The segment estimate used below is the conditional input whose planned source
producer is `lemma:quadratic#segment`.
-/

set_option autoImplicit false

open Filter
open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-! The inverse coordinate map for `datasetToEuclidean`. -/

/-- Reconstruct a dataset from its flattened Euclidean coordinates. -/
def datasetFromEuclidean {k m n : ℕ}
    (x : EuclideanSpace ℝ (DatasetCoordinate k m n)) :
    Dataset (Observation k m) n :=
  fun i =>
    (fun j => x (i, Sum.inl j), fun j => x (i, Sum.inr j))

@[simp] theorem datasetToEuclidean_fromEuclidean {k m n : ℕ}
    (x : EuclideanSpace ℝ (DatasetCoordinate k m n)) :
    datasetToEuclidean (datasetFromEuclidean x) = x := by
  apply PiLp.ext
  intro q
  rcases q with ⟨i, c⟩
  cases c <;> simp [datasetToEuclidean, datasetFromEuclidean]

@[simp] theorem datasetFromEuclidean_toEuclidean {k m n : ℕ}
    (D : Dataset (Observation k m) n) :
    datasetFromEuclidean (datasetToEuclidean D) = D := by
  funext i
  apply Prod.ext <;> funext j <;>
    simp [datasetFromEuclidean, datasetToEuclidean]

theorem datasetToEuclidean_sub {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    datasetToEuclidean (D - E) = datasetToEuclidean D - datasetToEuclidean E := by
  apply PiLp.ext
  intro q
  rcases q with ⟨i, c⟩
  cases c <;> simp [datasetToEuclidean]

theorem datasetNorm_fromEuclidean {k m n : ℕ}
    (x : EuclideanSpace ℝ (DatasetCoordinate k m n)) :
    datasetNorm (datasetFromEuclidean x) = ‖x‖ := by
  rw [datasetNorm_eq_euclidean]
  simp

theorem datasetNorm_sub_eq_euclidean {k m n : ℕ}
    (D E : Dataset (Observation k m) n) :
    datasetNorm (D - E) = ‖datasetToEuclidean D - datasetToEuclidean E‖ := by
  rw [datasetNorm_eq_euclidean, datasetToEuclidean_sub]

/-! The exact frozen dataset segment estimate, kept as an internal premise. -/

/-- The source-style segment estimate measured in the frozen dataset norm. -/
def DatasetLinearGrowthSegmentBound {k m n : ℕ}
    (f : Dataset (Observation k m) n → ℝ) (a b : ℝ) : Prop :=
  ∀ D E, |f D - f E| ≤
    datasetNorm (D - E) * (a + b / 2 * (datasetNorm D + datasetNorm E))

theorem datasetSegmentBound_toEuclidean {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b) :
    HasLinearGrowthSegmentBound (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
      f (datasetFromEuclidean x)) a b := by
  intro x y
  have h := hseg (datasetFromEuclidean x) (datasetFromEuclidean y)
  rw [datasetNorm_sub_eq_euclidean, datasetNorm_fromEuclidean,
    datasetNorm_fromEuclidean] at h
  simpa only [datasetToEuclidean_fromEuclidean, dist_eq_norm] using h

theorem continuous_datasetFunction_of_segmentBound {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Continuous (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
      f (datasetFromEuclidean x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let g : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ :=
    fun y => f (datasetFromEuclidean y)
  have hsegE : HasLinearGrowthSegmentBound g a b := by
    simpa only [g] using datasetSegmentBound_toEuclidean hseg
  let K : NNReal := ⟨a + b * (‖x‖ + 1), by positivity⟩
  have hLip : LipschitzOnWith K g (Metric.ball x 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro u hu v hv
    have hud : dist u x < 1 := Metric.mem_ball.mp hu
    have hvd : dist v x < 1 := Metric.mem_ball.mp hv
    rw [dist_eq_norm] at hud hvd
    have hunorm : ‖u‖ ≤ ‖x‖ + 1 := by
      calc
        ‖u‖ = ‖(u - x) + x‖ := by congr 1; abel
        _ ≤ ‖u - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hvnorm : ‖v‖ ≤ ‖x‖ + 1 := by
      calc
        ‖v‖ = ‖(v - x) + x‖ := by congr 1; abel
        _ ≤ ‖v - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hsum : ‖u‖ + ‖v‖ ≤ 2 * ‖x‖ + 2 := by linarith
    have hcoeff : a + b / 2 * (‖u‖ + ‖v‖) ≤ a + b * (‖x‖ + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ b / 2)
      nlinarith
    have hM := hsegE u v
    calc
      dist (g u) (g v) = |g u - g v| := Real.dist_eq _ _
      _ ≤ dist u v * (a + b / 2 * (‖u‖ + ‖v‖)) := hM
      _ ≤ dist u v * (a + b * (‖x‖ + 1)) :=
        mul_le_mul_of_nonneg_left hcoeff dist_nonneg
      _ = (K : ℝ) * dist u v := by
        change dist u v * (a + b * (‖x‖ + 1)) =
          (a + b * (‖x‖ + 1)) * dist u v
        ring
  exact hLip.continuousOn.continuousAt (Metric.ball_mem_nhds x zero_lt_one)

/-- The mollified function, evaluated on the Euclidean coordinates of a
frozen dataset. -/
noncomputable def datasetClipThenMollify {k m n : ℕ}
    (f : Dataset (Observation k m) n → ℝ) (N η : ℝ) :
    EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ :=
  clipThenMollify (fun x => f (datasetFromEuclidean x)) N η

theorem datasetClipThenMollify_close {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {N η a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η)
    (D : Dataset (Observation k m) n) :
    |datasetClipThenMollify f N η (datasetToEuclidean D) -
      clipValue N (f D)| ≤
        η * (a + b * datasetNorm D + b * η / 2) := by
  have hf := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hsegE := datasetSegmentBound_toEuclidean hseg
  have hclip := clipFunction_segmentBound (N := N) hsegE
  have h := clipThenMollify_close (f := fun x => f (datasetFromEuclidean x))
    hf hη hclip ha hb (datasetToEuclidean D)
  simpa [datasetClipThenMollify, clipFunction, datasetNorm_eq_euclidean] using h

theorem datasetClipThenMollify_fderiv_bound {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {N η a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η)
    (D : Dataset (Observation k m) n) :
    ‖fderiv ℝ (datasetClipThenMollify f N η) (datasetToEuclidean D)‖ ≤
      a + b * η + b * datasetNorm D := by
  have hf := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hsegE := datasetSegmentBound_toEuclidean hseg
  have hclip := clipFunction_segmentBound (N := N) hsegE
  have h := clipThenMollify_fderiv_bound
    (f := fun x => f (datasetFromEuclidean x)) hf hη hclip ha hb
    (datasetToEuclidean D)
  simpa [datasetClipThenMollify, datasetNorm_eq_euclidean] using h

theorem datasetClipThenMollify_tendsto {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {N a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (D : Dataset (Observation k m) n) :
    Tendsto (fun η : ℝ =>
      datasetClipThenMollify f N η (datasetToEuclidean D))
      (𝓝[>] (0 : ℝ)) (𝓝 (clipValue N (f D))) := by
  have hf := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hsegE := datasetSegmentBound_toEuclidean hseg
  have hclip := clipFunction_segmentBound (N := N) hsegE
  let c : ℝ := a + b * datasetNorm D
  have hfactor : Tendsto (fun η : ℝ => c + b * η / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    convert tendsto_const_nhds.add ((hid.const_mul b).div_const 2) using 1
    simp [c]
  have herror : Tendsto (fun η : ℝ => η * (c + b * η / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.mul hfactor
  apply (Metric.tendsto_nhds).2
  intro ε hε
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      η * (c + b * η / 2) < ε := herror.eventually (gt_mem_nhds hε)
  have hclose : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      dist (datasetClipThenMollify f N η (datasetToEuclidean D))
        (clipValue N (f D)) ≤ η * (c + b * η / 2) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have h := datasetClipThenMollify_close (N := N) hseg ha hb hη D
    simpa [c, Real.dist_eq] using h
  filter_upwards [hsmall, hclose] with η hη hηclose
  exact lt_of_le_of_lt hηclose hη

theorem datasetClipThenMollify_range {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {N η a b : ℝ}
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) (hη : 0 < η)
    (x : EuclideanSpace ℝ (DatasetCoordinate k m n)) :
    -N ≤ datasetClipThenMollify f N η x ∧
      datasetClipThenMollify f N η x ≤ N := by
  have hf := continuous_datasetFunction_of_segmentBound hseg ha hb
  simpa [datasetClipThenMollify] using
    (clipThenMollify_range (f := fun y => f (datasetFromEuclidean y)) hf hN hη x)

/-- At a fixed clipping level, the mollified means converge under any
probability measure on the frozen Euclidean dataset coordinates. Boundedness
of the clipped family supplies the integrable majorant, so a second moment
assumption is not needed for this fixed-cutoff limit. -/
theorem datasetClipThenMollify_integral_tendsto {k m n : ℕ}
    {f : Dataset (Observation k m) n → ℝ} {N a b : ℝ}
    {μ : Measure (EuclideanSpace ℝ (DatasetCoordinate k m n))}
    [IsProbabilityMeasure μ]
    (hseg : DatasetLinearGrowthSegmentBound f a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) :
    Tendsto (fun η : ℝ =>
      ∫ x, datasetClipThenMollify f N η x ∂μ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, clipValue N (f (datasetFromEuclidean x)) ∂μ)) := by
  have hf := continuous_datasetFunction_of_segmentBound hseg ha hb
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : EuclideanSpace ℝ (DatasetCoordinate k m n) => N)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change AEStronglyMeasurable
      (clipThenMollify (fun x => f (datasetFromEuclidean x)) N η) μ
    exact (contDiff_clipThenMollify hf hη).continuous.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with η hη
    filter_upwards with x
    have hrange := datasetClipThenMollify_range hseg ha hb hN hη x
    have habs : |datasetClipThenMollify f N η x| ≤ N := abs_le.mpr hrange
    simpa [Real.norm_eq_abs] using habs
  · exact integrable_const N
  · filter_upwards with x
    simpa using datasetClipThenMollify_tendsto (N := N) hseg ha hb
      (datasetFromEuclidean x)

end LOOConcentration
