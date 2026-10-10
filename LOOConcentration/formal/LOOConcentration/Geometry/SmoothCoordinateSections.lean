import LOOConcentration.FunctionalInequalities.CoordinatePoincare
import LOOConcentration.Geometry.BlockDerivativeNorm
import LOOConcentration.Geometry.SmoothLocalSlope
import LOOConcentration.Geometry.SmoothObservationSlope
import LOOConcentration.Geometry.NormTransport
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth coordinate sections and their energies

For the actual `piFinSuccAbove` insertion, flattening the section is an affine
map whose linear part is the isometric observation-block inclusion. Its
derivative is therefore the corresponding restriction of the full derivative.
The reviewed local-slope identities give the exact collective squared-slope
identity and transfer full squared-slope integrability to every joint section
law.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- Insert an observation at its actual `Fin.succAbove` coordinate, preserving
the order of all tail coordinates. -/
def smoothCoordinateSectionInsert {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) : DataCarrier k m n :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail)

/-- Recover the actual tail of a dataset after splitting at coordinate `i`. -/
def smoothCoordinateSectionTail {k m n : ℕ}
    (i : Fin (n + 1)) (D : DataCarrier k m n) :
    Fin n → Observation (k + 1) (m + 1) :=
  ((MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i) D).2

@[simp] theorem smoothCoordinateSectionInsert_at {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) :
    smoothCoordinateSectionInsert i tail z i = z := by
  simp [smoothCoordinateSectionInsert,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

@[simp] theorem smoothCoordinateSectionTail_insert {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) :
    smoothCoordinateSectionTail i (smoothCoordinateSectionInsert i tail z) = tail := by
  simp [smoothCoordinateSectionTail, smoothCoordinateSectionInsert,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- The exact affine offset of the flattened coordinate insertion. -/
noncomputable def smoothCoordinateSectionOffset {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1)) :
    EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
  datasetToEuclidean (smoothCoordinateSectionInsert i tail 0)

/-- The affine Euclidean map obtained by inserting the variable observation
block and fixing the actual `Fin.succAbove` tail. -/
noncomputable def smoothCoordinateSectionAffine {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1)) :
    EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
  fun x => datasetBlockInclusion (k := k) (m := m) (n := n) i x +
    smoothCoordinateSectionOffset i tail

private theorem datasetBlockInclusion_coordinate {k m n : ℕ}
    (i : Fin (n + 1))
    (v : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)))
    (j : Fin (n + 1)) (a : ObservationCoordinate (k + 1) (m + 1)) :
    (datasetBlockInclusion (k := k) (m := m) (n := n) i v).ofLp (j, a) =
      if j = i then v.ofLp a else 0 := by
  classical
  let evalObs : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →ₗ[ℝ] ℝ :=
    (LinearMap.proj a).comp
      (WithLp.linearEquiv (2 : ENNReal) ℝ
        (ObservationCoordinate (k + 1) (m + 1) → ℝ)).toLinearMap
  let evalData : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (j, a)).comp
      (WithLp.linearEquiv (2 : ENNReal) ℝ
        (DatasetCoordinate (k + 1) (m + 1) (n + 1) → ℝ)).toLinearMap
  let L := evalData.comp
    (datasetBlockInclusion (k := k) (m := m) (n := n) i).toLinearMap
  let R : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →ₗ[ℝ] ℝ :=
    if j = i then evalObs else 0
  have hLR : L = R := by
    apply LinearMap.ext_on_range
      (v := fun b => EuclideanSpace.basisFun
        (ObservationCoordinate (k + 1) (m + 1)) ℝ b)
    · exact (EuclideanSpace.basisFun
        (ObservationCoordinate (k + 1) (m + 1)) ℝ).toBasis.span_eq
    · intro b
      by_cases hji : j = i
      · subst j
        dsimp [L, R, evalData, evalObs]
        simp only [WithLp.linearEquiv_apply]
        rw [EuclideanSpace.basisFun_apply, datasetBlockInclusion_single]
        simp [PiLp.single_apply]
      · dsimp [L, R, evalData, evalObs]
        simp only [WithLp.linearEquiv_apply]
        rw [EuclideanSpace.basisFun_apply, datasetBlockInclusion_single]
        simp [hji]
  have hv := congrArg (fun T : _ →ₗ[ℝ] ℝ => T v) hLR
  by_cases hji : j = i
  · subst j
    simpa [L, R, evalData, evalObs, LinearMap.comp_apply,
      WithLp.linearEquiv, WithLp.addEquiv] using hv
  · simpa [L, R, evalData, evalObs, hji, LinearMap.comp_apply,
      WithLp.linearEquiv, WithLp.addEquiv] using hv

/-- The affine section is the literal flattened dataset insertion, under the
frozen observation coordinate map. -/
theorem smoothCoordinateSectionAffine_eq_insert {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) :
    smoothCoordinateSectionAffine i tail (observationToEuclidean z) =
      datasetToEuclidean (smoothCoordinateSectionInsert i tail z) := by
  apply PiLp.ext
  intro q
  rcases q with ⟨j, a⟩
  by_cases hji : j = i
  · subst j
    simp [smoothCoordinateSectionAffine, smoothCoordinateSectionOffset,
      smoothCoordinateSectionInsert, datasetBlockInclusion_coordinate,
      datasetToEuclidean, observationToEuclidean,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
  · rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨j', h⟩
    · exact (hji h).elim
    · subst j
      simp [smoothCoordinateSectionAffine, smoothCoordinateSectionOffset,
        smoothCoordinateSectionInsert, datasetBlockInclusion_coordinate,
        datasetToEuclidean, observationToEuclidean,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- The scalar Euclidean function on the variable block of a smooth full
dataset test. -/
noncomputable def smoothCoordinateSectionFunction {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1)) :
    EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) → ℝ :=
  fun x => f (smoothCoordinateSectionAffine i tail x)

theorem contDiff_smoothCoordinateSectionFunction {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (tail : Fin n → Observation (k + 1) (m + 1)) :
    ContDiff ℝ 1 (smoothCoordinateSectionFunction f i tail) := by
  let A : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
    (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap
  have hA : ContDiff ℝ 1 (fun x => A x) := by
    simpa using (contDiff_id.continuousLinearMap_comp A)
  have hOffset : ContDiff ℝ 1
      (fun _ : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) =>
        smoothCoordinateSectionOffset i tail) := contDiff_const
  have hAffine : ContDiff ℝ 1 (smoothCoordinateSectionAffine i tail) := by
    change ContDiff ℝ 1 (fun x => A x + smoothCoordinateSectionOffset i tail)
    exact hA.add hOffset
  exact hf.comp hAffine

/-- The derivative of the affine insertion is exactly the actual isometric
dataset block inclusion. -/
theorem fderiv_smoothCoordinateSectionAffine {k m n : ℕ}
    (i : Fin (n + 1)) (tail : Fin n → Observation (k + 1) (m + 1))
    (x : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1))) :
    fderiv ℝ (smoothCoordinateSectionAffine i tail) x =
      (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap := by
  let A : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
    (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap
  have hA : HasFDerivAt (smoothCoordinateSectionAffine i tail) A x := by
    change HasFDerivAt (fun y => A y + smoothCoordinateSectionOffset i tail) A x
    exact (ContinuousLinearMap.hasFDerivAt A).add_const
      (smoothCoordinateSectionOffset i tail)
  exact hA.fderiv

/-- The scalar derivative on a smooth coordinate section is the full
derivative composed with the actual block inclusion. -/
theorem fderiv_smoothCoordinateSectionFunction {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (tail : Fin n → Observation (k + 1) (m + 1))
    (x : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1))) :
    fderiv ℝ (smoothCoordinateSectionFunction f i tail) x =
      (fderiv ℝ f (smoothCoordinateSectionAffine i tail x)).comp
        (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap := by
  have hAffine := fderiv_smoothCoordinateSectionAffine i tail x
  have hfAt : DifferentiableAt ℝ f (smoothCoordinateSectionAffine i tail x) :=
    (hf.differentiable one_ne_zero) _
  have hAffineAt : DifferentiableAt ℝ (smoothCoordinateSectionAffine i tail) x :=
    by
      change DifferentiableAt ℝ (fun y =>
        (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap y +
          smoothCoordinateSectionOffset i tail) x
      exact (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap.differentiableAt.add_const _
  calc
    fderiv ℝ (smoothCoordinateSectionFunction f i tail) x =
        fderiv ℝ (f ∘ smoothCoordinateSectionAffine i tail) x := rfl
    _ = (fderiv ℝ f (smoothCoordinateSectionAffine i tail x)).comp
        (fderiv ℝ (smoothCoordinateSectionAffine i tail) x) :=
      fderiv_comp x hfAt hAffineAt
    _ = (fderiv ℝ f (smoothCoordinateSectionAffine i tail x)).comp
        (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap := by
      rw [hAffine]

/-- The actual locally Lipschitz section witness is the frozen smooth
observation pullback of the affine Euclidean section. -/
theorem coordinateSectionWitness_smoothCoordinateSection {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (tail : Fin n → Observation (k + 1) (m + 1)) :
    coordinateSectionWitness (smoothDatasetPullback f hf) i tail =
      smoothObservationPullback (smoothCoordinateSectionFunction f i tail)
        (contDiff_smoothCoordinateSectionFunction f hf i tail) := by
  apply Subtype.ext
  funext z
  simp only [coordinateSectionWitness, smoothDatasetPullback,
    smoothObservationPullback, smoothCoordinateSectionFunction]
  exact congrArg f (smoothCoordinateSectionAffine_eq_insert i tail z).symm

/-- Exact derivative-norm formula for each actual smooth coordinate-section
local slope. -/
theorem observationLocalSlope_smoothCoordinateSection_eq {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope
        (coordinateSectionWitness (smoothDatasetPullback f hf) i tail) z =
      ‖(fderiv ℝ f (datasetToEuclidean
          (smoothCoordinateSectionInsert i tail z))).comp
        (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ := by
  rw [coordinateSectionWitness_smoothCoordinateSection f hf i tail]
  rw [observationLocalSlope_smoothPullback_eq
    (smoothCoordinateSectionFunction f i tail)
    (contDiff_smoothCoordinateSectionFunction f hf i tail) z]
  rw [fderiv_smoothCoordinateSectionFunction f hf i tail
    (observationToEuclidean z)]
  rw [smoothCoordinateSectionAffine_eq_insert i tail z]

/-- The exact sum of actual coordinate-section squared slopes is the full
frozen dataset squared slope for every smooth flattened test. -/
theorem sum_smoothCoordinateSection_slope_sq {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (D : DataCarrier k m n) :
    (∑ i : Fin (n + 1),
      (observationLocalSlope
        (coordinateSectionWitness (smoothDatasetPullback f hf) i
          (smoothCoordinateSectionTail i D)) (D i)) ^ 2) =
      (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2 := by
  calc
    (∑ i : Fin (n + 1),
      (observationLocalSlope
        (coordinateSectionWitness (smoothDatasetPullback f hf) i
          (smoothCoordinateSectionTail i D)) (D i)) ^ 2) =
      ∑ i : Fin (n + 1),
        ‖(fderiv ℝ f (datasetToEuclidean D)).comp
          (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [observationLocalSlope_smoothCoordinateSection_eq]
      have hinsert : smoothCoordinateSectionInsert i
          (smoothCoordinateSectionTail i D) (D i) = D := by
        simp [smoothCoordinateSectionInsert, smoothCoordinateSectionTail,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      rw [hinsert]
    _ = ‖fderiv ℝ f (datasetToEuclidean D)‖ ^ 2 :=
      sum_datasetBlock_fderiv_norm_sq f (datasetToEuclidean D)
    _ = (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2 := by
      rw [datasetLocalSlope_smoothPullback_eq]

/-- Each actual section energy is pointwise bounded by the full smooth-test
energy at its inserted dataset. -/
theorem smoothCoordinateSection_slope_sq_le_full {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1))
    (tail : Fin n → Observation (k + 1) (m + 1))
    (z : Observation (k + 1) (m + 1)) :
    (observationLocalSlope
      (coordinateSectionWitness (smoothDatasetPullback f hf) i tail) z) ^ 2 ≤
      (datasetLocalSlope (smoothDatasetPullback f hf)
        (smoothCoordinateSectionInsert i tail z)) ^ 2 := by
  have hsum := sum_smoothCoordinateSection_slope_sq f hf
    (smoothCoordinateSectionInsert i tail z)
  have hsingle := Finset.single_le_sum
    (fun j _ => sq_nonneg (observationLocalSlope
      (coordinateSectionWitness (smoothDatasetPullback f hf) j
        (smoothCoordinateSectionTail j
          (smoothCoordinateSectionInsert i tail z)))
      (smoothCoordinateSectionInsert i tail z j)))
    (Finset.mem_univ i)
  have htail : smoothCoordinateSectionTail i
      (smoothCoordinateSectionInsert i tail z) = tail :=
    smoothCoordinateSectionTail_insert i tail z
  have hz : smoothCoordinateSectionInsert i tail z i = z :=
    smoothCoordinateSectionInsert_at i tail z
  simpa [htail, hz] using hsingle.trans_eq hsum

/-- Joint squared-slope energy of an actual smooth coordinate section. -/
noncomputable def smoothCoordinateSectionEnergy {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1)) :
    Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) → ℝ :=
  fun p =>
    (observationLocalSlope
      (coordinateSectionWitness (smoothDatasetPullback f hf) i p.2) p.1) ^ 2

private theorem continuous_datasetToEuclidean_sections {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation (k + 1) (m + 1)) N →
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) N)) := by
  change Continuous (fun D : Dataset (Observation (k + 1) (m + 1)) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate (k + 1) (m + 1) N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate (k + 1) (m + 1) N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl a => exact ((continuous_apply a).comp continuous_fst).comp (continuous_apply i)
    | inr b => exact ((continuous_apply b).comp continuous_snd).comp (continuous_apply i))

private def smoothCoordinateSectionInsertPair {k m n : ℕ}
    (i : Fin (n + 1)) :
    Observation (k + 1) (m + 1) × (Fin n → Observation (k + 1) (m + 1)) →
      DataCarrier k m n :=
  fun p => (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm p

private theorem continuous_smoothCoordinateSectionInsertPair {k m n : ℕ}
    (i : Fin (n + 1)) :
    Continuous (smoothCoordinateSectionInsertPair (k := k) (m := m) i) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    have heval : (fun p : Observation (k + 1) (m + 1) ×
        (Fin n → Observation (k + 1) (m + 1)) =>
        smoothCoordinateSectionInsertPair i p i) = Prod.fst := by
      funext p
      simp [smoothCoordinateSectionInsertPair,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rw [heval]
    exact continuous_fst
  · rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨j', h⟩
    · exact (hji h).elim
    · subst j
      have heval : (fun p : Observation (k + 1) (m + 1) ×
          (Fin n → Observation (k + 1) (m + 1)) =>
          smoothCoordinateSectionInsertPair i p (i.succAbove j')) = fun p => p.2 j' := by
        funext p
        simp [smoothCoordinateSectionInsertPair,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      rw [heval]
      exact (continuous_apply j').comp continuous_snd

private theorem continuous_smoothCoordinateSectionEnergy {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin (n + 1)) :
    Continuous (smoothCoordinateSectionEnergy f hf i) := by
  let A := (datasetBlockInclusion (k := k) (m := m) (n := n) i).toContinuousLinearMap
  have hflat : Continuous (fun p : Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) =>
      datasetToEuclidean (smoothCoordinateSectionInsertPair i p)) :=
    continuous_datasetToEuclidean_sections.comp
      (continuous_smoothCoordinateSectionInsertPair i)
  have hderiv : Continuous (fun p : Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) =>
      fderiv ℝ f (datasetToEuclidean (smoothCoordinateSectionInsertPair i p))) :=
    (hf.continuous_fderiv one_ne_zero).comp hflat
  have hcomp : Continuous (fun p : Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) =>
      (fderiv ℝ f (datasetToEuclidean (smoothCoordinateSectionInsertPair i p))).comp A) :=
    hderiv.clm_comp_const A
  have hnorm : Continuous (fun p : Observation (k + 1) (m + 1) ×
      (Fin n → Observation (k + 1) (m + 1)) =>
      ‖(fderiv ℝ f (datasetToEuclidean (smoothCoordinateSectionInsertPair i p))).comp A‖ ^ 2) :=
    (continuous_norm.comp hcomp).pow 2
  have heq : smoothCoordinateSectionEnergy f hf i = fun p =>
      ‖(fderiv ℝ f (datasetToEuclidean (smoothCoordinateSectionInsertPair i p))).comp A‖ ^ 2 := by
    funext p
    have h := observationLocalSlope_smoothCoordinateSection_eq f hf i p.2 p.1
    have hsq := congrArg (fun r : ℝ => r ^ 2) h
    simpa [smoothCoordinateSectionEnergy, smoothCoordinateSectionInsertPair,
      smoothCoordinateSectionInsert, A] using hsq
  rw [heq]
  exact hnorm

/-- Full squared-slope integrability supplies the joint integrability of each
actual coordinate-section energy, using the insertion measure-preserving
equivalence and the pointwise partial-energy bound. -/
theorem integrable_smoothCoordinateSectionEnergy_of_fullEnergy
    {k m n : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hfull : Integrable
      (fun D : DataCarrier k m n =>
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ))
    (i : Fin (n + 1)) :
    Integrable (smoothCoordinateSectionEnergy f hf i)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
  let ν : Measure (Fin n → Observation (k + 1) (m + 1)) :=
    Measure.pi fun _ : Fin n => μ
  let fullν : Measure (DataCarrier k m n) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let ins := smoothCoordinateSectionInsertPair (k := k) (m := m) i
  have hMP : MeasurePreserving ins (μ.prod ν) fullν := by
    change MeasurePreserving
      (fun p => (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Observation (k + 1) (m + 1)) i).symm p)
      (μ.prod ν) fullν
    simpa [ν, fullν] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => μ) i).symm
  have hfullComp : Integrable
      (fun p => (datasetLocalSlope (smoothDatasetPullback f hf) (ins p)) ^ 2)
      (μ.prod ν) := by
    change Integrable
      ((fun D : DataCarrier k m n =>
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2) ∘ ins) (μ.prod ν)
    exact hMP.integrable_comp_of_integrable hfull
  refine hfullComp.mono' (continuous_smoothCoordinateSectionEnergy f hf i).aestronglyMeasurable ?_
  filter_upwards with p
  have hle := smoothCoordinateSection_slope_sq_le_full f hf i p.2 p.1
  simpa [smoothCoordinateSectionEnergy, smoothCoordinateSectionInsertPair,
    smoothCoordinateSectionInsert, ins, ν, Real.norm_eq_abs] using hle

/-- For a bounded smooth full-dataset test with integrable full squared slope,
the reviewed coordinate Poincaré theorem applies with every section-energy
admission discharged by the preceding transport theorem. -/
theorem integralVariance_smoothDatasetPullback_coordinatePoincare
    {k m n : ℕ} {μ : Measure (Observation (k + 1) (m + 1))}
    [IsProbabilityMeasure μ] {C B : ℝ}
    (hLSI : HasLogSobolev μ C)
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hbound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (hfull : Integrable
      (fun D : DataCarrier k m n =>
        (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    integralVariance (Measure.pi fun _ : Fin (n + 1) => μ)
        (smoothDatasetPullback f hf).1 ≤
      C * ∑ i : Fin (n + 1),
        ∫ tail : Fin n → Observation (k + 1) (m + 1),
          ∫ z, observationLocalSlope
            (coordinateSectionWitness (smoothDatasetPullback f hf) i tail) z ^ 2 ∂μ
            ∂Measure.pi (fun _ : Fin n => μ) := by
  have hFmeas : Measurable (smoothDatasetPullback f hf).1 := by
    change Measurable (fun D : DataCarrier k m n => f (datasetToEuclidean D))
    exact (hf.continuous.comp
      continuous_datasetToEuclidean_sections).measurable
  have hfiniteEnergy : ∀ i : Fin (n + 1),
      Integrable
        (fun p : Observation (k + 1) (m + 1) ×
            (Fin n → Observation (k + 1) (m + 1)) =>
          observationLocalSlope
            (coordinateSectionWitness (smoothDatasetPullback f hf) i p.2) p.1 ^ 2)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    intro i
    exact integrable_smoothCoordinateSectionEnergy_of_fullEnergy f hf hfull i
  exact integralVariance_piFin_coordinate_poincare hLSI
    (smoothDatasetPullback f hf) hFmeas hbound hfiniteEnergy

#print axioms smoothCoordinateSectionAffine_eq_insert
#print axioms fderiv_smoothCoordinateSectionAffine
#print axioms fderiv_smoothCoordinateSectionFunction
#print axioms observationLocalSlope_smoothCoordinateSection_eq
#print axioms sum_smoothCoordinateSection_slope_sq
#print axioms integrable_smoothCoordinateSectionEnergy_of_fullEnergy
#print axioms integralVariance_smoothDatasetPullback_coordinatePoincare

end LOOConcentration
