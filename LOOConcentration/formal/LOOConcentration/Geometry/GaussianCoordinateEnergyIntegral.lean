import LOOConcentration.Geometry.LipschitzCoordinateEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrated Gaussian coordinate energy

For a globally Lipschitz scalar function on finite Euclidean space, the actual
derivatives of its affine coordinate sections are square-integrable. Their
integrated squared sum is the integrated squared norm of the full derivative.
The same coordinate energies admit literal conditional Gaussian integral
formulas after splitting off one coordinate of a finite product.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

noncomputable section

namespace LOOConcentration

local instance (ι : Type*) [Fintype ι] : DecidableEq ι := Classical.decEq ι

/-- The actual derivative of the affine section in coordinate i, evaluated
at the coordinate of the base point. -/
noncomputable def euclideanCoordinateSectionDerivative
    {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (i : ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  deriv (euclideanCoordinateSection f x i) (x i)

/-- The global Lipschitz bound controls the full Fréchet derivative at every
point, including points where the function is not differentiable. -/
theorem norm_fderiv_le_of_lipschitz_euclidean
    {ι : Type*} [Fintype ι] {K : ℝ≥0}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f)
    (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ f x‖ ≤ (K : ℝ) := by
  exact norm_fderiv_le_of_lipschitz ℝ hf

/-- Each actual coordinate-section derivative is bounded everywhere by the
same global Lipschitz constant. -/
theorem norm_euclideanCoordinateSectionDerivative_le
    {ι : Type*} [Fintype ι] {K : ℝ≥0}
  (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f)
    (i : ι) (x : EuclideanSpace ℝ ι) :
    ‖euclideanCoordinateSectionDerivative f i x‖ ≤ (K : ℝ) := by
  exact norm_deriv_le_of_lipschitz
    (lipschitzWith_euclideanCoordinateSection f hf x i)

private theorem sq_le_sq_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  have hb : 0 ≤ b := le_trans ha hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg ha hb)]

private theorem sq_le_Ksq_of_norm_le {K : ℝ≥0} {x : ℝ} (hx : ‖x‖ ≤ (K : ℝ)) :
    x ^ 2 ≤ (K : ℝ) ^ 2 := by
  have hxabs : |x| ≤ (K : ℝ) := by simpa [Real.norm_eq_abs] using hx
  have hleft : 0 ≤ |x| := abs_nonneg x
  have hsquare := sq_le_sq_of_nonneg_le hleft hxabs
  simpa [sq_abs] using hsquare

/-- Almost everywhere, an actual coordinate-section derivative is the
evaluation of the actual Fréchet derivative on the corresponding Euclidean
basis vector. Its representative on the right is measurable on the whole
carrier by Mathlib's measurable derivative theorem. -/
theorem aestronglyMeasurable_euclideanCoordinateSectionDerivative
    {ι : Type*} [Fintype ι] [Nonempty ι] {K : ℝ≥0}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) (i : ι) :
    AEStronglyMeasurable
      (fun x => euclideanCoordinateSectionDerivative f i x)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
  let v : EuclideanSpace ℝ ι := EuclideanSpace.single i (1 : ℝ)
  have hmeas : Measurable (fun x : EuclideanSpace ℝ ι => fderiv ℝ f x v) := by
    exact measurable_fderiv_apply_const ℝ f v
  have hsm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => fderiv ℝ f x v)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := hmeas.aestronglyMeasurable
  have hdiff := standardGaussian_ae_differentiableAt_of_locallyLipschitz
    f hf.locallyLipschitz
  have hEq : (fun x => euclideanCoordinateSectionDerivative f i x) =ᵐ[
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hdiff] with x hx
    exact deriv_euclideanCoordinateSection_eq_fderiv f x i hx
  exact hsm.congr hEq.symm

/-- The actual squared coordinate-section derivative is integrable under the
canonical finite-dimensional Gaussian. This uses the AE derivative identity
for measurability and the pointwise Lipschitz derivative bound for finite
energy. -/
theorem integrable_euclideanCoordinateSectionDerivative_sq
    {ι : Type*} [Fintype ι] [Nonempty ι] (K : ℝ≥0)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) (i : ι) :
    Integrable
      (fun x => (euclideanCoordinateSectionDerivative f i x) ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
  let d := fun x : EuclideanSpace ℝ ι => euclideanCoordinateSectionDerivative f i x
  have hdsm : AEStronglyMeasurable d
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa [d] using aestronglyMeasurable_euclideanCoordinateSectionDerivative f hf i
  have hsqsm : AEStronglyMeasurable (fun x => d x ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    exact hdsm.pow 2
  have hbound : ∀ x, ‖d x ^ 2‖ ≤ (K : ℝ) ^ 2 := by
    intro x
    have hd := norm_euclideanCoordinateSectionDerivative_le f hf i x
    have hsq := sq_le_Ksq_of_norm_le hd
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (d x))]
    exact hsq
  apply Integrable.mono' (integrable_const ((K : ℝ) ^ 2)) hsqsm
  filter_upwards with x
  exact hbound x

/-- The squared norm of the total derivative is integrable under the
canonical Gaussian, with the global Lipschitz bound providing a finite
constant majorant. -/
theorem integrable_fderiv_norm_sq_of_lipschitz
    {ι : Type*} [Fintype ι] [Nonempty ι] (K : ℝ≥0)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
  have hsm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖fderiv ℝ f x‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    fun_prop
  have hbound : ∀ x : EuclideanSpace ℝ ι,
      ‖‖fderiv ℝ f x‖ ^ 2‖ ≤ (K : ℝ) ^ 2 := by
    intro x
    have hnorm := norm_fderiv_le_of_lipschitz_euclidean f hf x
    have hsq := sq_le_sq_of_nonneg_le (norm_nonneg _) hnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq
  apply Integrable.mono' (integrable_const ((K : ℝ) ^ 2)) hsm
  filter_upwards with x
  exact hbound x

/-- The integrated collective coordinate-energy identity for a globally
Lipschitz function. All summands and the total energy are integrable before
the finite sum is moved through the integral. -/
theorem integral_fderiv_norm_sq_eq_sum_integral_coordinateDerivative_sq
    {ι : Type*} [Fintype ι] [Nonempty ι] (K : ℝ≥0)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) :
    (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) =
      ∑ i : ι, ∫ x,
        (euclideanCoordinateSectionDerivative f i x) ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
  have hae := ae_standardGaussian_euclideanCoordinateEnergy K f hf
  calc
    (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) =
        ∫ x, ∑ i : ι, (euclideanCoordinateSectionDerivative f i x) ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
            apply integral_congr_ae
            filter_upwards [hae] with x hx
            exact hx.symm
    _ = ∑ i : ι, ∫ x,
          (euclideanCoordinateSectionDerivative f i x) ^ 2
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
          simpa only [Finset.sum_apply] using
            (integral_finsetSum (Finset.univ : Finset ι)
              (f := fun i x => (euclideanCoordinateSectionDerivative f i x) ^ 2)
              (by
                intro i hi
                exact integrable_euclideanCoordinateSectionDerivative_sq K f hf i))

/-- The joint family of actual affine-section derivatives is measurable. This
uses Mathlib's parameter derivative theorem on the continuous joint section
family; evaluation at the moving base coordinate is also measurable. -/
theorem measurable_euclideanCoordinateSectionDerivative
    {ι : Type*} [Fintype ι] {K : ℝ≥0}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) (i : ι) :
    Measurable (fun x => euclideanCoordinateSectionDerivative f i x) := by
  let sections : EuclideanSpace ℝ ι → ℝ → ℝ :=
    fun x t => euclideanCoordinateSection f x i t
  have hcoordinate : Continuous (fun x : EuclideanSpace ℝ ι => x i) :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : ι => ℝ) i
  have hpath : Continuous
      (fun p : EuclideanSpace ℝ ι × ℝ => euclideanCoordinatePath p.1 i p.2) := by
    change Continuous (fun p : EuclideanSpace ℝ ι × ℝ =>
      p.1 + (p.2 - p.1 i) • EuclideanSpace.single i (1 : ℝ))
    exact continuous_fst.add
      ((continuous_snd.sub (hcoordinate.comp continuous_fst)).smul continuous_const)
  have hjoint : Continuous (Function.uncurry sections) := by
    change Continuous (fun p : EuclideanSpace ℝ ι × ℝ =>
      f (euclideanCoordinatePath p.1 i p.2))
    exact hf.continuous.comp hpath
  have hderiv : Measurable (fun p : EuclideanSpace ℝ ι × ℝ =>
      deriv (euclideanCoordinateSection f p.1 i) p.2) := by
    exact measurable_deriv_with_param (f := sections) hjoint
  have heval : Measurable (fun x : EuclideanSpace ℝ ι => (x, x i)) :=
    measurable_id.prodMk hcoordinate.measurable
  convert hderiv.comp heval using 1
  · ext x
    rfl

/-- The square of the frozen Observation(1,1) local slope is genuinely
integrable under its actual Gaussian law. Measurability is obtained by the
accepted AE slope/coordinate identity, and integrability is then transferred
from the coordinate energies. -/
theorem integrable_gaussianObservation_localSlope_sq
    (K : ℝ≥0)
    (f : EuclideanSpace ℝ (ObservationCoordinate 1 1) → ℝ)
    (hf : LipschitzWith K f) :
    Integrable
      (fun z => (observationLocalSlope
        (locallyLipschitzObservationPullback f hf.locallyLipschitz) z) ^ 2)
      gaussianObservationLaw := by
  let E := EuclideanSpace ℝ (ObservationCoordinate 1 1)
  let γ := ProbabilityTheory.stdGaussian E
  let obs : Observation 1 1 → E := observationToEuclidean
  let μ := gaussianObservationLaw
  let energy : Observation 1 1 → ℝ := fun z =>
    ∑ i : ObservationCoordinate 1 1,
      (euclideanCoordinateSectionDerivative f i (obs z)) ^ 2
  have hcoord : ∀ i : ObservationCoordinate 1 1,
      Integrable (fun z : Observation 1 1 =>
        (euclideanCoordinateSectionDerivative f i (obs z)) ^ 2) μ := by
    intro i
    have hstd := integrable_euclideanCoordinateSectionDerivative_sq K f hf i
    have hmap : μ.map obs = γ := by
      simpa [E, γ, μ, obs] using gaussianObservationLaw_map_observationToEuclidean
    have hMapped : Integrable
        (fun x : E => (euclideanCoordinateSectionDerivative f i x) ^ 2)
        (μ.map obs) := by
      simpa [hmap, E, γ] using hstd
    exact (integrable_map_measure hMapped.aestronglyMeasurable
      (observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable)).mp
        hMapped
  have henergy : Integrable energy μ := by
    have hs := integrable_finsetSum (Finset.univ : Finset (ObservationCoordinate 1 1))
      (f := fun i z =>
        (euclideanCoordinateSectionDerivative f i (obs z)) ^ 2)
      (by
        intro i hi
        exact hcoord i)
    simpa only [Finset.sum_apply, energy, obs, μ] using hs
  have hae := ae_gaussianObservationLaw_observationLocalSlope_sq_eq_coordinateEnergy K f hf
  have henergyEq : (fun z : Observation 1 1 =>
      (observationLocalSlope
        (locallyLipschitzObservationPullback f hf.locallyLipschitz) z) ^ 2) =ᵐ[μ]
      energy := by
    filter_upwards [hae] with z hz
    simpa [energy, E, obs, μ, euclideanCoordinateSectionDerivative] using hz
  exact henergy.congr henergyEq.symm

/-- The actual frozen Observation(1,1) slope energy equals the sum of the
integrated actual coordinate-section energies. -/
theorem integral_gaussianObservation_localSlope_sq_eq_sum_coordinateDerivative_sq
    (K : ℝ≥0)
    (f : EuclideanSpace ℝ (ObservationCoordinate 1 1) → ℝ)
    (hf : LipschitzWith K f) :
    (∫ z, (observationLocalSlope
      (locallyLipschitzObservationPullback f hf.locallyLipschitz) z) ^ 2
        ∂gaussianObservationLaw) =
      ∑ i : ObservationCoordinate 1 1, ∫ z,
        (euclideanCoordinateSectionDerivative f i (observationToEuclidean z)) ^ 2
          ∂gaussianObservationLaw := by
  have hae := ae_gaussianObservationLaw_observationLocalSlope_sq_eq_coordinateEnergy K f hf
  calc
    (∫ z, (observationLocalSlope
      (locallyLipschitzObservationPullback f hf.locallyLipschitz) z) ^ 2
        ∂gaussianObservationLaw) =
      ∫ z, ∑ i : ObservationCoordinate 1 1,
        (euclideanCoordinateSectionDerivative f i (observationToEuclidean z)) ^ 2
          ∂gaussianObservationLaw := by
            apply integral_congr_ae
            filter_upwards [hae] with z hz
            simpa [euclideanCoordinateSectionDerivative] using hz
    _ = ∑ i : ObservationCoordinate 1 1, ∫ z,
        (euclideanCoordinateSectionDerivative f i (observationToEuclidean z)) ^ 2
          ∂gaussianObservationLaw := by
          simpa only [Finset.sum_apply] using
            (integral_finsetSum (Finset.univ : Finset (ObservationCoordinate 1 1))
              (f := fun i z =>
                (euclideanCoordinateSectionDerivative f i (observationToEuclidean z)) ^ 2)
              (by
                intro i hi
                have hstd := integrable_euclideanCoordinateSectionDerivative_sq K f hf i
                have hmap : gaussianObservationLaw.map observationToEuclidean =
                    ProbabilityTheory.stdGaussian
                      (EuclideanSpace ℝ (ObservationCoordinate 1 1)) :=
                  gaussianObservationLaw_map_observationToEuclidean
                have hMapped : Integrable
                    (fun x : EuclideanSpace ℝ (ObservationCoordinate 1 1) =>
                      (euclideanCoordinateSectionDerivative f i x) ^ 2)
                    (gaussianObservationLaw.map observationToEuclidean) := by
                  simpa [hmap] using hstd
                exact (integrable_map_measure hMapped.aestronglyMeasurable
                  observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable).mp
                  hMapped))

/-- The actual insertion map used to condition on one coordinate of a finite
Gaussian product. The inverse piFinSuccAbove equivalence inserts the real
coordinate and restores the remaining coordinates in their original order. -/
noncomputable def gaussianPiInsertCoordinate {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) (tail : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (t, tail)

/-- Every actual coordinate-section derivative square remains integrable on
the literal independent Gaussian Pi carrier. -/
theorem integrable_euclideanCoordinateSectionDerivative_sq_pi
    {n : ℕ} (K : ℝ≥0)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : LipschitzWith K f)
    (i : Fin (n + 1)) :
    Integrable
      (fun y : Fin (n + 1) → ℝ =>
        (euclideanCoordinateSectionDerivative f i
          (WithLp.toLp (2 : ENNReal) y)) ^ 2)
      (standardGaussianPiLaw (Fin (n + 1))) := by
  have hstd := integrable_euclideanCoordinateSectionDerivative_sq K f hf i
  have hmap : (standardGaussianPiLaw (Fin (n + 1))).map
      (WithLp.toLp (2 : ENNReal) : (Fin (n + 1) → ℝ) →
        EuclideanSpace ℝ (Fin (n + 1))) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [standardGaussianPiLaw] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (n + 1)))
  have hMapped : Integrable
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
        (euclideanCoordinateSectionDerivative f i x) ^ 2)
      ((standardGaussianPiLaw (Fin (n + 1))).map
        (WithLp.toLp (2 : ENNReal))) := by
    simpa [hmap] using hstd
  exact (integrable_map_measure hMapped.aestronglyMeasurable
    (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin (n + 1) => ℝ)).measurable.aemeasurable).mp hMapped

/-- Integrating over the independent Gaussian Pi law is the same as
integrating the corresponding Euclidean energy under the canonical Gaussian. -/
theorem integral_euclideanCoordinateSectionDerivative_sq_pi_eq_stdGaussian
    {n : ℕ} (K : ℝ≥0)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : LipschitzWith K f)
    (i : Fin (n + 1)) :
    (∫ y : Fin (n + 1) → ℝ,
      (euclideanCoordinateSectionDerivative f i
        (WithLp.toLp (2 : ENNReal) y)) ^ 2
        ∂standardGaussianPiLaw (Fin (n + 1))) =
      ∫ x, (euclideanCoordinateSectionDerivative f i x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  have hstd := integrable_euclideanCoordinateSectionDerivative_sq K f hf i
  have hmap : (standardGaussianPiLaw (Fin (n + 1))).map
      (WithLp.toLp (2 : ENNReal) : (Fin (n + 1) → ℝ) →
        EuclideanSpace ℝ (Fin (n + 1))) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [standardGaussianPiLaw] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (n + 1)))
  calc
    _ = ∫ x, (euclideanCoordinateSectionDerivative f i x) ^ 2
        ∂(standardGaussianPiLaw (Fin (n + 1))).map
          (WithLp.toLp (2 : ENNReal)) := by
            symm
            exact integral_map
              (PiLp.continuous_toLp (p := (2 : ENNReal))
                (β := fun _ : Fin (n + 1) => ℝ)).measurable.aemeasurable
              (by simpa [hmap] using hstd.aestronglyMeasurable)
    _ = ∫ x, (euclideanCoordinateSectionDerivative f i x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by rw [hmap]

/-- The conditional-coordinate integral under the literal independent
Gaussian Pi law equals the integrated actual affine-section derivative
energy. The conditioned function is evaluated at the point reconstructed by
the measure-preserving piFinSuccAbove insertion, and its derivative is taken
at the real conditioning coordinate itself. -/
theorem integral_gaussianConditionalCoordinateSectionDerivative_sq_eq_stdGaussian
    {n : ℕ} (K : ℝ≥0)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : LipschitzWith K f)
    (i : Fin (n + 1)) :
    (∫ tail : Fin n → ℝ, ∫ t : ℝ,
      (deriv (euclideanCoordinateSection f
        (WithLp.toLp (2 : ENNReal) (gaussianPiInsertCoordinate i t tail)) i) t) ^ 2
        ∂ProbabilityTheory.gaussianReal 0 1
        ∂standardGaussianPiLaw (Fin n)) =
      ∫ x, (euclideanCoordinateSectionDerivative f i x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let μ := standardGaussianPiLaw (Fin (n + 1))
  let ν := standardGaussianPiLaw (Fin n)
  let γ := ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)
  have : IsProbabilityMeasure ν := by
    dsimp [ν, standardGaussianPiLaw]
    infer_instance
  have : IsProbabilityMeasure γ := by
    dsimp [γ]
    infer_instance
  let g : ℝ × (Fin n → ℝ) → ℝ := fun p =>
    (deriv (euclideanCoordinateSection f
      (WithLp.toLp (2 : ENNReal) (e.symm p)) i) p.1) ^ 2
  have hMP : MeasurePreserving e μ (γ.prod ν) := by
    simpa [e, μ, ν, γ, standardGaussianPiLaw] using
      (measurePreserving_piFinSuccAbove
        (μ := fun _ : Fin (n + 1) =>
          ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) i)
  have hraw := integrable_euclideanCoordinateSectionDerivative_sq_pi K f hf i
  have hcomp : (fun y : Fin (n + 1) → ℝ => g (e y)) =
      (fun y => (euclideanCoordinateSectionDerivative f i
        (WithLp.toLp (2 : ENNReal) y)) ^ 2) := by
    funext y
    have hcoord : (e y).1 = y i := by
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    change (deriv (euclideanCoordinateSection f
      (WithLp.toLp (2 : ENNReal) (e.symm (e y))) i) (e y).1) ^ 2 =
      (deriv (euclideanCoordinateSection f
        (WithLp.toLp (2 : ENNReal) y) i)
        ((WithLp.toLp (2 : ENNReal) y) i)) ^ 2
    rw [e.symm_apply_apply, hcoord]
  have htarget : Integrable g (γ.prod ν) := by
    have hcompInt : Integrable (fun y : Fin (n + 1) → ℝ => g (e y)) μ := by
      simpa [hcomp] using hraw
    exact (hMP.integrable_comp_emb e.measurableEmbedding).mp hcompInt
  calc
    _ = ∫ p, g p ∂γ.prod ν := by
      symm
      exact integral_prod_symm g htarget
    _ = ∫ y : Fin (n + 1) → ℝ, g (e y) ∂μ := by
      symm
      exact hMP.integral_comp' g
    _ = ∫ y : Fin (n + 1) → ℝ,
        (euclideanCoordinateSectionDerivative f i
          (WithLp.toLp (2 : ENNReal) y)) ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with y
          exact congrFun hcomp y
    _ = ∫ x, (euclideanCoordinateSectionDerivative f i x) ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) :=
          integral_euclideanCoordinateSectionDerivative_sq_pi_eq_stdGaussian K f hf i

/-- Summing the true conditional-coordinate energies gives the integrated
collective Gaussian gradient energy, with coefficient one. -/
theorem sum_integral_gaussianConditionalCoordinateSectionDerivative_sq_eq_integral_fderiv_norm_sq
    {n : ℕ} (K : ℝ≥0)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : LipschitzWith K f) :
    ∑ i : Fin (n + 1),
      ∫ tail : Fin n → ℝ, ∫ t : ℝ,
        (deriv (euclideanCoordinateSection f
          (WithLp.toLp (2 : ENNReal) (gaussianPiInsertCoordinate i t tail)) i) t) ^ 2
          ∂ProbabilityTheory.gaussianReal 0 1
          ∂standardGaussianPiLaw (Fin n) =
    ∫ x, ‖fderiv ℝ f x‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  calc
    _ = ∑ i : Fin (n + 1), ∫ x,
        (euclideanCoordinateSectionDerivative f i x) ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact integral_gaussianConditionalCoordinateSectionDerivative_sq_eq_stdGaussian
            K f hf i
    _ = ∫ x, ‖fderiv ℝ f x‖ ^ 2
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
          exact (integral_fderiv_norm_sq_eq_sum_integral_coordinateDerivative_sq
            K f hf).symm

#print axioms integrable_euclideanCoordinateSectionDerivative_sq
#print axioms norm_fderiv_le_of_lipschitz_euclidean
#print axioms norm_euclideanCoordinateSectionDerivative_le
#print axioms aestronglyMeasurable_euclideanCoordinateSectionDerivative
#print axioms measurable_euclideanCoordinateSectionDerivative
#print axioms integrable_fderiv_norm_sq_of_lipschitz
#print axioms integral_fderiv_norm_sq_eq_sum_integral_coordinateDerivative_sq
#print axioms integrable_gaussianObservation_localSlope_sq
#print axioms integral_gaussianObservation_localSlope_sq_eq_sum_coordinateDerivative_sq
#print axioms integral_gaussianConditionalCoordinateSectionDerivative_sq_eq_stdGaussian
#print axioms sum_integral_gaussianConditionalCoordinateSectionDerivative_sq_eq_integral_fderiv_norm_sq

end LOOConcentration

end
