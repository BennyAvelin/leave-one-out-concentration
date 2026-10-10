import LOOConcentration.Geometry.SmoothObservationSlope
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic

/-!
# Differentiability of locally Lipschitz Euclidean functions

This module supplies the local Rademacher step for the Gaussian finite-energy
extension route. It uses actual local Lipschitz neighborhoods, obtains a
countable open subcover, and upgrades within-set differentiability on each
open neighborhood. It also records the pointwise local-slope identity for an
observation-coordinate pullback at every point where the Euclidean function
is differentiable.
-/

set_option autoImplicit false

open Filter MeasureTheory
open Asymptotics
open scoped Topology

namespace LOOConcentration

/-- A locally Lipschitz function on a positive-dimensional finite Euclidean
space is differentiable almost everywhere for volume. The proof applies
Rademacher on a countable open cover of actual local Lipschitz neighborhoods.
-/
theorem locallyLipschitz_ae_differentiableAt_euclidean
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), DifferentiableAt ℝ f x := by
  classical
  let E := EuclideanSpace ℝ ι
  choose K U hU hLip using hf
  let V : E → Set E := fun x => interior (U x)
  have hVopen (x : E) : IsOpen (V x) := isOpen_interior
  have hxV (x : E) : x ∈ V x := mem_interior_iff_mem_nhds.mpr (hU x)
  have hVLip (x : E) : LipschitzOnWith (K x) f (V x) :=
    (hLip x).mono interior_subset
  obtain ⟨e, hecover⟩ :=
    (isLindelof_univ : IsLindelof (Set.univ : Set E)).indexed_countable_subcover
      V hVopen (by
        intro x hx
        exact Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hlocal (n : ℕ) :
      ∀ᵐ x ∂(volume : Measure E), x ∈ V (e n) → DifferentiableAt ℝ f x := by
    have hrademacher :
        ∀ᵐ x ∂(volume : Measure E),
          x ∈ V (e n) → DifferentiableWithinAt ℝ f (V (e n)) x := by
      exact (hVLip (e n)).ae_differentiableWithinAt_of_mem (μ := volume)
    filter_upwards [hrademacher] with x hx
    intro hxVn
    exact (hx hxVn).differentiableAt ((hVopen (e n)).mem_nhds hxVn)
  have hall :
      ∀ᵐ x ∂(volume : Measure E),
        ∀ n, x ∈ V (e n) → DifferentiableAt ℝ f x :=
    ae_all_iff.2 hlocal
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hecover (Set.mem_univ x))
  exact hx n hn

/-- Absolute continuity transfers the volume-a.e. Rademacher conclusion to
any measure dominated by volume. -/
theorem locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure (EuclideanSpace ℝ ι)}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LocallyLipschitz f)
    (hμ : μ ≪ (volume : Measure (EuclideanSpace ℝ ι))) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
  hμ.ae_le (locallyLipschitz_ae_differentiableAt_euclidean f hf)

/-- Compose a locally Lipschitz Euclidean function with the reviewed
continuous linear observation-coordinate equivalence, retaining the actual
frozen local-Lipschitz witness. -/
noncomputable def locallyLipschitzObservationPullback {k m : ℕ}
    (f : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hf : LocallyLipschitz f) :
    {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)} := by
  let T : Observation (k + 1) (m + 1) →
      EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) :=
    observationToEuclidean
  refine ⟨fun z => f (T z), ?_⟩
  intro z
  obtain ⟨K, U, hU, hLip⟩ := hf (T z)
  refine ⟨T ⁻¹' U,
    observationCoordinateContinuousLinearEquiv.continuous.continuousAt.preimage_mem_nhds hU,
    K, K.coe_nonneg, ?_⟩
  intro w hw v hv
  have hdist := hLip.dist_le_mul (T w) hw (T v) hv
  calc
    |f (T w) - f (T v)| = dist (f (T w)) (f (T v)) := (Real.dist_eq _ _).symm
    _ ≤ (K : ℝ) * dist (T w) (T v) := hdist
    _ = (K : ℝ) * observationNorm (w - v) := by
      rw [dist_eq_norm, ← observationNorm_sub_eq_euclidean]

private theorem observationNorm_fromEuclidean_sub_wave12 {k m : ℕ}
    (z : Observation (k + 1) (m + 1))
    (y : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1))) :
    observationNorm (observationFromEuclidean y - z) =
      ‖y - observationToEuclidean z‖ := by
  rw [observationNorm_eq_euclidean, observationToEuclidean_sub,
    observationToEuclidean_fromEuclidean]

/-- At every Euclidean differentiability point, the frozen observation
punctured local slope of a locally Lipschitz coordinate pullback is exactly
the norm of the Euclidean Fréchet derivative. Only pointwise differentiability
is used; no `C¹` hypothesis is required. -/
theorem observationLocalSlope_locallyLipschitzPullback_eq
    {k m : ℕ}
    (f : EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hlocal : LocallyLipschitz f)
    (z : Observation (k + 1) (m + 1))
    (hdiff : DifferentiableAt ℝ f (observationToEuclidean z)) :
    observationLocalSlope (locallyLipschitzObservationPullback f hlocal) z =
      ‖fderiv ℝ f (observationToEuclidean z)‖ := by
  let _ : PerfectSpace (Observation (k + 1) (m + 1)) := perfectSpace_of_module ℝ _
  let x := observationToEuclidean z
  let G := locallyLipschitzObservationPullback f hlocal
  let q : Observation (k + 1) (m + 1) → ℝ := fun w =>
    |f (observationToEuclidean w) - f x| / observationNorm (w - z)
  change limsup q (𝓝[≠] z) = ‖fderiv ℝ f x‖
  have hbounded : (𝓝[≠] z).IsBoundedUnder (· ≤ ·) q := by
    simpa [q, x, G, locallyLipschitzObservationPullback] using
      observationSlope_bounded G z
  have hnonneg : ∃ᶠ w in 𝓝[≠] z, 0 ≤ q w := by
    apply Filter.Frequently.of_forall
    intro w
    exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hCobounded : (𝓝[≠] z).IsCoboundedUnder (· ≤ ·) q := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    exact hnonneg
  have hupper : limsup q (𝓝[≠] z) ≤ ‖fderiv ℝ f x‖ := by
    apply (Filter.limsup_le_iff' hCobounded hbounded).2
    intro c hc
    have hgap : 0 < c - ‖fderiv ℝ f x‖ := sub_pos.mpr hc
    let ε : ℝ := (c - ‖fderiv ℝ f x‖) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hsmall := (isLittleO_iff.1 hdiff.hasFDerivAt.isLittleO) hε
    have hTcontinuous :
        Continuous (observationToEuclidean : Observation (k + 1) (m + 1) →
          EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1))) :=
      observationCoordinateContinuousLinearEquiv.continuous
    have hsmallObs : ∀ᶠ w in 𝓝 z,
        ‖f (observationToEuclidean w) - f x -
          fderiv ℝ f x (observationToEuclidean w - x)‖ ≤
          ε * ‖observationToEuclidean w - x‖ := by
      simpa [x] using hTcontinuous.continuousAt.eventually hsmall
    have hquot : ∀ᶠ w in 𝓝[≠] z, q w ≤ ‖fderiv ℝ f x‖ + ε := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hsmallObs,
        self_mem_nhdsWithin] with w hw hneWithin
      have hne : w ≠ z := by simpa using hneWithin
      have hnormPos : 0 < observationNorm (w - z) := observationNorm_sub_pos hne
      have hnormEq : ‖observationToEuclidean w - x‖ =
          observationNorm (w - z) := by
        simpa [x] using (observationNorm_sub_eq_euclidean w z).symm
      have hnum : |f (observationToEuclidean w) - f x| ≤
          (‖fderiv ℝ f x‖ + ε) * observationNorm (w - z) := by
        calc
          |f (observationToEuclidean w) - f x| =
              ‖f (observationToEuclidean w) - f x‖ := (Real.norm_eq_abs _).symm
          _ = ‖fderiv ℝ f x (observationToEuclidean w - x) +
                (f (observationToEuclidean w) - f x -
                  fderiv ℝ f x (observationToEuclidean w - x))‖ := by
            congr 1
            ring
          _ ≤ ‖fderiv ℝ f x (observationToEuclidean w - x)‖ +
                ‖f (observationToEuclidean w) - f x -
                  fderiv ℝ f x (observationToEuclidean w - x)‖ := norm_add_le _ _
          _ ≤ ‖fderiv ℝ f x‖ * ‖observationToEuclidean w - x‖ +
                ε * ‖observationToEuclidean w - x‖ := by
            exact add_le_add
              ((fderiv ℝ f x).le_opNorm (observationToEuclidean w - x)) hw
          _ = (‖fderiv ℝ f x‖ + ε) * observationNorm (w - z) := by
            rw [hnormEq]
            ring
      exact (div_le_iff₀ hnormPos).2 hnum
    filter_upwards [hquot] with w hw
    exact hw.trans (by dsimp [ε]; linarith)
  have hlower : ‖fderiv ℝ f x‖ ≤ limsup q (𝓝[≠] z) := by
    let L : ℝ := limsup q (𝓝[≠] z)
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact le_limsup_of_frequently_le hnonneg hbounded
    by_contra hnot
    have hgap : 0 < ‖fderiv ℝ f x‖ - L :=
      sub_pos.mpr (lt_of_not_ge hnot)
    let ε : ℝ := (‖fderiv ℝ f x‖ - L) / 2
    let C : ℝ := L + ε
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hC : 0 ≤ C := by dsimp [C]; linarith
    have hEv : ∀ᶠ w in 𝓝[≠] z, q w < C := by
      have hlim : limsup q (𝓝[≠] z) ≤ L := by rfl
      exact (Filter.limsup_le_iff hCobounded hbounded).mp hlim C (by
        dsimp [C]
        linarith)
    have hLipAtObservation : ∀ᶠ w in 𝓝 z,
        |f (observationToEuclidean w) - f x| ≤ C * observationNorm (w - z) := by
      have hpunct := (eventually_nhdsWithin_iff.mp hEv)
      filter_upwards [hpunct] with w hw
      by_cases hwz : w = z
      · subst w
        have hzero : f (observationToEuclidean z) - f x = 0 := by simp [x]
        rw [hzero, abs_zero]
        exact mul_nonneg hC (Real.sqrt_nonneg _)
      · have hnorm : 0 < observationNorm (w - z) := observationNorm_sub_pos hwz
        exact (div_lt_iff₀ hnorm).mp (hw hwz) |>.le
    have hLipAtEuclidean : ∀ᶠ y in 𝓝 x,
        ‖f y - f x‖ ≤ C * ‖y - x‖ := by
      have hFromContinuous :
          Continuous (observationFromEuclidean :
            EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) →
              Observation (k + 1) (m + 1)) :=
        observationCoordinateContinuousLinearEquiv.symm.continuous
      have hcomp :=
        (hFromContinuous.continuousAt (x := x)).eventually hLipAtObservation
      filter_upwards [hcomp] with y hy
      rw [observationToEuclidean_fromEuclidean] at hy
      have hnorm : observationNorm (observationFromEuclidean y - z) = ‖y - x‖ := by
        simpa [x] using observationNorm_fromEuclidean_sub_wave12 z y
      simpa [Real.norm_eq_abs, hnorm] using hy
    have hderiv : ‖fderiv ℝ f x‖ ≤ C :=
      norm_fderiv_le_of_lip' ℝ hC hLipAtEuclidean
    dsimp [C, ε] at hderiv
    linarith
  exact le_antisymm hupper hlower

#print axioms locallyLipschitz_ae_differentiableAt_euclidean
#print axioms locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
#print axioms locallyLipschitzObservationPullback
#print axioms observationLocalSlope_locallyLipschitzPullback_eq

end LOOConcentration
