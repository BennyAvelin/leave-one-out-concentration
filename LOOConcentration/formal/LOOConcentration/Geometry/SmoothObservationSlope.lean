import LOOConcentration.Frozen.Slopes.ObservationLocalSlope
import LOOConcentration.Geometry.EuclideanNormFacts
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentration.Geometry.NormTransport
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-!
# Smooth local slope in frozen observation coordinates

The coordinate flattening map is a continuous linear equivalence, and the
frozen observation norm is its Euclidean norm. This identifies the frozen
punctured local slope of a smooth pullback with the norm of its Euclidean
Fréchet derivative.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

/-- Reconstruct an observation from its flattened Euclidean coordinates. -/
def observationFromEuclidean {k m : ℕ}
    (x : EuclideanSpace ℝ (ObservationCoordinate k m)) : Observation k m :=
  (fun i => x (Sum.inl i), fun j => x (Sum.inr j))

@[simp] theorem observationToEuclidean_fromEuclidean {k m : ℕ}
    (x : EuclideanSpace ℝ (ObservationCoordinate k m)) :
    observationToEuclidean (observationFromEuclidean x) = x := by
  apply PiLp.ext
  intro q
  cases q <;> rfl

@[simp] theorem observationFromEuclidean_toEuclidean {k m : ℕ}
    (z : Observation k m) :
    observationFromEuclidean (observationToEuclidean z) = z := by
  apply Prod.ext <;> funext i <;> rfl

theorem observationToEuclidean_sub {k m : ℕ}
    (z w : Observation k m) :
    observationToEuclidean (z - w) = observationToEuclidean z - observationToEuclidean w := by
  apply PiLp.ext
  intro q
  cases q <;> simp [observationToEuclidean]

private theorem continuous_observationToEuclidean_smooth {k m : ℕ} :
    Continuous (observationToEuclidean : Observation k m →
      EuclideanSpace ℝ (ObservationCoordinate k m)) := by
  change Continuous (fun z : Observation k m =>
    WithLp.toLp (2 : ENNReal) (fun q : ObservationCoordinate k m =>
      Sum.elim z.1 z.2 q))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : ObservationCoordinate k m => ℝ)).comp (by
    apply continuous_pi
    intro q
    cases q with
    | inl i => exact (continuous_apply i).comp continuous_fst
    | inr j => exact (continuous_apply j).comp continuous_snd)

private theorem continuous_observationFromEuclidean_smooth {k m : ℕ} :
    Continuous (observationFromEuclidean : EuclideanSpace ℝ
      (ObservationCoordinate k m) → Observation k m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : ObservationCoordinate k m => ℝ) (Sum.inl i)
  · apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : ObservationCoordinate k m => ℝ) (Sum.inr j)

/-- The coordinate flattening is a genuine continuous linear equivalence.
It does not assert that the raw inherited product norm is the source norm. -/
def observationCoordinateContinuousLinearEquiv {k m : ℕ} :
    Observation k m ≃L[ℝ] EuclideanSpace ℝ (ObservationCoordinate k m) where
  toFun := observationToEuclidean
  map_add' := observationToEuclidean_add
  map_smul' := by
    intro c z
    apply PiLp.ext
    intro q
    cases q <;> simp [observationToEuclidean]
  invFun := observationFromEuclidean
  left_inv := observationFromEuclidean_toEuclidean
  right_inv := observationToEuclidean_fromEuclidean
  continuous_toFun := continuous_observationToEuclidean_smooth
  continuous_invFun := continuous_observationFromEuclidean_smooth

/-- Frozen-norm subtraction is exactly Euclidean distance after flattening. -/
theorem observationNorm_sub_eq_euclidean {k m : ℕ}
    (z w : Observation k m) :
    observationNorm (z - w) =
      ‖observationToEuclidean z - observationToEuclidean w‖ := by
  rw [observationNorm_eq_euclidean, observationToEuclidean_sub]

private theorem observationNorm_fromEuclidean_sub {k m : ℕ}
    (z : Observation k m)
    (y : EuclideanSpace ℝ (ObservationCoordinate k m)) :
    observationNorm (observationFromEuclidean y - z) =
      ‖y - observationToEuclidean z‖ := by
  rw [observationNorm_eq_euclidean, observationToEuclidean_sub,
    observationToEuclidean_fromEuclidean]

/-- Pull a `C¹` scalar function on flattened Euclidean observation space back
to the frozen observation carrier with its genuine frozen local-Lipschitz
witness. -/
noncomputable def smoothObservationPullback {k m : ℕ}
    (f : EuclideanSpace ℝ
      (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)} := by
  let T : Observation (k + 1) (m + 1) →
      EuclideanSpace ℝ (ObservationCoordinate (k + 1) (m + 1)) :=
    observationToEuclidean
  have hT : Continuous T := continuous_observationToEuclidean_smooth
  refine ⟨fun z => f (T z), ?_⟩
  intro z
  obtain ⟨K, U, hU, hLip⟩ := hf.locallyLipschitz (T z)
  refine ⟨T ⁻¹' U, hT.continuousAt.preimage_mem_nhds hU,
    K, K.coe_nonneg, ?_⟩
  intro w hw v hv
  have hdist := hLip.dist_le_mul (T w) hw (T v) hv
  calc
    |f (T w) - f (T v)| = dist (f (T w)) (f (T v)) := (Real.dist_eq _ _).symm
    _ ≤ (K : ℝ) * dist (T w) (T v) := hdist
    _ = (K : ℝ) * observationNorm (w - v) := by
      rw [dist_eq_norm, ← observationNorm_sub_eq_euclidean]

/-- The frozen punctured local slope of a smooth observation pullback is the
operator norm of the Euclidean Fréchet derivative at the flattened point. -/
theorem observationLocalSlope_smoothPullback_eq {k m : ℕ}
    (f : EuclideanSpace ℝ
      (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (z : Observation (k + 1) (m + 1)) :
    observationLocalSlope (smoothObservationPullback f hf) z =
      ‖fderiv ℝ f (observationToEuclidean z)‖ := by
  let _ : PerfectSpace (Observation (k + 1) (m + 1)) := perfectSpace_of_module ℝ _
  let x := observationToEuclidean z
  let q : Observation (k + 1) (m + 1) → ℝ := fun w =>
    |f (observationToEuclidean w) - f x| / observationNorm (w - z)
  change limsup q (𝓝[≠] z) = ‖fderiv ℝ f x‖
  have hbounded : (𝓝[≠] z).IsBoundedUnder (· ≤ ·) q := by
    simpa [q, x, smoothObservationPullback] using
      observationSlope_bounded (smoothObservationPullback f hf) z
  have hnonneg : ∃ᶠ w in 𝓝[≠] z, 0 ≤ q w := by
    apply Filter.Frequently.of_forall
    intro w
    exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hCobounded : (𝓝[≠] z).IsCoboundedUnder (· ≤ ·) q := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    exact hnonneg
  have hupper : limsup q (𝓝[≠] z) ≤ ‖fderiv ℝ f x‖ := by
    apply (Filter.limsup_le_iff' hCobounded hbounded).2
    intro (c : ℝ) hc
    have hc0 : (0 : ℝ) ≤ c :=
      le_trans (norm_nonneg (fderiv ℝ f x)) hc.le
    let K : NNReal := Real.toNNReal c
    have hK : ‖fderiv ℝ f x‖₊ < K := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal c hc0]
      exact hc
    obtain ⟨U, hU, hLip⟩ :=
      hf.contDiffAt.exists_lipschitzOnWith_of_nnnorm_lt K hK
    have hTpre : observationToEuclidean ⁻¹' U ∈ 𝓝 z :=
      continuous_observationToEuclidean_smooth.continuousAt.preimage_mem_nhds hU
    have hquot : ∀ᶠ w in 𝓝[≠] z, q w ≤ c := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hTpre,
        self_mem_nhdsWithin] with w hw hneWithin
      have hne : w ≠ z := by simpa using hneWithin
      have hxU : x ∈ U := mem_of_mem_nhds hU
      have hdist := hLip.dist_le_mul (observationToEuclidean w) hw x hxU
      have hnorm : 0 < observationNorm (w - z) := observationNorm_sub_pos hne
      have hdistEq : dist (observationToEuclidean w) x =
          observationNorm (w - z) := by
        calc
          dist (observationToEuclidean w) x =
              ‖observationToEuclidean w - observationToEuclidean z‖ := by
                simp [x, dist_eq_norm]
          _ = observationNorm (w - z) :=
            (observationNorm_sub_eq_euclidean w z).symm
      have hnum : |f (observationToEuclidean w) - f x| ≤
          c * observationNorm (w - z) := by
        rw [Real.dist_eq, hdistEq] at hdist
        simpa [K, Real.coe_toNNReal c hc0] using hdist
      exact (div_le_iff₀ hnorm).2 hnum
    exact hquot
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
      have hcomp :=
        (continuous_observationFromEuclidean_smooth.continuousAt (x := x)).eventually
          hLipAtObservation
      filter_upwards [hcomp] with y hy
      simpa [x, observationNorm_fromEuclidean_sub] using hy
    have hderiv : ‖fderiv ℝ f x‖ ≤ C :=
      norm_fderiv_le_of_lip' ℝ hC hLipAtEuclidean
    dsimp [C, ε] at hderiv
    linarith
  exact le_antisymm hupper hlower

/-- The squared frozen local slope of a smooth observation pullback is
continuous on the exact source carrier. -/
theorem continuous_observationLocalSlope_sq_smoothPullback {k m : ℕ}
    (f : EuclideanSpace ℝ
      (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : Observation (k + 1) (m + 1) =>
      (observationLocalSlope (smoothObservationPullback f hf) z) ^ 2) := by
  have hderiv : Continuous (fun z : Observation (k + 1) (m + 1) =>
      fderiv ℝ f (observationToEuclidean z)) :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_observationToEuclidean_smooth
  have hnorm : Continuous (fun z : Observation (k + 1) (m + 1) =>
      ‖fderiv ℝ f (observationToEuclidean z)‖ ^ 2) :=
    (continuous_norm.comp hderiv).pow 2
  have heq : (fun z : Observation (k + 1) (m + 1) =>
      (observationLocalSlope (smoothObservationPullback f hf) z) ^ 2) =
      fun z => ‖fderiv ℝ f (observationToEuclidean z)‖ ^ 2 := by
    funext z
    rw [observationLocalSlope_smoothPullback_eq]
  rw [heq]
  exact hnorm

theorem measurable_observationLocalSlope_sq_smoothPullback {k m : ℕ}
    (f : EuclideanSpace ℝ
      (ObservationCoordinate (k + 1) (m + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Measurable (fun z : Observation (k + 1) (m + 1) =>
      (observationLocalSlope (smoothObservationPullback f hf) z) ^ 2) :=
  (continuous_observationLocalSlope_sq_smoothPullback f hf).measurable

#print axioms observationCoordinateContinuousLinearEquiv
#print axioms smoothObservationPullback
#print axioms observationLocalSlope_smoothPullback_eq
#print axioms continuous_observationLocalSlope_sq_smoothPullback
#print axioms measurable_observationLocalSlope_sq_smoothPullback

end LOOConcentration
