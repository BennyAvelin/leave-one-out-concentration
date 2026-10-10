import LOOConcentration.Analysis.DatasetClipMollify
import LOOConcentration.Concentration.SegmentEstimate
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-!
# Local slope of a smooth function in frozen dataset coordinates

The dataset coordinate map preserves the source's unnormalized Euclidean norm.
Consequently, the frozen limsup local slope of a smooth flattened function is
the operator norm of its Fréchet derivative. The squared slope is continuous.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

private theorem continuous_datasetToEuclidean_smooth {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation k m) N →
      EuclideanSpace ℝ (DatasetCoordinate k m N)) := by
  change Continuous (fun D : Dataset (Observation k m) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

private theorem continuous_datasetFromEuclidean_smooth {k m N : ℕ} :
    Continuous (datasetFromEuclidean : EuclideanSpace ℝ (DatasetCoordinate k m N) →
      Dataset (Observation k m) N) := by
  apply continuous_pi
  intro i
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ) (i, Sum.inl j)
  · apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ) (i, Sum.inr j)

/-- Pull a `C¹` scalar function on the flattened Euclidean dataset space back
to the frozen dataset carrier, with its required local-Lipschitz witness. -/
noncomputable def smoothDatasetPullback {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) : LocallyLipschitzDataFunction k m n := by
  let T : DataCarrier k m n → EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) := datasetToEuclidean
  have hT : Continuous T := continuous_datasetToEuclidean_smooth
  refine ⟨fun D => f (T D), ?_⟩
  intro D
  obtain ⟨K, U, hU, hLip⟩ := hf.locallyLipschitz (T D)
  refine ⟨T ⁻¹' U, hT.continuousAt.preimage_mem_nhds hU, K, K.coe_nonneg, ?_⟩
  intro E hE G hG
  have hdist := hLip.dist_le_mul (T E) hE (T G) hG
  calc
    |f (T E) - f (T G)| = dist (f (T E)) (f (T G)) := (Real.dist_eq _ _).symm
    _ ≤ (K : ℝ) * dist (T E) (T G) := hdist
    _ = (K : ℝ) * ‖datasetToEuclidean (E - G)‖ := by
      rw [dist_eq_norm, ← datasetToEuclidean_sub]
    _ = (K : ℝ) * datasetNorm (E - G) := by
      rw [← datasetNorm_eq_euclidean]

/-- For every frozen dataset, the local slope of a smooth pullback is the
operator norm of the Euclidean Fréchet derivative at its flattened point. -/
theorem datasetLocalSlope_smoothPullback_eq {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (D : DataCarrier k m n) :
    datasetLocalSlope (smoothDatasetPullback f hf) D =
      ‖fderiv ℝ f (datasetToEuclidean D)‖ := by
  letI : PerfectSpace (DataCarrier k m n) := perfectSpace_of_module ℝ _
  let x := datasetToEuclidean D
  let q : DataCarrier k m n → ℝ := fun E =>
    |f (datasetToEuclidean E) - f x| / datasetNorm (E - D)
  change limsup q (𝓝[≠] D) = ‖fderiv ℝ f x‖
  have hbounded : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) q := by
    simpa [q, x, smoothDatasetPullback] using
      datasetSlope_bounded (smoothDatasetPullback f hf) D
  have hnonneg : ∃ᶠ E in 𝓝[≠] D, 0 ≤ q E := by
    apply Filter.Frequently.of_forall
    intro E
    exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hCobounded : (𝓝[≠] D).IsCoboundedUnder (· ≤ ·) q := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    exact hnonneg
  have hupper : limsup q (𝓝[≠] D) ≤ ‖fderiv ℝ f x‖ := by
    apply (Filter.limsup_le_iff' hCobounded hbounded).2
    intro (c : ℝ) hc
    have hc0 : (0 : ℝ) ≤ c :=
      le_trans (norm_nonneg (fderiv ℝ f x)) hc.le
    let K : NNReal := Real.toNNReal c
    have hK : ‖fderiv ℝ f x‖₊ < K := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal c hc0]
      exact hc
    obtain ⟨U, hU, hLip⟩ := hf.contDiffAt.exists_lipschitzOnWith_of_nnnorm_lt K hK
    have hTpre : datasetToEuclidean ⁻¹' U ∈ 𝓝 D :=
      continuous_datasetToEuclidean_smooth.continuousAt.preimage_mem_nhds hU
    have hquot : ∀ᶠ E in 𝓝[≠] D, q E ≤ c := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hTpre,
        self_mem_nhdsWithin] with E hE hED
      have hne : E ≠ D := by simpa using hED
      have hxU : x ∈ U := mem_of_mem_nhds hU
      have hdist := hLip.dist_le_mul (datasetToEuclidean E) hE x hxU
      have hnorm : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hne
      have hdistEq : dist (datasetToEuclidean E) x = datasetNorm (E - D) := by
        calc
          dist (datasetToEuclidean E) x =
              ‖datasetToEuclidean E - datasetToEuclidean D‖ := by simp [x, dist_eq_norm]
          _ = ‖datasetToEuclidean (E - D)‖ := by rw [datasetToEuclidean_sub]
          _ = datasetNorm (E - D) := (datasetNorm_eq_euclidean _).symm
      have hnum : |f (datasetToEuclidean E) - f x| ≤ c * datasetNorm (E - D) := by
        rw [Real.dist_eq, hdistEq] at hdist
        simpa [K, Real.coe_toNNReal c hc0] using hdist
      exact (div_le_iff₀ hnorm).2 hnum
    exact hquot
  have hlower : ‖fderiv ℝ f x‖ ≤ limsup q (𝓝[≠] D) := by
    let L : ℝ := limsup q (𝓝[≠] D)
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact le_limsup_of_frequently_le hnonneg hbounded
    by_contra hnot
    have hgap : 0 < ‖fderiv ℝ f x‖ - L := sub_pos.mpr (lt_of_not_ge hnot)
    let ε : ℝ := (‖fderiv ℝ f x‖ - L) / 2
    let C : ℝ := L + ε
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hC : 0 ≤ C := by dsimp [C]; linarith
    have hEv : ∀ᶠ E in 𝓝[≠] D, q E < C := by
      have hlim : limsup q (𝓝[≠] D) ≤ L := by rfl
      exact (Filter.limsup_le_iff hCobounded hbounded).mp hlim C (by
        dsimp [C]
        linarith)
    have hLipAtData : ∀ᶠ E in 𝓝 D,
        |f (datasetToEuclidean E) - f x| ≤ C * datasetNorm (E - D) := by
      have hpunct := (eventually_nhdsWithin_iff.mp hEv)
      filter_upwards [hpunct] with E hE
      by_cases hED : E = D
      · subst E
        have hzero : f (datasetToEuclidean D) - f x = 0 := by simp [x]
        rw [hzero, abs_zero]
        exact mul_nonneg hC (Real.sqrt_nonneg _)
      · have hnorm : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hED
        exact (div_lt_iff₀ hnorm).mp (hE hED) |>.le
    have hLipAtEuclidean : ∀ᶠ y in 𝓝 x,
        ‖f y - f x‖ ≤ C * ‖y - x‖ := by
      have hcomp :=
        (continuous_datasetFromEuclidean_smooth.continuousAt (x := x)).eventually hLipAtData
      filter_upwards [hcomp] with y hy
      have hnorm : datasetNorm (datasetFromEuclidean y - D) = ‖y - x‖ := by
        rw [datasetNorm_sub_eq_euclidean]
        simp [x]
      simpa [datasetToEuclidean_fromEuclidean, datasetNorm_sub_eq_euclidean,
        Real.norm_eq_abs, x, hnorm] using hy
    have hderiv : ‖fderiv ℝ f x‖ ≤ C := norm_fderiv_le_of_lip' ℝ hC hLipAtEuclidean
    dsimp [C, ε] at hderiv
    linarith
  exact le_antisymm hupper hlower

/-- The squared frozen local slope of a smooth Euclidean pullback is
continuous on the exact dataset carrier. -/
theorem continuous_datasetLocalSlope_sq_smoothPullback {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun D : DataCarrier k m n =>
      (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2) := by
  have hderiv : Continuous (fun D : DataCarrier k m n =>
      fderiv ℝ f (datasetToEuclidean D)) :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_datasetToEuclidean_smooth
  have hnorm : Continuous (fun D : DataCarrier k m n =>
      ‖fderiv ℝ f (datasetToEuclidean D)‖ ^ 2) :=
    (continuous_norm.comp hderiv).pow 2
  have heq : (fun D : DataCarrier k m n =>
      (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2) =
      fun D => ‖fderiv ℝ f (datasetToEuclidean D)‖ ^ 2 := by
    funext D
    rw [datasetLocalSlope_smoothPullback_eq]
  rw [heq]
  exact hnorm

theorem measurable_datasetLocalSlope_sq_smoothPullback {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Measurable (fun D : DataCarrier k m n =>
      (datasetLocalSlope (smoothDatasetPullback f hf) D) ^ 2) :=
  (continuous_datasetLocalSlope_sq_smoothPullback f hf).measurable

end LOOConcentration
