import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic
import LOOConcentration.Examples.GaussianInverseDesignMoment
import LOOConcentration.Examples.OlsGaussianTails

set_option autoImplicit false

open MeasureTheory
open ProbabilityTheory
open scoped NNReal

namespace LOOConcentration

private noncomputable abbrev designGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

private def designCovariates {N : ℕ} (G : Fin N → ℝ × ℝ) : Fin N → ℝ :=
  fun i => (G i).1

private def designTailSqSum {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, (x i) ^ 2

private noncomputable def designCovariateStats {r : ℕ} (x : Fin (r + 1) → ℝ) : ℝ × ℝ :=
  ((∑ i : Fin (r + 1), x i) / ((r + 1 : ℕ) : ℝ),
    ∑ i : Fin (r + 1),
      (x i - (∑ j : Fin (r + 1), x j) / ((r + 1 : ℕ) : ℝ)) ^ 2)

private noncomputable def designMeanDirection (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1)) :=
  WithLp.toLp 2
    (fun _ : Fin (r + 1) => (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)

private noncomputable def designFirstVector (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1)) :=
  PiLp.single 2 0 (1 : ℝ)

private noncomputable def designMeanReflection (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + 1)) :=
  Submodule.reflection (ℝ ∙ (designMeanDirection r - designFirstVector r))ᗮ

private def designFromEuclidean {r : ℕ}
    (z : EuclideanSpace ℝ (Fin (r + 1))) : Fin (r + 1) → ℝ :=
  WithLp.ofLp z

private noncomputable def designReflectCoordinates {r : ℕ} (x : Fin (r + 1) → ℝ) :
    Fin (r + 1) → ℝ :=
  designFromEuclidean (designMeanReflection r (WithLp.toLp 2 x))

private def designSplitFirst {r : ℕ} (x : Fin (r + 1) → ℝ) :
    ℝ × (Fin r → ℝ) :=
  (x 0, fun j => x ((0 : Fin (r + 1)).succAbove j))

private lemma designMeanDirection_norm_eq (r : ℕ) :
    ‖designMeanDirection r‖ = ‖designFirstVector r‖ := by
  have hN : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hN
  have hdir : ‖designMeanDirection r‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin (r + 1),
      ((Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) ^ 2) = 1
    calc
      _ = ((r + 1 : ℕ) : ℝ) *
          (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
        calc
          _ = (Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 *
              (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ ^ 2 := by
            exact congrArg (fun a : ℝ => a *
              (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ ^ 2)
              (Real.sq_sqrt hN.le).symm
          _ = 1 := by field_simp [ne_of_gt hsqrt]
  have he : ‖designFirstVector r‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [designFirstVector]
  nlinarith [norm_nonneg (designMeanDirection r), norm_nonneg (designFirstVector r)]

private lemma designMeanReflection_maps_direction (r : ℕ) :
    designMeanReflection r (designMeanDirection r) = designFirstVector r := by
  exact Submodule.reflection_sub (designMeanDirection_norm_eq r)

private lemma designCovariateStats_reflection (r : ℕ) (x : Fin (r + 1) → ℝ) :
    designCovariateStats x =
      ((designReflectCoordinates x) 0 /
          Real.sqrt ((r + 1 : ℕ) : ℝ),
        designTailSqSum (fun j =>
          (designReflectCoordinates x) ((0 : Fin (r + 1)).succAbove j))) := by
  let z : EuclideanSpace ℝ (Fin (r + 1)) := WithLp.toLp 2 x
  let R := designMeanReflection r
  let u := designMeanDirection r
  let e := designFirstVector r
  have hRu : R u = e := designMeanReflection_maps_direction r
  have hcoordinate : (R z) 0 =
      (∑ i : Fin (r + 1), x i) / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    have hi := R.inner_map_map z u
    rw [hRu] at hi
    change inner ℝ (R z) (PiLp.single 2 0 (1 : ℝ)) = inner ℝ z u at hi
    rw [EuclideanSpace.inner_single_right] at hi
    have hi' : (R z) 0 = ∑ i : Fin (r + 1), x i *
        (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
      simpa [u, z, designMeanDirection, PiLp.toLp_apply, PiLp.inner_apply,
        mul_comm] using hi
    calc
      (R z) 0 = ∑ i : Fin (r + 1), x i *
          (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := hi'
      _ = (∑ i : Fin (r + 1), x i) /
          Real.sqrt ((r + 1 : ℕ) : ℝ) := by
        simp [div_eq_mul_inv, Finset.sum_mul]
  have hnorm : (∑ i : Fin (r + 1), (R z i) ^ 2) =
      ∑ i : Fin (r + 1), (x i) ^ 2 := by
    calc
      _ = ‖R z‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq (R z)).symm
      _ = ‖z‖ ^ 2 := by rw [R.norm_map]
      _ = ∑ i : Fin (r + 1), (x i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have htail : (∑ j : Fin r, (R z ((0 : Fin (r + 1)).succAbove j)) ^ 2) =
      (∑ i : Fin (r + 1), (R z i) ^ 2) - (R z 0) ^ 2 := by
    have hsum := Fin.sum_univ_succAbove
      (fun i : Fin (r + 1) => (R z i) ^ 2) (0 : Fin (r + 1))
    linarith
  have hcoordSq : (R z 0) ^ 2 =
      (∑ i : Fin (r + 1), x i) ^ 2 / ((r + 1 : ℕ) : ℝ) := by
    rw [hcoordinate, div_pow, Real.sq_sqrt (by positivity :
      0 ≤ ((r + 1 : ℕ) : ℝ))]
  have hcenter :
      (∑ i : Fin (r + 1),
        (x i - (∑ j : Fin (r + 1), x j) / ((r + 1 : ℕ) : ℝ)) ^ 2) =
      (∑ i : Fin (r + 1), x i ^ 2) -
        (∑ i : Fin (r + 1), x i) ^ 2 / ((r + 1 : ℕ) : ℝ) := by
    let c : ℝ := (∑ i : Fin (r + 1), x i) / ((r + 1 : ℕ) : ℝ)
    have hcross : (∑ i : Fin (r + 1), 2 * x i * c) =
        2 * c * (∑ i : Fin (r + 1), x i) := by
      calc
        _ = ∑ i : Fin (r + 1), c * (2 * x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = c * ∑ i : Fin (r + 1), 2 * x i := by rw [Finset.mul_sum]
        _ = 2 * c * ∑ i : Fin (r + 1), x i := by rw [← Finset.mul_sum]; ring
    have hconst : (∑ _i : Fin (r + 1), c ^ 2) =
        ((r + 1 : ℕ) : ℝ) * c ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    calc
      _ = ∑ i : Fin (r + 1), (x i - c) ^ 2 := by rfl
      _ = ∑ i : Fin (r + 1), (x i ^ 2 - 2 * x i * c + c ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i : Fin (r + 1), x i ^ 2) -
          2 * c * (∑ i : Fin (r + 1), x i) +
          ((r + 1 : ℕ) : ℝ) * c ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
      _ = (∑ i : Fin (r + 1), x i ^ 2) -
          (∑ i : Fin (r + 1), x i) ^ 2 / ((r + 1 : ℕ) : ℝ) := by
        have hcast : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        dsimp [c]
        field_simp [hcast]
        ring
  apply Prod.ext
  · dsimp [designCovariateStats, designReflectCoordinates, designFromEuclidean]
    rw [hcoordinate]
    have hN : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hsqrt : Real.sqrt ((r + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp [hN, hsqrt]
    rw [Real.sq_sqrt (by positivity : 0 ≤ ((r + 1 : ℕ) : ℝ))]
  · change
      (∑ i : Fin (r + 1),
        (x i - (∑ j : Fin (r + 1), x j) / ((r + 1 : ℕ) : ℝ)) ^ 2) =
      ∑ j : Fin r, (R z ((0 : Fin (r + 1)).succAbove j)) ^ 2
    rw [htail, hnorm, hcoordSq, ← hcenter]

private lemma measurable_designReflectCoordinates {r : ℕ} :
    Measurable (designReflectCoordinates (r := r)) := by
  unfold designReflectCoordinates designFromEuclidean
  fun_prop

private lemma measurable_designSplitFirst {r : ℕ} :
    Measurable (designSplitFirst (r := r)) := by
  apply Measurable.prodMk
  · exact measurable_pi_apply 0
  · rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply ((0 : Fin (r + 1)).succAbove j)

@[fun_prop]
private lemma measurable_designTailSqSum {r : ℕ} :
    Measurable (designTailSqSum (r := r)) := by
  unfold designTailSqSum
  fun_prop

private lemma measurable_designCovariateStats (r : ℕ) :
    Measurable (designCovariateStats (r := r)) := by
  unfold designCovariateStats
  fun_prop

private lemma measurable_designMeanScale (r : ℕ) :
    Measurable (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) := by
  fun_prop

private lemma measurable_olsMeanDesignStats {N : ℕ} :
    Measurable (fun G : Fin N → ℝ × ℝ => (olsXBar G, olsCenteredDesign G)) := by
  exact continuous_olsXBar.measurable.prodMk continuous_olsCenteredDesign.measurable

private lemma measure_map_designReflectCoordinates (r : ℕ) :
    (Measure.pi fun _ : Fin (r + 1) => designGaussian).map
      (designReflectCoordinates (r := r)) =
    Measure.pi fun _ : Fin (r + 1) => designGaussian := by
  let E := EuclideanSpace ℝ (Fin (r + 1))
  let R := designMeanReflection r
  have hR : (ProbabilityTheory.stdGaussian E).map R =
      ProbabilityTheory.stdGaussian E := ProbabilityTheory.stdGaussian_map R
  calc
    _ = ((Measure.pi fun _ : Fin (r + 1) => designGaussian).map (WithLp.toLp 2)).map
        (fun z : EuclideanSpace ℝ (Fin (r + 1)) => designFromEuclidean (R z)) := by
      exact (Measure.map_map
        ((WithLp.measurable_ofLp 2 (Fin (r + 1) → ℝ)).comp R.continuous.measurable)
        (WithLp.measurable_toLp 2 (Fin (r + 1) → ℝ))).symm
    _ = ((ProbabilityTheory.stdGaussian E).map R).map
        designFromEuclidean := by
      rw [ProbabilityTheory.map_pi_eq_stdGaussian]
      exact (Measure.map_map
        (WithLp.measurable_ofLp 2 (Fin (r + 1) → ℝ))
        R.continuous.measurable).symm
    _ = (ProbabilityTheory.stdGaussian E).map
        designFromEuclidean := by rw [hR]
    _ = Measure.pi fun _ : Fin (r + 1) => designGaussian := by
      unfold designFromEuclidean
      rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
      rw [Measure.map_map (WithLp.measurable_ofLp 2 (Fin (r + 1) → ℝ))
        (WithLp.measurable_toLp 2 (Fin (r + 1) → ℝ))]
      have hcomp :
          (fun x : Fin (r + 1) → ℝ => WithLp.ofLp (WithLp.toLp 2 x)) = id := by
        funext x
        exact WithLp.ofLp_toLp 2 x
      change Measure.map
        (fun x : Fin (r + 1) → ℝ => WithLp.ofLp (WithLp.toLp 2 x))
        (Measure.pi fun _ : Fin (r + 1) => designGaussian) = _
      rw [hcomp, Measure.map_id]

private lemma measure_map_designSplitFirst (r : ℕ) :
    (Measure.pi fun _ : Fin (r + 1) => designGaussian).map
      (designSplitFirst (r := r)) =
    designGaussian.prod (Measure.pi fun _ : Fin r => designGaussian) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ)
    (0 : Fin (r + 1))
  have hp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (r + 1) => designGaussian) (0 : Fin (r + 1))
  have he : (designSplitFirst (r := r)) = e := by
    funext x
    rfl
  rw [he]
  exact hp.map_eq

private lemma measure_map_designReflectedSplit (r : ℕ) :
    (Measure.pi fun _ : Fin (r + 1) => designGaussian).map
      (fun x => designSplitFirst (designReflectCoordinates x)) =
    designGaussian.prod (Measure.pi fun _ : Fin r => designGaussian) := by
  calc
    _ = ((Measure.pi fun _ : Fin (r + 1) => designGaussian).map
        designReflectCoordinates).map designSplitFirst := by
      exact (Measure.map_map measurable_designSplitFirst
        measurable_designReflectCoordinates).symm
    _ = (Measure.pi fun _ : Fin (r + 1) => designGaussian).map designSplitFirst := by
      rw [measure_map_designReflectCoordinates]
    _ = designGaussian.prod (Measure.pi fun _ : Fin r => designGaussian) :=
      measure_map_designSplitFirst r

private lemma measurable_designDownstream (r : ℕ) :
    Measurable (fun z : ℝ × (Fin r → ℝ) =>
      (z.1 / Real.sqrt ((r + 1 : ℕ) : ℝ), designTailSqSum z.2)) := by
  fun_prop

private lemma measure_map_designCovariateStats (r : ℕ) :
    (Measure.pi fun _ : Fin (r + 1) => designGaussian).map designCovariateStats =
      (Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian).prod
        (Measure.map designTailSqSum (Measure.pi fun _ : Fin r => designGaussian)) := by
  let ν : Measure (Fin (r + 1) → ℝ) :=
    Measure.pi fun _ : Fin (r + 1) => designGaussian
  let splitReflect : (Fin (r + 1) → ℝ) → ℝ × (Fin r → ℝ) :=
    fun x => designSplitFirst (designReflectCoordinates x)
  let downstream : ℝ × (Fin r → ℝ) → ℝ × ℝ :=
    fun z => (z.1 / Real.sqrt ((r + 1 : ℕ) : ℝ), designTailSqSum z.2)
  have hfun : designCovariateStats = downstream ∘ splitReflect := by
    funext x
    exact designCovariateStats_reflection r x
  calc
    _ = ν.map (downstream ∘ splitReflect) := by rw [hfun]
    _ = (ν.map splitReflect).map downstream := by
      exact (Measure.map_map (measurable_designDownstream r)
        (measurable_designSplitFirst.comp measurable_designReflectCoordinates)).symm
    _ = (designGaussian.prod (Measure.pi fun _ : Fin r => designGaussian)).map downstream := by
      rw [measure_map_designReflectedSplit]
    _ = (Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ))
          designGaussian).prod
        (Measure.map designTailSqSum (Measure.pi fun _ : Fin r => designGaussian)) := by
      exact (Measure.map_prod_map _ _ (measurable_designMeanScale r)
        (measurable_designTailSqSum (r := r))).symm

private lemma measure_map_designCovariates (r : ℕ) :
    (olsPairGaussianLaw (r + 1)).map (designCovariates (N := r + 1)) =
      Measure.pi fun _ : Fin (r + 1) => designGaussian := by
  change (Measure.pi fun _ : Fin (r + 1) =>
    designGaussian.prod designGaussian).map
      (fun G i => (G i).1) = Measure.pi fun _ : Fin (r + 1) => designGaussian
  rw [Measure.pi_map_pi (f := fun _ => Prod.fst)]
  · congr 1
    funext i
    simp [Measure.map_fst_prod, designGaussian]
  · intro i
    exact measurable_fst.aemeasurable

private lemma measure_map_olsMeanDesign_succ (r : ℕ) :
    (olsPairGaussianLaw (r + 1)).map
      (fun G => (olsXBar G, olsCenteredDesign G)) =
    (Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian).prod
      (Measure.map olsCenteredDesign (olsPairGaussianLaw (r + 1))) := by
  let ν : Measure (Fin (r + 1) → ℝ) :=
    Measure.pi fun _ : Fin (r + 1) => designGaussian
  have htail : (Measure.map designTailSqSum (Measure.pi fun _ : Fin r => designGaussian)) =
      Measure.map olsCenteredDesign (olsPairGaussianLaw (r + 1)) := by
    change Measure.map (fun x : Fin r → ℝ => ∑ i : Fin r, x i ^ 2)
        (Measure.pi fun _ : Fin r => ProbabilityTheory.gaussianReal 0 1) =
      Measure.map olsCenteredDesign
        (Measure.pi fun _ : Fin (r + 1) =>
          (ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1))
    exact (olsCenteredDesign_gaussian_pushforward r).symm
  have hcomp :
      (fun G : Fin (r + 1) → ℝ × ℝ => (olsXBar G, olsCenteredDesign G)) =
        designCovariateStats (r := r) ∘ designCovariates (N := r + 1) := by
    funext G
    apply Prod.ext
    · simp [designCovariateStats, designCovariates, olsXBar]
    · simp [designCovariateStats, designCovariates, olsCenteredDesign, olsXBar]
  calc
    _ = ((olsPairGaussianLaw (r + 1)).map
        (designCovariates (N := r + 1))).map designCovariateStats := by
      rw [hcomp]
      exact (Measure.map_map (measurable_designCovariateStats r)
        (by
          rw [measurable_pi_iff]
          intro i
          exact measurable_fst.comp (measurable_pi_apply i))).symm
    _ = (Measure.pi fun _ : Fin (r + 1) => designGaussian).map designCovariateStats := by
      rw [measure_map_designCovariates]
    _ = _ := by rw [measure_map_designCovariateStats, htail]

private lemma measure_map_olsXBar_succ (r : ℕ) :
    (olsPairGaussianLaw (r + 1)).map olsXBar =
      Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian := by
  let μ := olsPairGaussianLaw (r + 1)
  let m := Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian
  let s := Measure.map olsCenteredDesign μ
  have hs : s Set.univ = 1 := by
    rw [Measure.map_apply continuous_olsCenteredDesign.measurable MeasurableSet.univ]
    simp [μ]
  have hjoint := measure_map_olsMeanDesign_succ r
  calc
    _ = Measure.map Prod.fst (Measure.map
        (fun G : Fin (r + 1) → ℝ × ℝ => (olsXBar G, olsCenteredDesign G)) μ) := by
      rw [Measure.map_map measurable_fst (measurable_olsMeanDesignStats (N := r + 1))]
      rfl
    _ = Measure.map Prod.fst (m.prod s) := by rw [hjoint]
    _ = m := by
      rw [Measure.map_fst_prod, hs, one_smul]

private lemma integrable_designGaussian_sq :
    Integrable (fun x : ℝ => x ^ 2) designGaussian := by
  simpa [designGaussian] using
    (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) (2 : ℝ≥0)).integrable_sq

private lemma integral_designGaussian_sq :
    (∫ x : ℝ, x ^ 2 ∂designGaussian) = 1 := by
  have hvar : Var[id; designGaussian] = 1 := by simp [designGaussian]
  have hvarInt : Var[id; designGaussian] =
      ∫ x : ℝ, (x - 0) ^ 2 ∂designGaussian := by
    simpa [designGaussian] using
      (variance_eq_integral (X := id) (μ := designGaussian)
        measurable_id'.aemeasurable)
  calc
    _ = ∫ x : ℝ, (x - 0) ^ 2 ∂designGaussian := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = Var[id; designGaussian] := hvarInt.symm
    _ = 1 := hvar

private lemma designMeanScale_sq_pointwise (r : ℕ) (z : ℝ) :
    (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 =
      (1 / ((r + 1 : ℕ) : ℝ)) * z ^ 2 := by
  have hN : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt ((r + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ ((r + 1 : ℕ) : ℝ))]
  field_simp [hN, hsqrt]

private lemma integrable_designMeanScale_sq (r : ℕ) :
    Integrable (fun z : ℝ =>
      (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2) designGaussian := by
  have h := integrable_designGaussian_sq.const_mul
    (1 / ((r + 1 : ℕ) : ℝ))
  convert h using 1
  funext z
  rw [designMeanScale_sq_pointwise]

private lemma integral_designMeanScale_sq (r : ℕ) :
    (∫ z : ℝ,
      (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 ∂designGaussian) =
      1 / ((r + 1 : ℕ) : ℝ) := by
  calc
    _ = ∫ z : ℝ, (1 / ((r + 1 : ℕ) : ℝ)) * z ^ 2 ∂designGaussian := by
      apply integral_congr_ae
      exact ae_of_all _ (designMeanScale_sq_pointwise r)
    _ = (1 / ((r + 1 : ℕ) : ℝ)) *
        ∫ z : ℝ, z ^ 2 ∂designGaussian := by rw [integral_const_mul]
    _ = 1 / ((r + 1 : ℕ) : ℝ) := by rw [integral_designGaussian_sq]; ring

private lemma integrable_olsXBar_sq_succ (r : ℕ) :
    Integrable (fun G : Fin (r + 1) → ℝ × ℝ => (olsXBar G) ^ 2)
      (olsPairGaussianLaw (r + 1)) := by
  let μ := olsPairGaussianLaw (r + 1)
  let m := Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian
  have hm : Integrable (fun y : ℝ => y ^ 2) m := by
    have hcomp : Integrable
        ((fun y : ℝ => y ^ 2) ∘
          (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ))) designGaussian := by
      change Integrable (fun z : ℝ =>
        (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2) designGaussian
      exact integrable_designMeanScale_sq r
    exact (integrable_map_measure (by fun_prop)
      (measurable_designMeanScale r).aemeasurable).mpr hcomp
  have hbar : Integrable (fun y : ℝ => y ^ 2) (Measure.map olsXBar μ) := by
    rw [measure_map_olsXBar_succ r]
    exact hm
  exact (integrable_map_measure (by fun_prop)
    (continuous_olsXBar.measurable.aemeasurable)).mp hbar

private lemma integral_olsXBar_sq_succ (r : ℕ) :
    (∫ G : Fin (r + 1) → ℝ × ℝ, (olsXBar G) ^ 2
      ∂olsPairGaussianLaw (r + 1)) = 1 / ((r + 1 : ℕ) : ℝ) := by
  calc
    _ = ∫ y : ℝ, y ^ 2 ∂Measure.map olsXBar (olsPairGaussianLaw (r + 1)) := by
      symm
      exact integral_map continuous_olsXBar.measurable.aemeasurable (by fun_prop)
    _ = ∫ y : ℝ, y ^ 2 ∂Measure.map
        (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian := by
      rw [measure_map_olsXBar_succ]
    _ = ∫ z : ℝ,
        (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 ∂designGaussian := by
      exact integral_map (measurable_designMeanScale r).aemeasurable (by fun_prop)
    _ = 1 / ((r + 1 : ℕ) : ℝ) := integral_designMeanScale_sq r

private lemma integrable_olsMeanDesignProduct_succ {r : ℕ} (hr : 2 < r) :
    Integrable
      (fun G : Fin (r + 1) → ℝ × ℝ =>
        (olsXBar G) ^ 2 * (olsCenteredDesign G)⁻¹)
      (olsPairGaussianLaw (r + 1)) := by
  let μ := olsPairGaussianLaw (r + 1)
  let m := Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian
  let s := Measure.map olsCenteredDesign μ
  have hf : Integrable (fun y : ℝ => y ^ 2) m := by
    have hcomp : Integrable
        ((fun y : ℝ => y ^ 2) ∘
          (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ))) designGaussian := by
      change Integrable (fun z : ℝ =>
        (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2) designGaussian
      exact integrable_designMeanScale_sq r
    exact (integrable_map_measure (by fun_prop)
      (measurable_designMeanScale r).aemeasurable).mpr hcomp
  have hg : Integrable (fun y : ℝ => y⁻¹) s := by
    refine (integrable_map_measure (by fun_prop)
      continuous_olsCenteredDesign.measurable.aemeasurable).mpr ?_
    exact integrable_inv_olsCenteredDesign_gaussian
      (d := r) (by omega : 2 < r)
  have hprod : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2⁻¹) (m.prod s) :=
    hf.mul_prod hg
  have hstat : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2⁻¹)
      (μ.map (fun G : Fin (r + 1) → ℝ × ℝ =>
        (olsXBar G, olsCenteredDesign G))) := by
    rw [measure_map_olsMeanDesign_succ r]
    exact hprod
  exact (integrable_map_measure (by fun_prop)
    (measurable_olsMeanDesignStats (N := r + 1)).aemeasurable).mp hstat

private lemma integral_olsMeanDesignProduct_succ {r : ℕ} (hr : 2 < r) :
    (∫ G : Fin (r + 1) → ℝ × ℝ,
      (olsXBar G) ^ 2 * (olsCenteredDesign G)⁻¹
        ∂olsPairGaussianLaw (r + 1)) =
      1 / (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 3)) := by
  let μ := olsPairGaussianLaw (r + 1)
  let m := Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian
  let s := Measure.map olsCenteredDesign μ
  have hdesign : (∫ y : ℝ, y⁻¹ ∂s) =
      1 / (((r + 1 : ℕ) : ℝ) - 3) := by
    calc
      _ = ∫ G : Fin (r + 1) → ℝ × ℝ,
          (olsCenteredDesign G)⁻¹ ∂μ := by
        dsimp [s, μ]
        exact integral_map continuous_olsCenteredDesign.measurable.aemeasurable (by fun_prop)
      _ = 1 / (((r + 1 : ℕ) : ℝ) - 3) := by
        simpa using integral_inv_olsCenteredDesign_gaussian_sample
          (N := r + 1) (by omega : 3 < r + 1)
  calc
    _ = ∫ z : ℝ × ℝ, z.1 ^ 2 * z.2⁻¹ ∂Measure.map
        (fun G : Fin (r + 1) → ℝ × ℝ =>
          (olsXBar G, olsCenteredDesign G)) μ := by
      symm
      exact integral_map (measurable_olsMeanDesignStats (N := r + 1)).aemeasurable
        (by fun_prop)
    _ = ∫ z : ℝ × ℝ, z.1 ^ 2 * z.2⁻¹ ∂m.prod s := by
      rw [measure_map_olsMeanDesign_succ r]
    _ = (∫ y : ℝ, y ^ 2 ∂m) * ∫ y : ℝ, y⁻¹ ∂s := by
      exact integral_prod_mul (fun y : ℝ => y ^ 2) (fun y : ℝ => y⁻¹)
    _ = 1 / (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 3)) := by
      have hmean : (∫ y : ℝ, y ^ 2 ∂m) =
          1 / ((r + 1 : ℕ) : ℝ) := by
        calc
          _ = ∫ z : ℝ,
              (z / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 ∂designGaussian := by
            dsimp [m]
            exact integral_map (measurable_designMeanScale r).aemeasurable (by fun_prop)
          _ = _ := integral_designMeanScale_sq r
      rw [hmean, hdesign]
      have hN : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
      have hD : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) - 3 := by
        push_cast
        have hr' : (2 : ℝ) < r := by exact_mod_cast hr
        linarith
      field_simp [ne_of_gt hN, ne_of_gt hD]

private lemma olsXBar_olsCenteredDesign_jointLaw_succ (r : ℕ) :
    (olsPairGaussianLaw (r + 1)).map
      (fun G => (olsXBar G, olsCenteredDesign G)) =
      ((olsPairGaussianLaw (r + 1)).map olsXBar).prod
        ((olsPairGaussianLaw (r + 1)).map olsCenteredDesign) := by
  let μ := olsPairGaussianLaw (r + 1)
  let m := Measure.map (fun z : ℝ => z / Real.sqrt ((r + 1 : ℕ) : ℝ)) designGaussian
  let s := Measure.map olsCenteredDesign μ
  have hjoint := measure_map_olsMeanDesign_succ r
  have hbar : μ.map olsXBar = m := measure_map_olsXBar_succ r
  have hdesign : μ.map olsCenteredDesign = s := rfl
  rw [hjoint, hbar, hdesign]

/-- Under the actual iid Gaussian pair law, the covariate sample mean and its
centered sum of squares are independent. The proof obtains their joint law by
an orthogonal reflection and a finite product-coordinate split. -/
theorem olsXBar_olsCenteredDesign_indepFun {N : ℕ} (hN : 0 < N) :
    ProbabilityTheory.IndepFun (olsXBar : (Fin N → ℝ × ℝ) → ℝ) olsCenteredDesign
      (olsPairGaussianLaw N) := by
  cases N with
  | zero => omega
  | succ r =>
      have hjoint := olsXBar_olsCenteredDesign_jointLaw_succ r
      exact (indepFun_iff_map_prod_eq_prod_map_map
        (continuous_olsXBar.measurable.aemeasurable)
        (continuous_olsCenteredDesign.measurable.aemeasurable)).2 hjoint

/-- The actual Gaussian sample mean has second moment `1/N`. -/
theorem integrable_olsXBar_sq {N : ℕ} (hN : 0 < N) :
    Integrable (fun G : Fin N → ℝ × ℝ => (olsXBar G) ^ 2)
      (olsPairGaussianLaw N) := by
  cases N with
  | zero => omega
  | succ r => exact integrable_olsXBar_sq_succ r

theorem integral_olsXBar_sq {N : ℕ} (hN : 0 < N) :
    (∫ G : Fin N → ℝ × ℝ, (olsXBar G) ^ 2 ∂olsPairGaussianLaw N) =
      1 / (N : ℝ) := by
  cases N with
  | zero => omega
  | succ r => exact integral_olsXBar_sq_succ r

/-- Integrability of the actual mixed mean-square/inverse-design statistic.
It follows from the joint product law and the two separately integrable
factors; the inverse moment is supplied by wave 10. -/
theorem integrable_olsXBar_sq_div_olsCenteredDesign {N : ℕ} (hN : 3 < N) :
    Integrable
      (fun G : Fin N → ℝ × ℝ =>
        (olsXBar G) ^ 2 / olsCenteredDesign G)
      (olsPairGaussianLaw N) := by
  cases N with
  | zero => omega
  | succ r =>
      have hr : 2 < r := by omega
      simpa [div_eq_mul_inv] using integrable_olsMeanDesignProduct_succ hr

/-- The mixed mean-square/inverse-design expectation under the actual iid
Gaussian pair law factors as `1/(N(N-3))` for `N > 3`. -/
theorem integral_olsXBar_sq_div_olsCenteredDesign {N : ℕ} (hN : 3 < N) :
    (∫ G : Fin N → ℝ × ℝ,
      (olsXBar G) ^ 2 / olsCenteredDesign G ∂olsPairGaussianLaw N) =
      1 / ((N : ℝ) * ((N : ℝ) - 3)) := by
  cases N with
  | zero => omega
  | succ r =>
      have hr : 2 < r := by omega
      simpa [div_eq_mul_inv] using integral_olsMeanDesignProduct_succ hr

#print axioms olsXBar_olsCenteredDesign_indepFun
#print axioms integrable_olsXBar_sq
#print axioms integral_olsXBar_sq
#print axioms integrable_olsXBar_sq_div_olsCenteredDesign
#print axioms integral_olsXBar_sq_div_olsCenteredDesign

end LOOConcentration
