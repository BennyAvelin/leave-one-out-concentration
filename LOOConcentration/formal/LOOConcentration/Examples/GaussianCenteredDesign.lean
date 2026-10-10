import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.OlsDesign

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LOOConcentration

private noncomputable abbrev centeredDesignGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

private noncomputable def centeredCovariateSqSum {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (x i - (∑ j : Fin N, x j) / (N : ℝ)) ^ 2

private def covariateSqSum {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (x i) ^ 2

private lemma measurable_covariateSqSum {N : ℕ} :
    Measurable (covariateSqSum (N := N)) := by
  unfold covariateSqSum
  fun_prop

private lemma centeredCovariateSqSum_eq_sub_meanSq {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) :
    centeredCovariateSqSum x = covariateSqSum x -
      (∑ i : Fin N, x i) ^ 2 / (N : ℝ) := by
  let c : ℝ := (∑ i : Fin N, x i) / (N : ℝ)
  have hcross : (∑ i : Fin N, 2 * x i * c) =
      2 * c * (∑ i : Fin N, x i) := by
    calc
      _ = ∑ i : Fin N, c * (2 * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin N, 2 * x i := by rw [Finset.mul_sum]
      _ = 2 * c * ∑ i : Fin N, x i := by rw [← Finset.mul_sum]; ring
  have hconst : (∑ _i : Fin N, c ^ 2) = (N : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  unfold centeredCovariateSqSum covariateSqSum
  change (∑ i : Fin N, (x i - c) ^ 2) = _
  calc
    _ = ∑ i : Fin N, (x i ^ 2 - 2 * x i * c + c ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin N, x i ^ 2) -
        2 * c * (∑ i : Fin N, x i) + (N : ℝ) * c ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
    _ = (∑ i : Fin N, x i ^ 2) - (∑ i : Fin N, x i) ^ 2 / (N : ℝ) := by
      have hcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      dsimp [c]
      field_simp [hcast]
      ring

private noncomputable def centeredDirection (r : ℕ) : EuclideanSpace ℝ (Fin (r + 1)) :=
  WithLp.toLp 2 (fun _ : Fin (r + 1) => (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)

private noncomputable def firstCoordinateVector (r : ℕ) : EuclideanSpace ℝ (Fin (r + 1)) :=
  PiLp.single 2 0 (1 : ℝ)

private noncomputable def centeredReflection (r : ℕ) :
    EuclideanSpace ℝ (Fin (r + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + 1)) :=
  Submodule.reflection (ℝ ∙ (centeredDirection r - firstCoordinateVector r))ᗮ

private lemma centeredDirection_norm_eq (r : ℕ) :
    ‖centeredDirection r‖ = ‖firstCoordinateVector r‖ := by
  have hN : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hN
  have hdir : ‖centeredDirection r‖ ^ 2 = 1 := by
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
  have he : ‖firstCoordinateVector r‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [firstCoordinateVector]
  nlinarith [norm_nonneg (centeredDirection r), norm_nonneg (firstCoordinateVector r)]

private lemma centeredReflection_maps_direction (r : ℕ) :
    centeredReflection r (centeredDirection r) = firstCoordinateVector r := by
  exact Submodule.reflection_sub (centeredDirection_norm_eq r)

private def dropFirst {r : ℕ} (x : EuclideanSpace ℝ (Fin (r + 1))) : Fin r → ℝ :=
  fun j => x ((0 : Fin (r + 1)).succAbove j)

private def rawDropFirst {r : ℕ} (x : Fin (r + 1) → ℝ) : Fin r → ℝ :=
  fun j => x ((0 : Fin (r + 1)).succAbove j)

private lemma iid_gaussian_drop_first (r : ℕ) :
    (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
      (rawDropFirst (r := r)) =
      Measure.pi (fun _ : Fin r => centeredDesignGaussian) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ)
    (0 : Fin (r + 1))
  have hp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (r + 1) => centeredDesignGaussian) (0 : Fin (r + 1))
  calc
    _ = ((Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map e).map
        Prod.snd := by
      rw [Measure.map_map measurable_snd e.measurable]
      rfl
    _ = (centeredDesignGaussian.prod
        (Measure.pi (fun _ : Fin r => centeredDesignGaussian))).map Prod.snd := by
      rw [hp.map_eq]
    _ = Measure.pi (fun _ : Fin r => centeredDesignGaussian) := by
      simp [Measure.map_snd_prod]

private lemma iid_pair_covariate_marginal (N : ℕ) :
    (Measure.pi (fun _ : Fin N => centeredDesignGaussian.prod centeredDesignGaussian)).map
      (fun G i => (G i).1) = Measure.pi (fun _ : Fin N => centeredDesignGaussian) := by
  rw [Measure.pi_map_pi (f := fun _ => Prod.fst)]
  · congr 1
    funext i
    simp [Measure.map_fst_prod]
  · intro i
    exact measurable_fst.aemeasurable

private lemma reflection_centering_identity (r : ℕ) (x : Fin (r + 1) → ℝ) :
    centeredCovariateSqSum x =
      covariateSqSum (dropFirst (centeredReflection r (WithLp.toLp 2 x))) := by
  let z : EuclideanSpace ℝ (Fin (r + 1)) := WithLp.toLp 2 x
  let R := centeredReflection r
  let u := centeredDirection r
  let e := firstCoordinateVector r
  have hRu : R u = e := centeredReflection_maps_direction r
  have hcoordinate : (R z) 0 = (∑ i : Fin (r + 1), x i) /
      Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    have hi := R.inner_map_map z u
    rw [hRu] at hi
    change inner ℝ (R z) (PiLp.single 2 0 (1 : ℝ)) = inner ℝ z u at hi
    rw [EuclideanSpace.inner_single_right] at hi
    have hi' : (R z) 0 = ∑ i : Fin (r + 1), x i *
        (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
      simpa [u, z, centeredDirection, PiLp.toLp_apply, PiLp.inner_apply,
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
      _ = ∑ i : Fin (r + 1), (x i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have htail : (∑ j : Fin r, (R z ((0 : Fin (r + 1)).succAbove j)) ^ 2) =
      (∑ i : Fin (r + 1), (R z i) ^ 2) - (R z 0) ^ 2 := by
    have hsum := Fin.sum_univ_succAbove
      (fun i : Fin (r + 1) => (R z i) ^ 2) (0 : Fin (r + 1))
    linarith
  have hcoordSq : (R z 0) ^ 2 =
      (∑ i : Fin (r + 1), x i) ^ 2 / ((r + 1 : ℕ) : ℝ) := by
    rw [hcoordinate, div_pow, Real.sq_sqrt (by positivity :
      0 ≤ ((r + 1 : ℕ) : ℝ))]
  rw [centeredCovariateSqSum_eq_sub_meanSq (by omega) x]
  unfold covariateSqSum
  rw [← hnorm, ← hcoordSq, ← htail]
  rfl

private lemma measurable_dropFirst (r : ℕ) :
    Measurable (dropFirst (r := r)) := by
  rw [measurable_pi_iff]
  intro j
  exact (measurable_pi_apply ((0 : Fin (r + 1)).succAbove j)).comp
    (WithLp.measurable_ofLp 2 (Fin (r + 1) → ℝ))

private lemma iid_gaussian_reflected_drop_first (r : ℕ) :
    (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
      (fun x => dropFirst (centeredReflection r (WithLp.toLp 2 x))) =
      Measure.pi (fun _ : Fin r => centeredDesignGaussian) := by
  let E := EuclideanSpace ℝ (Fin (r + 1))
  let R := centeredReflection r
  let T : E → (Fin r → ℝ) := dropFirst (r := r)
  have hT : (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
      (fun x => T (R (WithLp.toLp 2 x))) =
      Measure.pi (fun _ : Fin r => centeredDesignGaussian) := by
    have htail : (ProbabilityTheory.stdGaussian E).map T =
        Measure.pi (fun _ : Fin r => centeredDesignGaussian) := by
      rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
      calc
        _ = (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
            (T ∘ WithLp.toLp 2) :=
          Measure.map_map (measurable_dropFirst r)
            (WithLp.measurable_toLp 2 (Fin (r + 1) → ℝ))
        _ = (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
            (rawDropFirst (r := r)) := by
          exact congrArg (fun f =>
            (Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map f)
            (by
              funext x
              rfl)
        _ = Measure.pi (fun _ : Fin r => centeredDesignGaussian) :=
          iid_gaussian_drop_first r
    have hR : (ProbabilityTheory.stdGaussian E).map R =
        ProbabilityTheory.stdGaussian E := ProbabilityTheory.stdGaussian_map R
    calc
      _ = ((Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)).map
          (WithLp.toLp 2)).map (fun z => T (R z)) := by
        exact (Measure.map_map ((measurable_dropFirst r).comp
          (R.continuous.measurable))
          (WithLp.measurable_toLp 2 (Fin (r + 1) → ℝ))).symm
      _ = ((ProbabilityTheory.stdGaussian E).map R).map T := by
        rw [ProbabilityTheory.map_pi_eq_stdGaussian]
        exact (Measure.map_map (measurable_dropFirst r)
          R.continuous.measurable).symm
      _ = (ProbabilityTheory.stdGaussian E).map T := by rw [hR]
      _ = Measure.pi (fun _ : Fin r => centeredDesignGaussian) := htail
  simpa [T, R] using hT

private lemma olsCenteredDesign_eq_centeredCovariates {N : ℕ}
    (G : Fin N → ℝ × ℝ) :
    olsCenteredDesign G = centeredCovariateSqSum (fun i => (G i).1) := by
  rfl

/-- The centered Gaussian design sum of squares is the pushforward of `r`
independent standard Gaussian squares. -/
theorem olsCenteredDesign_gaussian_pushforward (r : ℕ) :
    (Measure.pi (fun _ : Fin (r + 1) =>
      (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)).prod
        (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))).map olsCenteredDesign =
    (Measure.pi (fun _ : Fin r => ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))).map
      (fun x => ∑ i : Fin r, (x i) ^ 2) := by
  let μpair := Measure.pi (fun _ : Fin (r + 1) =>
    centeredDesignGaussian.prod centeredDesignGaussian)
  let μcov := Measure.pi (fun _ : Fin (r + 1) => centeredDesignGaussian)
  let π : (Fin (r + 1) → ℝ × ℝ) → (Fin (r + 1) → ℝ) :=
    fun G i => (G i).1
  let C : (Fin (r + 1) → ℝ) → ℝ := centeredCovariateSqSum
  have hπ : μpair.map π = μcov := iid_pair_covariate_marginal (r + 1)
  have htrans : μcov.map (fun x => covariateSqSum (dropFirst
      (centeredReflection r (WithLp.toLp 2 x)))) =
      (Measure.pi (fun _ : Fin r => centeredDesignGaussian)).map covariateSqSum := by
    calc
      _ = (μcov.map (fun x => dropFirst
          (centeredReflection r (WithLp.toLp 2 x)))).map covariateSqSum := by
        exact (Measure.map_map measurable_covariateSqSum
          (((measurable_dropFirst r).comp
            (centeredReflection r).continuous.measurable).comp
            (WithLp.measurable_toLp 2 (Fin (r + 1) → ℝ)))).symm
      _ = (Measure.pi (fun _ : Fin r => centeredDesignGaussian)).map
          covariateSqSum := by
        simpa [μcov] using congrArg
          (fun ν => ν.map covariateSqSum) (iid_gaussian_reflected_drop_first r)
  calc
    μpair.map olsCenteredDesign = μpair.map (C ∘ π) := by
      apply congrArg (fun f => μpair.map f)
      funext G
      dsimp [C, π]
      exact olsCenteredDesign_eq_centeredCovariates G
    _ = (μpair.map π).map C := by
      rw [Measure.map_map (by unfold C centeredCovariateSqSum; fun_prop)
        (by
          rw [measurable_pi_iff]
          intro i
          exact measurable_fst.comp (measurable_pi_apply i))]
      
    _ = μcov.map C := by rw [hπ]
    _ = μcov.map (covariateSqSum ∘ fun x => dropFirst
        (centeredReflection r (WithLp.toLp 2 x))) := by
      congr 1
      funext x
      exact reflection_centering_identity r x
    _ = (Measure.pi (fun _ : Fin r => centeredDesignGaussian)).map covariateSqSum := htrans

end LOOConcentration
