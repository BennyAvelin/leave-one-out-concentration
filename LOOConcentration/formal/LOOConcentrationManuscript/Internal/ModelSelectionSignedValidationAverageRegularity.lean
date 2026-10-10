import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Gradient

/-- The average of a query function over the original ordered dataset carrier. -/
noncomputable def originalQueryValidationAverage {k m N : ℕ}
    (f : LOOConcentration.Observation k m → ℝ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, f (D i)

private theorem regular_of_segment_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x-y‖ * (a + b / 2 * (‖x‖ + ‖y‖))) :
    LocallyLipschitz F ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
        DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ a + b * ‖x‖ := by
  have hlocal : LocallyLipschitz F := by
    intro x
    let K : ℝ := a + b * (‖x‖ + 1)
    refine ⟨Real.toNNReal K, Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
    apply LipschitzOnWith.of_dist_le'
    intro u hu v hv
    have huNorm : ‖u‖ ≤ ‖x‖ + 1 := by
      have hdist : dist u x < 1 := Metric.mem_ball.mp hu
      calc
        ‖u‖ = ‖(u-x)+x‖ := by congr 1; abel
        _ ≤ ‖u-x‖ + ‖x‖ := norm_add_le _ _
        _ = dist u x + ‖x‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖x‖ := by linarith
        _ = ‖x‖ + 1 := by ring
    have hvNorm : ‖v‖ ≤ ‖x‖ + 1 := by
      have hdist : dist v x < 1 := Metric.mem_ball.mp hv
      calc
        ‖v‖ = ‖(v-x)+x‖ := by congr 1; abel
        _ ≤ ‖v-x‖ + ‖x‖ := norm_add_le _ _
        _ = dist v x + ‖x‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖x‖ := by linarith
        _ = ‖x‖ + 1 := by ring
    have hcoef : a + b / 2 * (‖u‖ + ‖v‖) ≤ K := by
      dsimp [K]
      calc
        a + b / 2 * (‖u‖ + ‖v‖) ≤ a + b / 2 * (2 * (‖x‖ + 1)) := by gcongr; linarith
        _ = a + b * (‖x‖ + 1) := by ring
    have h := hseg u v
    have hd : dist (F u) (F v) ≤ K * dist u v := by
      rw [Real.dist_eq, dist_eq_norm]
      calc
        |F u-F v| ≤ ‖u-v‖ * (a+b/2*(‖u‖+‖v‖)) := h
        _ ≤ ‖u-v‖ * K := mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)
        _ = K * dist u v := by rw [dist_eq_norm]; ring
    exact hd
  have hgradPoint (x : EuclideanSpace ℝ ι) : ‖gradient F x‖ ≤ a+b*‖x‖ := by
    have hderivε : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ F x‖ ≤ a+b*‖x‖+ε := by
      intro ε hε
      let δ : ℝ := ε/(b+1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      have hbδ : b*δ ≤ ε := by
        calc
          b*δ ≤ (b+1)*δ := by gcongr; linarith
          _ = ε := by dsimp [δ]; field_simp
      have hhalf : b/2*δ ≤ ε := by nlinarith [mul_nonneg hb (le_of_lt hδ)]
      apply norm_fderiv_le_of_lip' ℝ (by positivity)
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      have hyNorm : ‖y‖ ≤ ‖x‖+δ := by
        have hd : dist y x < δ := Metric.mem_ball.mp hy
        calc
          ‖y‖ = ‖(y-x)+x‖ := by congr 1; abel
          _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
          _ = dist y x+‖x‖ := by rw [dist_eq_norm]
          _ ≤ δ+‖x‖ := by linarith
          _ = ‖x‖+δ := by ring
      have hcoef : a+b/2*(‖x‖+‖y‖) ≤ a+b*‖x‖+ε := by
        calc
          a+b/2*(‖x‖+‖y‖) ≤ a+b/2*(‖x‖+(‖x‖+δ)) := by gcongr
          _ = a+b*‖x‖+b/2*δ := by ring
          _ ≤ a+b*‖x‖+ε := by linarith
      have h := hseg y x
      calc
        ‖F y-F x‖ = |F y-F x| := Real.norm_eq_abs _
        _ ≤ ‖y-x‖*(a+b/2*(‖y‖+‖x‖)) := by simpa [add_comm] using h
        _ ≤ (a+b*‖x‖+ε)*‖y-x‖ := by
          calc
            ‖y-x‖*(a+b/2*(‖y‖+‖x‖)) ≤ ‖y-x‖*(a+b*‖x‖+ε) :=
              mul_le_mul_of_nonneg_left (by simpa [add_comm] using hcoef) (norm_nonneg _)
            _ = _ := by ring
    have hfd : ‖fderiv ℝ F x‖ ≤ a+b*‖x‖ := le_of_forall_pos_le_add hderivε
    calc
      ‖gradient F x‖ = ‖fderiv ℝ F x‖ := by
        rw [gradient, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
      _ ≤ a+b*‖x‖ := hfd
  have hae := LOOConcentration.Revision.locallyLipschitz_ae_differentiableAt F hlocal
  refine ⟨hlocal, ?_⟩
  filter_upwards [hae] with x hx
  exact ⟨hx, hgradPoint x⟩

private theorem norm_observation_array {N k m : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :
    ‖(WithLp.toLp 2 (fun i : Fin N => LOOConcentration.observationNorm (D i)) :
      EuclideanSpace ℝ (Fin N))‖ = LOOConcentration.datasetNorm D := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [LOOConcentration.datasetNormSq, LOOConcentration.observationNorm_sq,
    Real.norm_eq_abs, sq_abs]

private theorem norm_real_pi_sq {N : ℕ} (f : Fin N → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin N))‖ ^ 2 = ∑ i, f i ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (f i))

private theorem sum_cauchy_bound {N : ℕ} (u v : Fin N → ℝ) :
    (∑ i, u i * v i) ≤
      Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  simpa using
    (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin N)) u v)

private theorem observation_array_diff_sum_bound {N k m : ℕ}
    (D E : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :
    (∑ i, LOOConcentration.observationNorm (D i-E i)) ≤
      Real.sqrt (N : ℝ) * LOOConcentration.datasetNorm (D-E) := by
  let u : Fin N → ℝ := fun i => LOOConcentration.observationNorm (D i-E i)
  have hcs := sum_cauchy_bound (fun _ : Fin N => (1:ℝ)) u
  have hsq : (∑ i, u i ^ 2) = LOOConcentration.datasetNorm (D-E)^2 := by
    rw [LOOConcentration.datasetNorm_sq]
    simp [u, LOOConcentration.datasetNormSq, LOOConcentration.observationNorm_sq]
  have hn : 0 ≤ LOOConcentration.datasetNorm (D-E) := Real.sqrt_nonneg _
  calc
    (∑ i, LOOConcentration.observationNorm (D i-E i)) = ∑ i, (1:ℝ)*u i := by simp [u]
    _ ≤ Real.sqrt (∑ i, (1:ℝ)^2) * Real.sqrt (∑ i, u i^2) := hcs
    _ = Real.sqrt (N:ℝ) * LOOConcentration.datasetNorm (D-E) := by
      rw [show (∑ i : Fin N, (1:ℝ)^2) = (N:ℝ) by simp, hsq,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hn]

private theorem observation_array_sum_bound {N k m : ℕ}
    (D E : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :
    Real.sqrt (∑ i, (LOOConcentration.observationNorm (D i) +
      LOOConcentration.observationNorm (E i)) ^ 2) ≤
        LOOConcentration.datasetNorm D + LOOConcentration.datasetNorm E := by
  let p : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun i => LOOConcentration.observationNorm (D i))
  let q : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun i => LOOConcentration.observationNorm (E i))
  have hp : ‖p‖ = LOOConcentration.datasetNorm D := by
    simpa [p] using norm_observation_array D
  have hq : ‖q‖ = LOOConcentration.datasetNorm E := by
    simpa [q] using norm_observation_array E
  have hsum : (∑ i, (LOOConcentration.observationNorm (D i) +
      LOOConcentration.observationNorm (E i)) ^ 2) = ‖p+q‖ ^ 2 := by
    rw [norm_real_pi_sq]
    simp [p, q]
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖p+q‖ ≤ ‖p‖+‖q‖ := norm_add_le _ _
    _ = LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E := by rw [hp,hq]

private theorem observation_array_weighted_sum_bound {N k m : ℕ}
    (D E : LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :
    (∑ i, LOOConcentration.observationNorm (D i-E i) *
      (LOOConcentration.observationNorm (D i)+LOOConcentration.observationNorm (E i))) ≤
      LOOConcentration.datasetNorm (D-E) *
        (LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E) := by
  let u : Fin N → ℝ := fun i => LOOConcentration.observationNorm (D i-E i)
  let v : Fin N → ℝ := fun i => LOOConcentration.observationNorm (D i)+
    LOOConcentration.observationNorm (E i)
  have hcs := sum_cauchy_bound u v
  have hsq : (∑ i, u i ^ 2) = LOOConcentration.datasetNorm (D-E)^2 := by
    rw [LOOConcentration.datasetNorm_sq]
    simp [u, LOOConcentration.datasetNormSq, LOOConcentration.observationNorm_sq]
  have hdn : 0 ≤ LOOConcentration.datasetNorm (D-E) := Real.sqrt_nonneg _
  have hu : Real.sqrt (∑ i, u i^2) = LOOConcentration.datasetNorm (D-E) := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hdn]
  have hv : Real.sqrt (∑ i, v i^2) ≤
      LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E := by
    simpa [v] using observation_array_sum_bound D E
  calc
    (∑ i, LOOConcentration.observationNorm (D i-E i) *
      (LOOConcentration.observationNorm (D i)+LOOConcentration.observationNorm (E i))) =
        ∑ i, u i*v i := by simp [u,v]
    _ ≤ Real.sqrt (∑ i, u i^2)*Real.sqrt (∑ i, v i^2) := hcs
    _ ≤ LOOConcentration.datasetNorm (D-E) *
        (LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E) := by
      rw [hu]
      exact mul_le_mul_of_nonneg_left hv hdn

private theorem original_query_average_segment_bound
    {k m N : ℕ} (f : LOOConcentration.Observation k m → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hlocal : LocallyLipschitz
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)))
    (hgrad : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
          (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c + d * ‖z‖)
    (x y : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N)) :
    |originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean x) -
      originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean y)| ≤
      ‖x-y‖ * (c/Real.sqrt (N:ℝ) + d/(2*(N:ℝ))*(‖x‖+‖y‖)) := by
  let D := LOOConcentration.Revision.datasetOfEuclidean x
  let E := LOOConcentration.Revision.datasetOfEuclidean y
  let u : Fin N → ℝ := fun i => LOOConcentration.observationNorm (D i-E i)
  let v : Fin N → ℝ := fun i => LOOConcentration.observationNorm (D i)+
    LOOConcentration.observationNorm (E i)
  let q : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) → ℝ :=
    fun z => f (LOOConcentration.Revision.observationOfEuclidean z)
  have hquery (a b : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m)) :
      |q a-q b| ≤ ‖a-b‖*(c+d/2*(‖a‖+‖b‖)) := by
    have hgrad' : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
        DifferentiableAt ℝ q z ∧ ‖gradient q z‖ ≤
          (Real.toNNReal c : ℝ)+(Real.toNNReal d : ℝ)*‖z‖ := by
      filter_upwards [hgrad] with z hz
      simpa [q, Real.coe_toNNReal _ hc, Real.coe_toNNReal _ hd] using hz
    have h := LOOConcentration.Revision.Providers.ae_gradient_segment_estimate
      q hlocal (Real.toNNReal c) (Real.toNNReal d) hgrad' a b
    simpa [q, Real.coe_toNNReal _ hc, Real.coe_toNNReal _ hd] using h
  have hpoint (i : Fin N) : |f (D i)-f (E i)| ≤ u i*(c+d/2*v i) := by
    have hmap : LOOConcentration.observationToEuclidean (D i-E i) =
        LOOConcentration.observationToEuclidean (D i)-
          LOOConcentration.observationToEuclidean (E i) := by
      apply PiLp.ext
      intro q
      cases q <;> simp [LOOConcentration.observationToEuclidean]
    have hs := hquery (LOOConcentration.observationToEuclidean (D i))
      (LOOConcentration.observationToEuclidean (E i))
    simpa [u,v,q, LOOConcentration.Revision.observationOfEuclidean_observationToEuclidean,
      LOOConcentration.observationNorm_eq_euclidean, hmap] using hs
  have hsum_abs :
      |∑ i : Fin N, (f (D i)-f (E i))| ≤ ∑ i : Fin N, |f (D i)-f (E i)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      (∑ i : Fin N, |f (D i)-f (E i)|) ≤
        c*(∑ i, u i)+d/2*(∑ i, u i*v i) := by
    calc
      _ ≤ ∑ i : Fin N, u i*(c+d/2*v i) := Finset.sum_le_sum fun i hi => hpoint i
      _ = c*(∑ i, u i)+d/2*(∑ i, u i*v i) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · calc
            (∑ i, u i*c) = (∑ i, u i)*c := by rw [Finset.sum_mul]
            _ = c*(∑ i, u i) := by ring
        · calc
            (∑ i, u i*(d/2*v i)) = ∑ i, (d/2)*(u i*v i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = d/2*(∑ i, u i*v i) := by rw [Finset.mul_sum]
  have hsum_u := observation_array_diff_sum_bound D E
  have hsum_uv := observation_array_weighted_sum_bound D E
  have hsum_u' : (∑ i : Fin N, u i) ≤
      Real.sqrt (N:ℝ)*LOOConcentration.datasetNorm (D-E) := by simpa [u] using hsum_u
  have hsum_uv' : (∑ i : Fin N, u i*v i) ≤
      LOOConcentration.datasetNorm (D-E)*
        (LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E) := by
    simpa [u,v] using hsum_uv
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hscale : 0 ≤ (1/(N:ℝ)) := by positivity
  have hDEnorm : LOOConcentration.datasetNorm (D-E) = ‖x-y‖ := by
    rw [LOOConcentration.datasetNorm_eq_euclidean]
    apply congrArg norm
    apply PiLp.ext
    rintro ⟨i,q⟩
    cases q <;> simp [D,E,LOOConcentration.datasetToEuclidean,
      LOOConcentration.Revision.datasetOfEuclidean]
  dsimp [originalQueryValidationAverage]
  have havg :
      (1/(N:ℝ))*∑ i : Fin N, f (D i) - (1/(N:ℝ))*∑ i : Fin N, f (E i) =
        (1/(N:ℝ))*∑ i : Fin N, (f (D i)-f (E i)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [havg, abs_mul, abs_of_nonneg hscale]
  calc
    (1/(N:ℝ))*|∑ i : Fin N, (f (D i)-f (E i))| ≤
        (1/(N:ℝ))*(c*(∑ i, u i)+d/2*(∑ i, u i*v i)) :=
      mul_le_mul_of_nonneg_left (hsum_abs.trans hsum_bound) hscale
    _ ≤ (1/(N:ℝ))*(c*(Real.sqrt (N:ℝ)*LOOConcentration.datasetNorm (D-E))+
        d/2*(LOOConcentration.datasetNorm (D-E)*
          (LOOConcentration.datasetNorm D+LOOConcentration.datasetNorm E))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hsum_u' hc
      · exact mul_le_mul_of_nonneg_left hsum_uv' (by positivity)
    _ = ‖x-y‖*(c/Real.sqrt (N:ℝ)+
        d/(2*(N:ℝ))*(‖x‖+‖y‖)) := by
      rw [hDEnorm, LOOConcentration.Revision.datasetNorm_datasetOfEuclidean,
        LOOConcentration.Revision.datasetNorm_datasetOfEuclidean]
      field_simp
      have hsquare : Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ)=(N:ℝ) := by
        calc
          Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ) = Real.sqrt (N:ℝ)^2 := by ring
          _ = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
      linear_combination (2*c*‖x-y‖)*hsquare

/-- The original-carrier query average has the sharp validation-size gradient
bound from the query mean's own almost-everywhere gradient bound. -/
theorem originalQueryValidationAverage_euclidean_regular
    {k m N : ℕ} (f : LOOConcentration.Observation k m → ℝ)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hlocal : LocallyLipschitz
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)))
    (hgrad : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
          (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c+d*‖z‖) :
    LocallyLipschitz
        (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N) =>
          originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u)) ∧
      ∀ᵐ u ∂(volume : Measure
          (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N))),
        DifferentiableAt ℝ
          (fun v => originalQueryValidationAverage f
            (LOOConcentration.Revision.datasetOfEuclidean v)) u ∧
          ‖gradient (fun v => originalQueryValidationAverage f
            (LOOConcentration.Revision.datasetOfEuclidean v)) u‖ ≤
            c/Real.sqrt (N:ℝ)+d/(N:ℝ)*‖u‖ := by
  let F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N) → ℝ :=
    fun u => originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u)
  let a : ℝ := c/Real.sqrt (N:ℝ)
  let b : ℝ := d/(N:ℝ)
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.2 hNpos
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg hc hsqrt.le
  have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg hd hNpos.le
  have hseg : ∀ x y, |F x-F y| ≤ ‖x-y‖*(a+b/2*(‖x‖+‖y‖)) := by
    intro x y
    have h := original_query_average_segment_bound f c d hc hd hN hlocal hgrad x y
    have hcoef : d/(2*(N:ℝ)) = (d/(N:ℝ))/2 := by field_simp
    change |originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean x)-
      originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean y)| ≤ _
    rw [show a=c/Real.sqrt (N:ℝ) by rfl,
      show b=d/(N:ℝ) by rfl, ← hcoef]
    exact h
  have hregular := regular_of_segment_bound F a b ha hb hseg
  refine ⟨?_, ?_⟩
  · simpa [F] using hregular.1
  · simpa [F,a,b] using hregular.2

/-- With zero query-growth coefficient, the average is globally Lipschitz on
the original full dataset carrier at the exact rate c/sqrt(N). -/
theorem originalQueryValidationAverage_euclidean_lipschitz_of_zero_growth
    {k m N : ℕ} (f : LOOConcentration.Observation k m → ℝ)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hdzero : d = 0)
    (hlocal : LocallyLipschitz
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z)))
    (hgrad : ∀ᵐ z ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
          (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c+d*‖z‖) :
    LipschitzWith (Real.toNNReal (c/Real.sqrt (N:ℝ)))
      (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N) =>
        originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u)) := by
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have ha : 0 ≤ c/Real.sqrt (N:ℝ) := div_nonneg hc (Real.sqrt_nonneg _)
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  have hseg := original_query_average_segment_bound f c d hc hd hN hlocal hgrad x y
  have hseg' : |originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean x)-
      originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean y)| ≤
      (c/Real.sqrt (N:ℝ))*‖x-y‖ := by
    simpa [hdzero, mul_comm] using hseg
  have hcoe : (Real.toNNReal (c/Real.sqrt (N:ℝ)) : ℝ)=c/Real.sqrt (N:ℝ) :=
    Real.coe_toNNReal _ ha
  change |originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean x)-
    originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean y)| ≤ _
  simpa [hcoe, mul_comm] using hseg'

/-- A genuine query-coordinate c-Lipschitz bound also makes the original
validation average globally c/sqrt(N)-Lipschitz. -/
theorem originalQueryValidationAverage_euclidean_lipschitz_of_query_lipschitz
    {k m N : ℕ} (f : LOOConcentration.Observation k m → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hN : 1 ≤ N)
    (hqueryLip : LipschitzWith (Real.toNNReal c)
      (fun z : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m) =>
        f (LOOConcentration.Revision.observationOfEuclidean z))) :
    LipschitzWith (Real.toNNReal (c/Real.sqrt (N:ℝ)))
      (fun u : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N) =>
        originalQueryValidationAverage f (LOOConcentration.Revision.datasetOfEuclidean u)) := by
  have hlocal := hqueryLip.locallyLipschitz
  have hgrad₀ := LOOConcentration.Revision.lipschitzWith_ae_differentiableAt_gradient_norm_le hqueryLip
  have hgrad : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate k m))),
      DifferentiableAt ℝ
          (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z ∧
        ‖gradient (fun y => f (LOOConcentration.Revision.observationOfEuclidean y)) z‖ ≤
          c+0*‖z‖ := by
    filter_upwards [hgrad₀] with z hz
    exact ⟨hz.1, by simpa [Real.coe_toNNReal _ hc] using hz.2⟩
  exact originalQueryValidationAverage_euclidean_lipschitz_of_zero_growth
    f c 0 hc (le_rfl) hN rfl hlocal hgrad


end LOOConcentration.Manuscript.Internal
