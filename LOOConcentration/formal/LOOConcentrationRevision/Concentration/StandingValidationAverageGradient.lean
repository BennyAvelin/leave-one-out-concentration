import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory Filter
open scoped Gradient

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
  have hae := locallyLipschitz_ae_differentiableAt F hlocal
  refine ⟨hlocal, ?_⟩
  filter_upwards [hae] with x hx
  exact ⟨hx, hgradPoint x⟩

noncomputable def standingValidationAverage
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n+2)) : ℝ :=
  (1 / (n+2 : ℝ)) * ∑ i : Fin (n+2),
    meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))

private theorem norm_observation_array {N k m : ℕ}
    (D : Dataset (Observation k m) N) :
    ‖(WithLp.toLp 2 (fun i : Fin N => observationNorm (D i)) :
      EuclideanSpace ℝ (Fin N))‖ = datasetNorm D := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [datasetNormSq, observationNorm_sq, Real.norm_eq_abs, sq_abs]

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

private theorem observation_array_sq_sum {N k m : ℕ}
    (D : Dataset (Observation k m) N) :
    (∑ i, observationNorm (D i) ^ 2) = datasetNorm D ^ 2 := by
  rw [datasetNorm_sq]
  simp [datasetNormSq, observationNorm_sq]

private theorem diff_array_sq_sum {N k m : ℕ}
    (D E : Dataset (Observation k m) N) :
    (∑ i, observationNorm (D i - E i) ^ 2) = datasetNorm (D-E) ^ 2 := by
  exact observation_array_sq_sum (D-E)

private theorem observation_array_sum_bound {N k m : ℕ}
    (D E : Dataset (Observation k m) N) :
    Real.sqrt (∑ i, (observationNorm (D i) + observationNorm (E i)) ^ 2) ≤
      datasetNorm D + datasetNorm E := by
  let p : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun i => observationNorm (D i))
  let q : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun i => observationNorm (E i))
  have hp : ‖p‖ = datasetNorm D := by
    simpa [p] using norm_observation_array D
  have hq : ‖q‖ = datasetNorm E := by
    simpa [q] using norm_observation_array E
  have hsum : (∑ i, (observationNorm (D i) + observationNorm (E i)) ^ 2) =
      ‖p+q‖ ^ 2 := by
    rw [norm_real_pi_sq]
    simp [p, q]
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖p+q‖ ≤ ‖p‖+‖q‖ := norm_add_le _ _
    _ = datasetNorm D+datasetNorm E := by rw [hp,hq]

private theorem observation_array_diff_sum_bound {N k m : ℕ}
    (D E : Dataset (Observation k m) N) :
    (∑ i, observationNorm (D i-E i)) ≤
      Real.sqrt (N : ℝ) * datasetNorm (D-E) := by
  let u : Fin N → ℝ := fun i => observationNorm (D i-E i)
  have hcs := sum_cauchy_bound (fun _ : Fin N => (1:ℝ)) u
  have hsq : (∑ i, u i ^ 2) = datasetNorm (D-E)^2 := by
    simpa [u] using diff_array_sq_sum D E
  have hn : 0 ≤ datasetNorm (D-E) := Real.sqrt_nonneg _
  calc
    (∑ i, observationNorm (D i-E i)) = ∑ i, (1:ℝ)*u i := by simp [u]
    _ ≤ Real.sqrt (∑ i, (1:ℝ)^2) * Real.sqrt (∑ i, u i^2) := hcs
    _ = Real.sqrt (N:ℝ) * datasetNorm (D-E) := by
      rw [show (∑ i : Fin N, (1:ℝ)^2) = (N:ℝ) by simp, hsq,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hn]

private theorem observation_array_weighted_sum_bound {N k m : ℕ}
    (D E : Dataset (Observation k m) N) :
    (∑ i, observationNorm (D i-E i) *
      (observationNorm (D i)+observationNorm (E i))) ≤
      datasetNorm (D-E) * (datasetNorm D+datasetNorm E) := by
  let u : Fin N → ℝ := fun i => observationNorm (D i-E i)
  let v : Fin N → ℝ := fun i => observationNorm (D i)+observationNorm (E i)
  have hcs := sum_cauchy_bound u v
  have hsq : (∑ i, u i ^ 2) = datasetNorm (D-E)^2 := by
    simpa [u] using diff_array_sq_sum D E
  have hdn : 0 ≤ datasetNorm (D-E) := Real.sqrt_nonneg _
  have hu : Real.sqrt (∑ i, u i^2) = datasetNorm (D-E) := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hdn]
  have hv : Real.sqrt (∑ i, v i^2) ≤ datasetNorm D+datasetNorm E := by
    simpa [v] using observation_array_sum_bound D E
  calc
    (∑ i, observationNorm (D i-E i) *
      (observationNorm (D i)+observationNorm (E i))) = ∑ i, u i*v i := by simp [u,v]
    _ ≤ Real.sqrt (∑ i, u i^2)*Real.sqrt (∑ i, v i^2) := hcs
    _ ≤ datasetNorm (D-E)*(datasetNorm D+datasetNorm E) := by
      rw [hu]
      exact mul_le_mul_of_nonneg_left hv hdn

private theorem source_observation_segment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (x y : EuclideanSpace ℝ (ObservationCoordinate k m)) :
    |meanFittedLoss μ (T n) L (observationOfEuclidean x)
        (hSt.mean_integrable (observationOfEuclidean x)) -
      meanFittedLoss μ (T n) L (observationOfEuclidean y)
        (hSt.mean_integrable (observationOfEuclidean y))| ≤
      ‖x-y‖ * (c+d/2*(‖x‖+‖y‖)) := by
  let g : EuclideanSpace ℝ (ObservationCoordinate k m) → ℝ := fun z =>
    meanFittedLoss μ (T n) L (observationOfEuclidean z)
      (hSt.mean_integrable (observationOfEuclidean z))
  have hloc : LocallyLipschitz g := by
    simpa [g] using hSt.mean_locallyLipschitz
  have hgrad : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ g z ∧ ‖gradient g z‖ ≤
        (Real.toNNReal c : ℝ) + (Real.toNNReal d : ℝ) * ‖z‖ := by
    filter_upwards [hSt.mean_gradient] with z hz
    simpa [g, Real.coe_toNNReal _ hSt.c_nonneg,
      Real.coe_toNNReal _ hSt.d_nonneg] using hz
  have h := ae_gradient_segment_estimate g hloc (Real.toNNReal c)
    (Real.toNNReal d) hgrad x y
  simpa [g, Real.coe_toNNReal _ hSt.c_nonneg,
    Real.coe_toNNReal _ hSt.d_nonneg] using h

private theorem standing_validation_euclidean_segment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (x y : EuclideanSpace ℝ (DatasetCoordinate k m (n+2))) :
    |standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
      standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean y)| ≤
      ‖x-y‖ * (c / Real.sqrt (n+2:ℝ) +
        d/(2*(n+2:ℝ))*(‖x‖+‖y‖)) := by
  let D := datasetOfEuclidean x
  let E := datasetOfEuclidean y
  let u : Fin (n+2) → ℝ := fun i => observationNorm (D i-E i)
  let v : Fin (n+2) → ℝ := fun i => observationNorm (D i)+observationNorm (E i)
  have hpoint (i : Fin (n+2)) :
      |meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
        meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))| ≤
        u i*(c+d/2*v i) := by
    have hmap : observationToEuclidean (D i-E i) =
        observationToEuclidean (D i)-observationToEuclidean (E i) := by
      apply PiLp.ext
      intro q
      cases q <;> simp [observationToEuclidean]
    have hs := source_observation_segment μ T L δ₁ δ₂ δ₃ c d hSt
      (observationToEuclidean (D i)) (observationToEuclidean (E i))
    simpa [u,v,hmap, observationNorm_eq_euclidean] using hs
  have hsum_abs :
      |∑ i : Fin (n+2),
        (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
         meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i)))| ≤
        ∑ i : Fin (n+2),
        |meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
         meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      (∑ i : Fin (n+2),
        |meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
         meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i))|) ≤
        c*(∑ i, u i)+d/2*(∑ i, u i*v i) := by
    calc
      _ ≤ ∑ i : Fin (n+2), u i*(c+d/2*v i) :=
        Finset.sum_le_sum fun i hi => hpoint i
      _ = c*(∑ i, u i)+d/2*(∑ i, u i*v i) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · calc
            (∑ i, u i*c) = (∑ i, u i)*c := by rw [Finset.sum_mul]
            _ = c*(∑ i, u i) := by ring
        · calc
            (∑ i, u i*(d/2*v i)) =
                ∑ i, (d/2)*(u i*v i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = d/2*(∑ i, u i*v i) := by rw [Finset.mul_sum]
  have hsum_u := observation_array_diff_sum_bound D E
  have hsum_uv := observation_array_weighted_sum_bound D E
  have hsum_u' : (∑ i : Fin (n+2), u i) ≤
      Real.sqrt (n+2:ℝ)*datasetNorm (D-E) := by simpa [u] using hsum_u
  have hsum_uv' : (∑ i : Fin (n+2), u i*v i) ≤
      datasetNorm (D-E)*(datasetNorm D+datasetNorm E) := by simpa [u,v] using hsum_uv
  have hc : 0 ≤ c := hSt.c_nonneg
  have hd : 0 ≤ d := hSt.d_nonneg
  have hN : 0 < (n+2:ℝ) := by positivity
  have hscale : 0 ≤ (1/(n+2:ℝ)) := by positivity
  have hDEnorm : datasetNorm (D-E) = ‖x-y‖ := by
    rw [datasetNorm_eq_euclidean]
    apply congrArg norm
    apply PiLp.ext
    rintro ⟨i,q⟩
    cases q <;> simp [D,E,datasetToEuclidean,datasetOfEuclidean]
  dsimp [standingValidationAverage]
  have havg :
      (1/(n+2:ℝ)) *
          (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
            (hSt.mean_integrable (D i))) -
        (1/(n+2:ℝ)) *
          (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (E i)
            (hSt.mean_integrable (E i))) =
        (1/(n+2:ℝ)) * ∑ i : Fin (n+2),
          (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
           meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i)) ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [havg, abs_mul, abs_of_nonneg hscale]
  calc
    (1/(n+2:ℝ)) *
        |∑ i : Fin (n+2),
          (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
           meanFittedLoss μ (T n) L (E i) (hSt.mean_integrable (E i)))| ≤
        (1/(n+2:ℝ))*(c*(∑ i, u i)+d/2*(∑ i, u i*v i)) :=
      mul_le_mul_of_nonneg_left (hsum_abs.trans hsum_bound) hscale
    _ ≤ (1/(n+2:ℝ))*
        (c*(Real.sqrt (n+2:ℝ)*datasetNorm (D-E))+
          d/2*(datasetNorm (D-E)*(datasetNorm D+datasetNorm E))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hsum_u' hc
      · exact mul_le_mul_of_nonneg_left hsum_uv' (by positivity)
    _ = ‖x-y‖ * (c/Real.sqrt (n+2:ℝ)+
        d/(2*(n+2:ℝ))*(‖x‖+‖y‖)) := by
      rw [hDEnorm, datasetNorm_datasetOfEuclidean, datasetNorm_datasetOfEuclidean]
      field_simp
      have hsquare : Real.sqrt (n+2:ℝ)*Real.sqrt (n+2:ℝ)=(n+2:ℝ) := by
        calc
          Real.sqrt (n+2:ℝ)*Real.sqrt (n+2:ℝ) =
              Real.sqrt (n+2:ℝ)^2 := by ring
          _ = (n+2:ℝ) := Real.sq_sqrt (le_of_lt hN)
      linear_combination (2*c*‖x-y‖) * hsquare

theorem standing_validation_average_gradient
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    LocallyLipschitz
        (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) =>
          standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt
            (datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
        DifferentiableAt ℝ
          (fun y => standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt
            (datasetOfEuclidean y)) x ∧
          ‖gradient (fun y => standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt
            (datasetOfEuclidean y)) x‖ ≤
            c/Real.sqrt (n+2:ℝ)+d/(n+2:ℝ)*‖x‖ := by
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ := fun x =>
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
  let a : ℝ := c/Real.sqrt (n+2:ℝ)
  let b : ℝ := d/(n+2:ℝ)
  have hN : 0 < (n+2:ℝ) := by positivity
  have hc : 0 ≤ c := hSt.c_nonneg
  have hd : 0 ≤ d := hSt.d_nonneg
  have hsqrt : 0 < Real.sqrt (n+2:ℝ) := Real.sqrt_pos.2 hN
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg hc hsqrt.le
  have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg hd hN.le
  have hseg : ∀ x y, |F x-F y| ≤ ‖x-y‖*(a+b/2*(‖x‖+‖y‖)) := by
    intro x y
    have h := standing_validation_euclidean_segment μ T L δ₁ δ₂ δ₃ c d hSt x y
    have hcoef : d/(n+2:ℝ)/2 = d/(2*(n+2:ℝ)) := by field_simp
    change |standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt
      (datasetOfEuclidean x)-standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt
      (datasetOfEuclidean y)| ≤ _
    rw [show a=c/Real.sqrt (n+2:ℝ) by rfl,
      show b=d/(n+2:ℝ) by rfl, hcoef]
    exact h
  have hregular := regular_of_segment_bound F a b ha hb hseg
  refine ⟨?_, ?_⟩
  · simpa [F] using hregular.1
  · simpa [F,a,b] using hregular.2

/-! A zero-growth specialization of the source segment bound.  The Lipschitz
constant is produced from `hSt`; no separate regularity premise is needed. -/
theorem standing_validation_average_zero_growth_lipschitz
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hd : d = 0) :
    LipschitzWith (Real.toNNReal (c / Real.sqrt (n+2:ℝ)))
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) =>
        standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  have hseg := standing_validation_euclidean_segment μ T L δ₁ δ₂ δ₃ c d hSt x y
  have hL : (Real.toNNReal (c / Real.sqrt (n+2:ℝ)) : ℝ) =
      c / Real.sqrt (n+2:ℝ) :=
    Real.coe_toNNReal _ (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
  simpa [hd, hL, mul_comm] using hseg


end LOOConcentration.Revision
