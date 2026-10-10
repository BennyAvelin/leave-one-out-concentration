import LOOConcentration.Concentration.NormTruncationSlope
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp

/-!
# Frozen Euclidean local slope of the squared-norm truncation

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version).
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

private theorem continuous_datasetToEuclidean_energy {k m N : ℕ} :
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

private theorem continuousAt_datasetNorm_sub_energy {k m N : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation (k + 1) (m + 1)) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean_energy.comp (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    rw [datasetNorm_eq_euclidean, show datasetToEuclidean (E - D) =
        datasetToEuclidean E - datasetToEuclidean D by
          apply PiLp.ext
          intro q
          rcases q with ⟨i, c⟩
          cases c <;> simp [datasetToEuclidean]]
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

private theorem datasetNormSq_sub_abs_le {k m n : ℕ}
    (D E : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    |datasetNormSq E - datasetNormSq D| ≤
      datasetNorm (E - D) * (datasetNorm E + datasetNorm D) := by
  have hsqE := datasetNorm_sq E
  have hsqD := datasetNorm_sq D
  have hnormdiff : |datasetNorm E - datasetNorm D| ≤ datasetNorm (E - D) := by
    rw [datasetNorm_eq_euclidean (E - D),
      show datasetToEuclidean (E - D) =
          datasetToEuclidean E - datasetToEuclidean D by
        apply PiLp.ext
        intro q
        rcases q with ⟨i, c⟩
        cases c <;> simp [datasetToEuclidean],
      datasetNorm_eq_euclidean E, datasetNorm_eq_euclidean D]
    exact abs_norm_sub_norm_le _ _
  rw [← hsqE, ← hsqD]
  have hfactor : datasetNorm E ^ 2 - datasetNorm D ^ 2 =
      (datasetNorm E - datasetNorm D) * (datasetNorm E + datasetNorm D) := by ring
  have hnormE : 0 ≤ datasetNorm E := Real.sqrt_nonneg _
  have hnormD : 0 ≤ datasetNorm D := Real.sqrt_nonneg _
  rw [hfactor, abs_mul, abs_of_nonneg (add_nonneg hnormE hnormD)]
  exact mul_le_mul_of_nonneg_right hnormdiff (add_nonneg hnormE hnormD)

private theorem truncationScalar_abs_sub_le {A x y : ℝ} (hA : 0 < A) :
    |A * (1 - Real.exp (-y / A)) - A * (1 - Real.exp (-x / A))| ≤
      Real.exp (-min x y / A) * |y - x| := by
  rcases le_total x y with hxy | hyx
  · have hδ : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hδA : 0 ≤ (y - x) / A := div_nonneg hδ hA.le
    have hexpδ : Real.exp (-(y - x) / A) ≤ 1 := by
      calc
        Real.exp (-(y - x) / A) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hA.le)
        _ = 1 := by simp
    have hsmall' : 1 - Real.exp (-((y - x) / A)) ≤ (y - x) / A := by
      have h := Real.add_one_le_exp (-((y - x) / A))
      linarith
    have hsmall : 1 - Real.exp (-(y - x) / A) ≤ (y - x) / A := by
      simpa only [neg_div] using hsmall'
    have hexp : Real.exp (-x / A) * Real.exp (-(y - x) / A) =
        Real.exp (-y / A) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hfac : A * (1 - Real.exp (-y / A)) - A * (1 - Real.exp (-x / A)) =
        A * Real.exp (-x / A) * (1 - Real.exp (-(y - x) / A)) := by
      rw [← hexp]
      ring
    have hnonneg : 0 ≤ A * Real.exp (-x / A) *
        (1 - Real.exp (-(y - x) / A)) :=
      mul_nonneg (mul_nonneg hA.le (Real.exp_nonneg _)) (sub_nonneg.mpr hexpδ)
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg hA.le (Real.exp_nonneg (-x / A)))
    have hcancel : A * Real.exp (-x / A) * ((y - x) / A) =
        Real.exp (-x / A) * (y - x) := by
      field_simp [hA.ne']
    rw [hfac, abs_of_nonneg hnonneg, min_eq_left hxy, abs_of_nonneg hδ]
    calc
      A * Real.exp (-x / A) * (1 - Real.exp (-(y - x) / A)) ≤
          A * Real.exp (-x / A) * ((y - x) / A) := hmul
      _ = Real.exp (-x / A) * (y - x) := hcancel
  · have hδ : 0 ≤ x - y := sub_nonneg.mpr hyx
    have hδA : 0 ≤ (x - y) / A := div_nonneg hδ hA.le
    have hexpδ : Real.exp (-(x - y) / A) ≤ 1 := by
      calc
        Real.exp (-(x - y) / A) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hA.le)
        _ = 1 := by simp
    have hsmall' : 1 - Real.exp (-((x - y) / A)) ≤ (x - y) / A := by
      have h := Real.add_one_le_exp (-((x - y) / A))
      linarith
    have hsmall : 1 - Real.exp (-(x - y) / A) ≤ (x - y) / A := by
      simpa only [neg_div] using hsmall'
    have hexp : Real.exp (-y / A) * Real.exp (-(x - y) / A) =
        Real.exp (-x / A) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hfac : A * (1 - Real.exp (-y / A)) - A * (1 - Real.exp (-x / A)) =
        -(A * Real.exp (-y / A) * (1 - Real.exp (-(x - y) / A))) := by
      rw [← hexp]
      ring
    have hnonneg : 0 ≤ A * Real.exp (-y / A) *
        (1 - Real.exp (-(x - y) / A)) :=
      mul_nonneg (mul_nonneg hA.le (Real.exp_nonneg _)) (sub_nonneg.mpr hexpδ)
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg hA.le (Real.exp_nonneg (-y / A)))
    have hcancel : A * Real.exp (-y / A) * ((x - y) / A) =
        Real.exp (-y / A) * (x - y) := by
      field_simp [hA.ne']
    rw [hfac, abs_neg, abs_of_nonneg hnonneg, min_eq_right hyx, abs_of_nonpos (sub_nonpos.mpr hyx)]
    calc
      A * Real.exp (-y / A) * (1 - Real.exp (-(x - y) / A)) ≤
          A * Real.exp (-y / A) * ((x - y) / A) := hmul
      _ = Real.exp (-y / A) * (x - y) := hcancel
      _ = Real.exp (-y / A) * -(y - x) := by rw [show x - y = -(y - x) by ring]

private theorem normTruncation_abs_sub_le {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D E : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    |normTruncation A hA E - normTruncation A hA D| ≤
      Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) *
        |datasetNormSq E - datasetNormSq D| := by
  unfold normTruncation
  simpa [min_comm, abs_sub_comm] using
    (truncationScalar_abs_sub_le (A := A) (x := datasetNormSq D)
      (y := datasetNormSq E) hA)

private theorem normTruncation_localLip_data {k m n : ℕ} {A : ℝ} (hA : 0 < A) :
    ∀ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
      ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |normTruncation A hA E - normTruncation A hA F| ≤ C * datasetNorm (E - F) := by
  intro D
  let U : Set (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    {E | datasetNorm (E - D) < 1}
  have hzero : datasetNorm (D - D) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
    (continuousAt_datasetNorm_sub_energy D) 1 (by norm_num)
  have hU : U ∈ 𝓝 D := by
    have hev : ∀ᶠ E in 𝓝 D, E ∈ U := by
      filter_upwards [Metric.ball_mem_nhds D hη] with E hE
      have hsmall := hηbound hE
      have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      change datasetNorm (E - D) < 1
      rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hsmall
      exact hsmall
    exact hev
  refine ⟨U, hU, 2 * (datasetNorm D + 1), ?_, ?_⟩
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
  · intro E hE F hF
    change datasetNorm (E - D) < 1 at hE
    change datasetNorm (F - D) < 1 at hF
    have hnormE : datasetNorm E ≤ datasetNorm D + 1 := by
      have hadd : D + (E - D) = E := by module
      calc
        datasetNorm E = datasetNorm (D + (E - D)) := by rw [hadd]
        _ ≤ datasetNorm D + datasetNorm (E - D) := datasetNorm_add_le _ _
        _ ≤ datasetNorm D + 1 := by nlinarith [hE.le]
    have hnormF : datasetNorm F ≤ datasetNorm D + 1 := by
      have hadd : D + (F - D) = F := by module
      calc
        datasetNorm F = datasetNorm (D + (F - D)) := by rw [hadd]
        _ ≤ datasetNorm D + datasetNorm (F - D) := datasetNorm_add_le _ _
        _ ≤ datasetNorm D + 1 := by nlinarith [hF.le]
    have hsum : datasetNorm E + datasetNorm F ≤ 2 * (datasetNorm D + 1) := by
      linarith
    have hq := normTruncation_abs_sub_le hA F E
    have hs := datasetNormSq_sub_abs_le F E
    have hmin : 0 ≤ min (datasetNormSq E) (datasetNormSq F) :=
      le_min (datasetNormSq_nonneg E) (datasetNormSq_nonneg F)
    have hexp : Real.exp (-min (datasetNormSq E) (datasetNormSq F) / A) ≤ 1 := by
      have harg : -min (datasetNormSq E) (datasetNormSq F) / A ≤ 0 := by
        simpa only [neg_div] using
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hmin) hA.le)
      calc
        Real.exp (-min (datasetNormSq E) (datasetNormSq F) / A) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr harg
        _ = 1 := by simp
    calc
      |normTruncation A hA E - normTruncation A hA F| ≤
          Real.exp (-min (datasetNormSq E) (datasetNormSq F) / A) *
            |datasetNormSq E - datasetNormSq F| := hq
      _ ≤ Real.exp (-min (datasetNormSq E) (datasetNormSq F) / A) *
            (datasetNorm (E - F) * (datasetNorm E + datasetNorm F)) :=
          mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
      _ ≤ 1 * (datasetNorm (E - F) * (datasetNorm E + datasetNorm F)) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      _ ≤ (2 * (datasetNorm D + 1)) * datasetNorm (E - F) := by
        have hdist : 0 ≤ datasetNorm (E - F) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hsum hdist]

private noncomputable def normTruncationSlopeEnvelope {k m n : ℕ}
    (A : ℝ) (D E : Dataset (Observation (k + 1) (m + 1)) (n + 1)) : ℝ :=
  Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) *
    (datasetNorm E + datasetNorm D)

private theorem continuous_normTruncationSlopeEnvelope {k m n : ℕ}
    (A : ℝ) (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    ContinuousAt (normTruncationSlopeEnvelope A D) D := by
  have hS : Continuous (datasetNormSq :
      Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ) := by
    unfold datasetNormSq observationNormSq
    fun_prop
  have hN : Continuous (datasetNorm :
      Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ) := by
    have hcont := continuous_datasetToEuclidean_energy (k := k) (m := m) (N := n + 1)
    have heq : (datasetNorm :
        Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ) =
        fun E => ‖datasetToEuclidean E‖ := by
      funext E
      exact datasetNorm_eq_euclidean E
    rw [heq]
    exact continuous_norm.comp hcont
  have hmin : ContinuousAt (fun E => min (datasetNormSq E) (datasetNormSq D)) D :=
    hS.continuousAt.min continuousAt_const
  have hexp : ContinuousAt
      (fun E => Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A)) D :=
    Real.continuous_exp.continuousAt.comp (hmin.neg.div_const A)
  have hsum : ContinuousAt (fun E => datasetNorm E + datasetNorm D) D :=
    hN.continuousAt.add continuousAt_const
  change ContinuousAt (fun E =>
    Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) *
      (datasetNorm E + datasetNorm D)) D
  exact hexp.mul hsum

/-- The actual truncation has a locally Lipschitz witness in the frozen
unnormalized Euclidean dataset norm. -/
noncomputable def normTruncation_locallyLipschitz {k m n : ℕ} {A : ℝ} (hA : 0 < A) :
    {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)} :=
  ⟨normTruncation A hA, normTruncation_localLip_data hA⟩

/-- The squared local slope of the bounded squared-norm truncation is
controlled by the truncation itself, including at the origin. -/
theorem normTruncation_localSlope_sq_le {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    (datasetLocalSlope (normTruncation_locallyLipschitz hA) D) ^ 2 ≤
      4 * normTruncation A hA D := by
  let f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)} :=
    normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA
  let q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ :=
    fun E => |f.1 E - f.1 D| / datasetNorm (E - D)
  have hquotBound : ∀ᶠ E in 𝓝[≠] D,
      q E ≤ normTruncationSlopeEnvelope A D E := by
    filter_upwards [self_mem_nhdsWithin] with E hne
    have hne' : E ≠ D := by simpa using hne
    have hden : 0 < datasetNorm (E - D) := datasetNorm_sub_pos hne'
    have hq := normTruncation_abs_sub_le hA D E
    have hs := datasetNormSq_sub_abs_le D E
    have hmin : 0 ≤ min (datasetNormSq E) (datasetNormSq D) :=
      le_min (datasetNormSq_nonneg E) (datasetNormSq_nonneg D)
    have hexp : 0 ≤ Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) :=
      (Real.exp_pos _).le
    change |normTruncation A hA E - normTruncation A hA D| /
        datasetNorm (E - D) ≤ _
    rw [normTruncationSlopeEnvelope]
    exact (div_le_iff₀ hden).2 (by
      calc
        |normTruncation A hA E - normTruncation A hA D| ≤
            Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) *
              (datasetNorm (E - D) * (datasetNorm E + datasetNorm D)) :=
          le_trans hq (mul_le_mul_of_nonneg_left hs hexp)
        _ = (Real.exp (-min (datasetNormSq E) (datasetNormSq D) / A) *
              (datasetNorm E + datasetNorm D)) * datasetNorm (E - D) := by ring)
  have hbounded := datasetSlope_bounded f D
  have henvelopeTendsto : Tendsto (normTruncationSlopeEnvelope A D)
      (𝓝 D) (𝓝 (normTruncationSlopeEnvelope A D D)) :=
    (continuous_normTruncationSlopeEnvelope A D).tendsto
  have henvelopeTendsto' : Tendsto (normTruncationSlopeEnvelope A D)
      (𝓝[≠] D) (𝓝 (normTruncationSlopeEnvelope A D D)) :=
    henvelopeTendsto.mono_left nhdsWithin_le_nhds
  have hSlopeLe : datasetLocalSlope f D ≤ normTruncationSlopeEnvelope A D D := by
    change limsup q (𝓝[≠] D) ≤ _
    rw [limsup_le_iff (datasetSlope_cobounded f D) hbounded]
    intro y hy
    have hpos : 0 < y - normTruncationSlopeEnvelope A D D := by linarith
    have heventually : ∀ᶠ E in 𝓝[≠] D,
        normTruncationSlopeEnvelope A D E < y := by
      simpa only [Set.mem_ofPred_eq] using
        henvelopeTendsto'.eventually (Iio_mem_nhds hy)
    filter_upwards [hquotBound, heventually] with E hqE hEnvE
    exact lt_of_le_of_lt hqE hEnvE
  have hSlopeNonneg := datasetLocalSlope_nonneg f D
  have hEnvelopeNonneg : 0 ≤ normTruncationSlopeEnvelope A D D := by
    dsimp [normTruncationSlopeEnvelope]
    exact mul_nonneg (Real.exp_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hSqLe : (datasetLocalSlope f D) ^ 2 ≤
      (normTruncationSlopeEnvelope A D D) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hSlopeLe)
      (add_nonneg hSlopeNonneg hEnvelopeNonneg)
    nlinarith [hprod]
  have hEnvelopeSq : (normTruncationSlopeEnvelope A D D) ^ 2 =
      4 * datasetNormSq D * Real.exp (-2 * datasetNormSq D / A) := by
    dsimp [normTruncationSlopeEnvelope]
    simp only [min_self]
    have hexp : (Real.exp (-datasetNormSq D / A)) ^ 2 =
        Real.exp (-2 * datasetNormSq D / A) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [show datasetNorm D + datasetNorm D = 2 * datasetNorm D by ring]
    rw [mul_pow, hexp]
    rw [show (2 * datasetNorm D) ^ 2 = 4 * datasetNorm D ^ 2 by ring]
    rw [datasetNorm_sq D]
    ring
  have ht : 0 ≤ datasetNormSq D / A := div_nonneg (datasetNormSq_nonneg D) hA.le
  have hscalar := normTruncation_scalar_slope_ineq ht
  have hscaled := mul_le_mul_of_nonneg_left hscalar (by positivity : 0 ≤ 4 * A)
  have hleft : 4 * A * ((datasetNormSq D / A) *
      Real.exp (-2 * (datasetNormSq D / A))) =
      4 * datasetNormSq D * Real.exp (-2 * datasetNormSq D / A) := by
    field_simp [hA.ne']
  have hright : 4 * A * (1 - Real.exp (-(datasetNormSq D / A))) =
      4 * normTruncation A hA D := by
    rw [normTruncation, neg_div]
    ring
  calc
    (datasetLocalSlope f D) ^ 2 ≤
        (normTruncationSlopeEnvelope A D D) ^ 2 := hSqLe
    _ = 4 * datasetNormSq D * Real.exp (-2 * datasetNormSq D / A) := hEnvelopeSq
    _ = 4 * A * ((datasetNormSq D / A) *
        Real.exp (-2 * (datasetNormSq D / A))) := hleft.symm
    _ ≤ 4 * A * (1 - Real.exp (-(datasetNormSq D / A))) := hscaled
    _ = 4 * normTruncation A hA D := hright

/-- At the zero dataset the frozen local slope of the truncation is zero. -/
theorem normTruncation_localSlope_zero {k m n : ℕ} {A : ℝ} (hA : 0 < A) :
    datasetLocalSlope (normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA)
      (0 : Dataset (Observation (k + 1) (m + 1)) (n + 1)) = 0 := by
  have hnonneg := datasetLocalSlope_nonneg
    (normTruncation_locallyLipschitz (k := k) (m := m) (n := n) hA)
    (0 : Dataset (Observation (k + 1) (m + 1)) (n + 1))
  have hsquare := normTruncation_localSlope_sq_le hA
    (0 : Dataset (Observation (k + 1) (m + 1)) (n + 1))
  rw [normTruncation_zero hA] at hsquare
  nlinarith

end LOOConcentration
