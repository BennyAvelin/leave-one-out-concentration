import LOOConcentrationRevision.FunctionalInequalities.IntrinsicPoincareClosure
import LOOConcentrationRevision.FunctionalInequalities.MollifiedGradientGrowth
import LOOConcentrationRevision.FunctionalInequalities.MollifiedSmoothGenerator
import LOOConcentrationRevision.Analysis.CenteredFatouLimit
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LOOConcentration.Revision

private theorem integral_sq_eq_centered_add_mean_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    {F : EuclideanSpace ℝ ι → ℝ}
    (hF : Integrable F μ) (_hF2 : Integrable (fun x => F x ^ 2) μ)
    (hcenter : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ) :
    (∫ x, F x ^ 2 ∂μ) =
      (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) + (∫ x, F x ∂μ) ^ 2 := by
  let m : ℝ := ∫ x, F x ∂μ
  have hidentity : (fun x => F x ^ 2) =
      (fun x => (F x - m) ^ 2 + (2 * m) * F x - m ^ 2) := by
    funext x
    dsimp [m]
    ring
  rw [hidentity]
  have hsum : Integrable (fun x => (F x - m) ^ 2 + (2 * m) * F x) μ := by
    exact hcenter.add (hF.const_mul (2 * m))
  rw [integral_sub hsum (integrable_const (m ^ 2)), integral_add hcenter
    (hF.const_mul (2 * m)), integral_const_mul, integral_const]
  simp only [Measure.real, measure_univ, smul_eq_mul]
  dsimp [m]
  ring

/-- A positive-mass ball controls the mean using only a centered second-moment
bound. The measure, function, ball, and actual center are shared literally. -/
theorem mean_sq_le_of_centered_variance_ball
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ) (_hF : Integrable F μ)
    (r B V : ℝ) (hB : 0 ≤ B)
    (hball : 0 < μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r))
    (hbound : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) r, |F x| ≤ B)
    (hcenter : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ)
    (hvariance : (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤ V) :
    (∫ x, F x ∂μ) ^ 2 ≤
      2 * V / μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * B ^ 2 := by
  let K : Set (EuclideanSpace ℝ ι) := Metric.ball 0 r
  let g : EuclideanSpace ℝ ι → ℝ := K.indicator (fun _ => 1)
  let m : ℝ := ∫ x, F x ∂μ
  have hK : MeasurableSet K := by
    exact Metric.isOpen_ball.measurableSet
  have hg : Integrable g μ := by
    apply Integrable.of_bound (measurable_const.indicator hK).aestronglyMeasurable 1
    filter_upwards [] with x
    by_cases hx : x ∈ K <;> simp [hx]
  have hpoint (x : EuclideanSpace ℝ ι) :
      g x * m ^ 2 ≤ 2 * (F x - m) ^ 2 + 2 * g x * B ^ 2 := by
    by_cases hx : x ∈ K
    · have hFx := hbound x (by simpa [K] using hx)
      simp [g, K, hx, m]
      have hsquare : (∫ y, F y ∂μ) ^ 2 ≤
          2 * (F x - ∫ y, F y ∂μ) ^ 2 + 2 * F x ^ 2 := by
        nlinarith [sq_nonneg (2 * F x - (∫ y, F y ∂μ))]
      have hprod : 0 ≤ (B - |F x|) * (B + |F x|) :=
        mul_nonneg (sub_nonneg.mpr hFx)
          (add_nonneg hB (abs_nonneg (F x)))
      have hsqB : F x ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs (F x)]
        nlinarith [hprod]
      nlinarith [hsquare, hsqB]
    · simp [g, K, hx]
      positivity
  have hint' : (∫ x, m ^ 2 * g x ∂μ) ≤
      ∫ x, 2 * (F x - m) ^ 2 + 2 * (B ^ 2 * g x) ∂μ := by
    apply integral_mono_ae
      ((hg.const_mul (m ^ 2)).congr (Eventually.of_forall fun x => by ring))
      ((hcenter.const_mul (2 : ℝ)).add ((hg.const_mul (B ^ 2)).const_mul (2 : ℝ)))
    exact Eventually.of_forall fun x => by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint x
  have hmass : (∫ x, g x ∂μ) = μ.real K := by
    dsimp [g]
    exact integral_indicator_one hK
  have hsimple : μ.real K * m ^ 2 ≤
      2 * (∫ x, (F x - m) ^ 2 ∂μ) + 2 * μ.real K * B ^ 2 := by
    calc
      μ.real K * m ^ 2 = ∫ x, m ^ 2 * g x ∂μ := by
        rw [integral_const_mul, hmass]
        ring
      _ ≤ _ := hint'
      _ = 2 * (∫ x, (F x - m) ^ 2 ∂μ) + 2 * μ.real K * B ^ 2 := by
        rw [integral_add (hcenter.const_mul (2 : ℝ))
          ((hg.const_mul (B ^ 2)).const_mul (2 : ℝ))]
        rw [integral_const_mul, integral_const_mul, integral_const_mul, hmass]
        ring
  have hmul : μ.real K * m ^ 2 ≤ 2 * V + 2 * μ.real K * B ^ 2 := by
    exact hsimple.trans (add_le_add (mul_le_mul_of_nonneg_left hvariance (by norm_num)) le_rfl)
  have hmdiv : m ^ 2 ≤ (2 * V + 2 * μ.real K * B ^ 2) / μ.real K := by
    rw [le_div_iff₀ hball]
    nlinarith [hmul]
  calc
    (∫ x, F x ∂μ) ^ 2 ≤ (2 * V + 2 * μ.real K * B ^ 2) / μ.real K := by
      simpa [m] using hmdiv
    _ = 2 * V / μ.real K + 2 * B ^ 2 := by
      rw [add_div]
      congr 1
      rw [show 2 * μ.real K * B ^ 2 = (2 * B ^ 2) * μ.real K by ring,
        mul_div_cancel_right₀ _ hball.ne']

/-- Conditional positive-ball and centered-variance input for nonnegative Fatou.
The same raw measure and actual approximant sequence occur in every premise. -/
theorem integrable_sq_of_uniform_centered_variance_approximants
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ) (f : ℕ → EuclideanSpace ℝ ι → ℝ)
    (r B V : ℝ) (hB : 0 ≤ B)
    (hball : 0 < μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r))
    (hF : Measurable F) (hcont : ∀ j, Continuous (f j))
    (hfi : ∀ j, Integrable (f j) μ)
    (hcenter : ∀ j, Integrable (fun x => (f j x - ∫ y, f j y ∂μ) ^ 2) μ)
    (hvariance : ∀ j, (∫ x, (f j x - ∫ y, f j y ∂μ) ^ 2 ∂μ) ≤ V)
    (hball_bound : ∀ j x, x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) r → |f j x| ≤ B)
    (hpoint : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (F x))) :
    Integrable (fun x => F x ^ 2) μ := by
  have hV : 0 ≤ V := le_trans (integral_nonneg fun _ => sq_nonneg _) (hvariance 0)
  have hraw_int (j : ℕ) : Integrable (fun x => (f j x) ^ 2) μ := by
    let m : ℝ := ∫ y, f j y ∂μ
    have hid : (fun x => (f j x) ^ 2) =
        (fun x => (f j x - m) ^ 2 + (2 * m) * f j x - m ^ 2) := by
      funext x
      dsimp [m]
      ring
    rw [hid]
    exact ((hcenter j).add ((hfi j).const_mul (2 * m))).sub (integrable_const (m ^ 2))
  have hraw_bound (j : ℕ) :
      (∫ x, (f j x) ^ 2 ∂μ) ≤ V + 2 * V / μ.real (Metric.ball 0 r) + 2 * B ^ 2 := by
    have hm := mean_sq_le_of_centered_variance_ball μ (f j) (hfi j) r B V hB hball
      (hball_bound j) (hcenter j) (hvariance j)
    calc
      _ = (∫ x, (f j x - ∫ y, f j y ∂μ) ^ 2 ∂μ) + (∫ x, f j x ∂μ) ^ 2 :=
        integral_sq_eq_centered_add_mean_sq (hfi j) (hraw_int j) (hcenter j)
      _ ≤ V + (2 * V / μ.real (Metric.ball 0 r) + 2 * B ^ 2) :=
        add_le_add (hvariance j) hm
      _ = V + 2 * V / μ.real (Metric.ball 0 r) + 2 * B ^ 2 := by ring
  let K : ℝ := V + 2 * V / μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * B ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hlintegral_bound (j : ℕ) :
      ∫⁻ x, ENNReal.ofReal ((f j x) ^ 2) ∂μ ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hraw_int j)
      (Eventually.of_forall fun x => sq_nonneg (f j x))]
    exact ENNReal.ofReal_le_ofReal (by simpa [K] using hraw_bound j)
  have hmeas (j : ℕ) : AEMeasurable (fun x => ENNReal.ofReal ((f j x) ^ 2)) μ := by
      exact (ENNReal.continuous_ofReal.comp ((hcont j).pow 2)).aemeasurable
  have hfatou := lintegral_liminf_le' (μ := μ)
    (f := fun j x => ENNReal.ofReal ((f j x) ^ 2)) (u := atTop) hmeas
  have hpointENN (x : EuclideanSpace ℝ ι) :
      Tendsto (fun j => ENNReal.ofReal ((f j x) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (F x ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_pow 2).continuousAt.tendsto.comp (hpoint x))
  have hlim (x : EuclideanSpace ℝ ι) :
      ENNReal.ofReal (F x ^ 2) = atTop.liminf
        (fun j => ENNReal.ofReal ((f j x) ^ 2)) := (hpointENN x).liminf_eq.symm
  have hbound : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ ≤ ENNReal.ofReal K := by
    calc
      _ = ∫⁻ x, atTop.liminf (fun j => ENNReal.ofReal ((f j x) ^ 2)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        exact hlim x
      _ ≤ atTop.liminf (fun j => ∫⁻ x, ENNReal.ofReal ((f j x) ^ 2) ∂μ) := hfatou
      _ ≤ ENNReal.ofReal K := liminf_le_of_frequently_le
        ((Eventually.of_forall hlintegral_bound).frequently)
  have hfinite : HasFiniteIntegral (fun x => F x ^ 2) μ := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (F x))]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  exact ⟨(hF.pow_const 2).aestronglyMeasurable, hfinite⟩

private theorem exists_pos_mass_ball
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∃ r : ℝ, 0 < r ∧ 0 < μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) := by
  let K : ℕ → Set (EuclideanSpace ℝ ι) := fun n => Metric.ball 0 ((n : ℝ) + 1)
  have hcover : (⋃ n, K n) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact Metric.mem_ball.mpr (by
        simpa [dist_eq_norm] using
          (lt_trans hn (by exact_mod_cast Nat.lt_succ_self n : (n : ℝ) < (n : ℝ) + 1)))
  have hmass : μ (⋃ n, K n) ≠ 0 := by
    rw [hcover, measure_univ]
    simp
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  have htop : μ (K n) ≠ ⊤ := measure_ne_top μ _
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  exact ENNReal.toReal_pos hn.ne' htop

/-- Finite intrinsic LSI gives an actual second moment on the same arbitrary
finite Euclidean carrier. The completed-pair Poincare theorem controls the
approximants; raw Fatou supplies first integrability; centered Fatou then gives
the limiting variance used to finish the raw second-moment bound. -/
theorem norm_sq_integrable_of_finite_logSobolevConstant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤) :
    Integrable (fun x => ‖x‖ ^ 2) μ := by
  let C : ℝ := (logSobolevConstant μ).toReal
  have hC : 0 ≤ C := by dsimp [C]; exact ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μ ≤ ENNReal.ofReal C := by
    dsimp [C]
    rw [ENNReal.ofReal_toReal hfinite.ne]
  obtain ⟨r, hr, hball⟩ := exists_pos_mass_ball μ
  let R : ℕ → NNReal := fun j => ⟨(j : ℝ) + 1, by positivity⟩
  let η : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let f : ℕ → EuclideanSpace ℝ ι → ℝ := fun j =>
    clipThenMollify (fun x : EuclideanSpace ℝ ι => ‖x‖) (R j) (η j)
  have hηpos (j : ℕ) : 0 < η j := by
    dsimp [η]
    positivity
  have hηle (j : ℕ) : η j ≤ 1 := by
    dsimp [η]
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηtendsto : Tendsto η atTop (𝓝 0) := by
    dsimp [η]
    have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hden
    change Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) at hinv
    simpa [η, div_eq_mul_inv] using hinv
  have hseg : HasLinearGrowthSegmentBound (fun x : EuclideanSpace ℝ ι => ‖x‖) 1 0 := by
    intro x y
    simpa [dist_eq_norm] using abs_norm_sub_norm_le x y
  have hsegClip (j : ℕ) : HasLinearGrowthSegmentBound
      (clipFunction (R j : ℝ) (fun x : EuclideanSpace ℝ ι => ‖x‖)) 1 0 :=
    clipFunction_segmentBound hseg
  have hclose (j : ℕ) (x : EuclideanSpace ℝ ι) :
      |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| ≤ η j := by
    have h := LOOConcentration.clipThenMollify_close (f := fun x : EuclideanSpace ℝ ι => ‖x‖)
      (N := (R j : ℝ)) (η := η j) (a := 1) (b := 0) continuous_norm (hηpos j)
      (hsegClip j) (by norm_num) (by norm_num) x
    have hfun : clipFunction (R j : ℝ) (fun x : EuclideanSpace ℝ ι => ‖x‖) =
        clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j := by
      funext y
      rfl
    rw [hfun] at h
    simpa [f, hfun, R, η] using h
  have hcontinuous (j : ℕ) : Continuous (f j) := by
    have h := clipThenMollify_bounded_smooth (fun x : EuclideanSpace ℝ ι => ‖x‖)
      continuous_norm (R j) (η j) (hηpos j)
    simpa [f] using h.1.continuous
  have hbound (j : ℕ) (x : EuclideanSpace ℝ ι) : |f j x| ≤ (R j : ℝ) := by
    have h := clipThenMollify_range (f := fun x : EuclideanSpace ℝ ι => ‖x‖)
      (N := (R j : ℝ)) continuous_norm (R j).property (hηpos j) x
    exact abs_le.mpr h
  have hgrad (j : ℕ) (x : EuclideanSpace ℝ ι) : ‖gradient (f j) x‖ ≤ 1 := by
    have h := clipThenMollify_gradient_growth (fun x : EuclideanSpace ℝ ι => ‖x‖)
      continuous_norm 1 0 (R j : ℝ) (η j) (hηpos j) (by
        intro y z
        simpa [dist_eq_norm] using abs_norm_sub_norm_le y z) x
    simpa [f] using h
  have hpoint (x : EuclideanSpace ℝ ι) : Tendsto (fun j => f j x) atTop (𝓝 ‖x‖) := by
    have hclip := clipValueSequence_tendsto (fun x : EuclideanSpace ℝ ι => ‖x‖) x
    have hηnorm : Tendsto (fun j => ‖f j x -
        clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x‖) atTop (𝓝 0) := by
      exact squeeze_zero (fun j => norm_nonneg _) (fun j => by
        rw [Real.norm_eq_abs]
        exact hclose j x) hηtendsto
    have hnormsub : Tendsto (fun j => ‖(f j x -
        clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x) - (0 : ℝ)‖)
        atTop (𝓝 0) := by simpa using hηnorm
    have herr : Tendsto (fun j => f j x -
        clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x) atTop (𝓝 0) := by
      exact (tendsto_iff_norm_sub_tendsto_zero).2 hnormsub
    simpa only [zero_add, sub_add_cancel] using herr.add hclip
  have hfi (j : ℕ) : Integrable (f j) μ := by
    apply Integrable.of_bound (hcontinuous j).aestronglyMeasurable (R j : ℝ)
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact hbound j x
  have hmean_abs (j : ℕ) : |∫ x, f j x ∂μ| ≤ (R j : ℝ) := by
    calc
      _ ≤ ∫ x, |f j x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, (R j : ℝ) ∂μ := by
        apply integral_mono_ae (hfi j).abs (integrable_const _)
        exact Eventually.of_forall (hbound j)
      _ = (R j : ℝ) := by simp [Measure.real, measure_univ]
  have hcenter (j : ℕ) :
      Integrable (fun x => (f j x - ∫ y, f j y ∂μ) ^ 2) μ := by
    refine Integrable.of_bound
      (((hcontinuous j).sub continuous_const).pow 2).aestronglyMeasurable
      ((2 * (R j : ℝ)) ^ 2) ?_
    filter_upwards [] with x
    change ‖(f j x - ∫ y, f j y ∂μ) ^ 2‖ ≤ (2 * (R j : ℝ)) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have habs : |f j x - ∫ y, f j y ∂μ| ≤ 2 * (R j : ℝ) := by
      calc
        _ ≤ |f j x| + |∫ y, f j y ∂μ| := abs_sub _ _
        _ ≤ (R j : ℝ) + (R j : ℝ) := add_le_add (hbound j x) (hmean_abs j)
        _ = 2 * (R j : ℝ) := by ring
    have hcapNonneg : 0 ≤ 2 * (R j : ℝ) := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hcapNonneg (abs_nonneg (f j x - ∫ y, f j y ∂μ)))
    nlinarith [hprod, sq_abs (f j x - ∫ y, f j y ∂μ)]
  have hvariance (j : ℕ) :
      (∫ x, (f j x - ∫ y, f j y ∂μ) ^ 2 ∂μ) ≤ C := by
    obtain ⟨p, hp, hs, hg⟩ := exists_smooth_pair_clipThenMollify μ
      (fun x : EuclideanSpace ℝ ι => ‖x‖) continuous_norm (R j) (η j) (hηpos j)
    let u : SobolevPair μ := ⟨p, subset_closure hp⟩
    have hpoincare := all_pairs_poincare_of_logSobolevConstant_le μ C hC hLC u
    have hmean : (∫ y, (WithLp.ofLp u.val).1 y ∂μ) = ∫ y, f j y ∂μ :=
      integral_congr_ae hs
    have hvarEq :
        (∫ x, (f j x - ∫ y, f j y ∂μ) ^ 2 ∂μ) =
          ∫ x, ((WithLp.ofLp u.val).1 x - ∫ y, (WithLp.ofLp u.val).1 y ∂μ) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      rw [hx, hmean]
    have henergy : sobolevEnergy μ u ≤ ENNReal.ofReal 1 := by
      change ∫⁻ x, ‖(WithLp.ofLp u.val).2 x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal 1
      calc
        _ ≤ ∫⁻ x, ENNReal.ofReal 1 ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hg] with x hx
          rw [hx]
          have hn := hgrad j x
          have hn0 := norm_nonneg (gradient (f j) x)
          have hsquare : ‖gradient (f j) x‖ ^ 2 ≤ 1 := by nlinarith
          have hreal := ENNReal.ofReal_le_ofReal hsquare
          have henorm : ‖gradient (f j) x‖ₑ = ENNReal.ofReal ‖gradient (f j) x‖ := by
            rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
            congr 1
          rw [henorm, ← ENNReal.ofReal_pow hn0 2]
          exact hreal
        _ = ENNReal.ofReal 1 := by simp [measure_univ]
    have henergyReal : (sobolevEnergy μ u).toReal ≤ 1 := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top henergy
      simpa using ht
    rw [hvarEq]
    calc
      _ ≤ C * (sobolevEnergy μ u).toReal := hpoincare
      _ ≤ C := by nlinarith [hC, henergyReal]
  have hball_bound (j : ℕ) (x : EuclideanSpace ℝ ι)
      (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) r) : |f j x| ≤ r + 1 := by
    have hxnorm : ‖x‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hclip := LOOConcentration.abs_clipValue_le_abs
      (A := (R j : ℝ)) (u := ‖x‖) (by positivity)
    calc
      |f j x| ≤ |clipValue ((R j : ℝ)) (‖x‖)| +
          |f j x - clipValue ((R j : ℝ)) (‖x‖)| := by
        calc
          |f j x| = |(f j x - clipValue ((R j : ℝ)) (‖x‖)) +
              clipValue ((R j : ℝ)) (‖x‖)| := by congr 1; ring
          _ ≤ |f j x - clipValue ((R j : ℝ)) (‖x‖)| +
              |clipValue ((R j : ℝ)) (‖x‖)| := abs_add_le _ _
          _ = |clipValue ((R j : ℝ)) (‖x‖)| +
              |f j x - clipValue ((R j : ℝ)) (‖x‖)| := by ring
      _ ≤ ‖x‖ + η j := by
        apply add_le_add
        · simpa [LOOConcentration.clipFunction, abs_of_nonneg (norm_nonneg _)] using hclip
        · have hclose' := hclose j x
          have hclipEq : clipValueSequence
              (fun x : EuclideanSpace ℝ ι => ‖x‖) j x =
                clipValue ((R j : ℝ)) (‖x‖) := by rfl
          simpa [hclipEq] using hclose'
      _ ≤ r + 1 := add_le_add hxnorm.le (hηle j)
  have hraw := integrable_sq_of_uniform_centered_variance_approximants μ
    (fun x : EuclideanSpace ℝ ι => ‖x‖) f r (r + 1) C (by linarith) hball
    continuous_norm.measurable hcontinuous hfi hcenter hvariance
    hball_bound hpoint
  have hnorm : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) μ := by
    apply (hraw.add (integrable_const (1 : ℝ))).mono
      continuous_norm.aestronglyMeasurable
    filter_upwards [] with x
    change ‖(‖x‖ : ℝ)‖ ≤ ‖‖x‖ ^ 2 + 1‖
    rw [Real.norm_of_nonneg (norm_nonneg x),
      Real.norm_of_nonneg (add_nonneg (sq_nonneg _) (by norm_num))]
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - (1 / 2 : ℝ))]
  have hclipIntegrable (j : ℕ) :
      Integrable (clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j) μ := by
    apply hnorm.mono
      ((LOOConcentration.continuous_clipValue ((j : ℝ) + 1)).comp_aestronglyMeasurable
        continuous_norm.aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact LOOConcentration.abs_clipValue_le_abs (by positivity)
  have hclipL1 := LOOConcentration.clipValueSequence_L1_tendsto hnorm
  have happroxInt (j : ℕ) : Integrable
      (fun x => |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x|) μ :=
    ((hfi j).sub (hclipIntegrable j)).norm
  have hclipErrorInt (j : ℕ) : Integrable
      (fun x => |clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x - ‖x‖|) μ :=
    ((hclipIntegrable j).sub hnorm).norm
  have happroxBound (j : ℕ) :
      (∫ x, |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| ∂μ) ≤ η j := by
    calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, η j ∂μ := by
        apply integral_mono_ae (happroxInt j) (integrable_const _)
        exact Eventually.of_forall fun x => hclose j x
      _ = η j := by simp [Measure.real, measure_univ]
  have happroxL1 : Tendsto
      (fun j => ∫ x, |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| ∂μ)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _)
      happroxBound hηtendsto
  have hL1bound (j : ℕ) :
      (∫ x, |f j x - ‖x‖| ∂μ) ≤
        (∫ x, |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| ∂μ) +
          (∫ x, |clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x - ‖x‖| ∂μ) := by
    have htri : ∀ x, |f j x - ‖x‖| ≤
        |f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| +
          |clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x - ‖x‖| := by
      intro x
      exact abs_sub_le _ _ _
    calc
      _ ≤ ∫ x, (|f j x - clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x| +
          |clipValueSequence (fun x : EuclideanSpace ℝ ι => ‖x‖) j x - ‖x‖|) ∂μ := by
        apply integral_mono_ae ((hfi j).sub hnorm |>.norm)
          ((happroxInt j).add (hclipErrorInt j))
        exact Eventually.of_forall htri
      _ = _ := integral_add (happroxInt j) (hclipErrorInt j)
  have hL1 : Tendsto (fun j => ∫ x, |f j x - ‖x‖| ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _)
      hL1bound (by simpa using happroxL1.add hclipL1)
  have hfatou := centeredPow_le_of_L1_tendsto hfi hnorm hL1
    (by norm_num : (2 : ℝ) ≤ 2) (ENNReal.ofReal C) (fun j => by
      have heq := ofReal_integral_eq_lintegral_ofReal (hcenter j)
        (Eventually.of_forall fun x => sq_nonneg (f j x - ∫ y, f j y ∂μ))
      have htotal : ∫⁻ x, ENNReal.ofReal ((f j x - ∫ y, f j y ∂μ) ^ 2) ∂μ ≤
          ENNReal.ofReal C := by
        rw [← heq]
        exact ENNReal.ofReal_le_ofReal (hvariance j)
      simpa [sq_abs] using htotal)
  have hcenterNorm : Integrable
      (fun x => (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2) μ := by
    have hidentity : (fun x : EuclideanSpace ℝ ι => (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2) =
        (fun x => ‖x‖ ^ 2 - (2 * (∫ y, ‖y‖ ∂μ)) * ‖x‖ + (∫ y, ‖y‖ ∂μ) ^ 2) := by
      funext x
      ring
    rw [hidentity]
    exact (hraw.sub (hnorm.const_mul _)).add (integrable_const _)
  have hfatouReal :
      (∫ x, (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2 ∂μ) ≤ C := by
    have heq := ofReal_integral_eq_lintegral_ofReal hcenterNorm
      (Eventually.of_forall fun x => sq_nonneg (‖x‖ - ∫ y, ‖y‖ ∂μ))
    have hfatou' : ∫⁻ x, ENNReal.ofReal
        ((‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2) ∂μ ≤ ENNReal.ofReal C := by
      simpa [sq_abs] using hfatou
    have hENN : ENNReal.ofReal
        (∫ x, (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2 ∂μ) ≤ ENNReal.ofReal C := by
      rw [heq]
      exact hfatou'
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    have hnonneg : 0 ≤ ∫ x, (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    simpa [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal hC] using htoReal
  have hmeanBound := mean_sq_le_of_centered_variance_ball μ
    (fun x : EuclideanSpace ℝ ι => ‖x‖) hnorm r r C (by linarith) hball
    (fun x hx => by
      have hxnorm : ‖x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hx
      simpa only [abs_of_nonneg (norm_nonneg x)] using hxnorm.le)
    hcenterNorm hfatouReal
  have hsecondBound : (∫ x, ‖x‖ ^ 2 ∂μ) ≤ C + 2 * C / μ.real
      (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * r ^ 2 := by
    calc
      _ = (∫ x, (‖x‖ - ∫ y, ‖y‖ ∂μ) ^ 2 ∂μ) + (∫ x, ‖x‖ ∂μ) ^ 2 :=
        integral_sq_eq_centered_add_mean_sq hnorm hraw hcenterNorm
      _ ≤ C + (2 * C / μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * r ^ 2) :=
        add_le_add hfatouReal hmeanBound
      _ = C + 2 * C / μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * r ^ 2 := by ring
  have hlintegral : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ ≤ ENNReal.ofReal
      (C + 2 * C / μ.real (Metric.ball (0 : EuclideanSpace ℝ ι) r) + 2 * r ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hraw
      (Eventually.of_forall fun x => sq_nonneg (‖x‖))]
    exact ENNReal.ofReal_le_ofReal hsecondBound
  have hfiniteInt : HasFiniteIntegral (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (‖x‖))]
    exact lt_of_le_of_lt hlintegral ENNReal.ofReal_lt_top
  exact ⟨(continuous_norm.pow 2).aestronglyMeasurable, hfiniteInt⟩

end LOOConcentration.Revision
