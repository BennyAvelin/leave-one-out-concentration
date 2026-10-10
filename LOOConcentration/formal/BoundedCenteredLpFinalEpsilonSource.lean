import LOOConcentrationRevision.FunctionalInequalities.IntrinsicPoincare
import LOOConcentrationRevision.Analysis.RealQLpDerivativeZeroRemoval
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentrationRevision

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual regularized source curve from the moment interpolation argument. -/
noncomputable def regularizedSourceLpCurve (μ : Measure Ω) (F : Ω → ℝ)
    (ε q : ℝ) : ℝ :=
  (∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ q ∂μ) ^ (2 / q)

/-- The exact derivative expression supplied by the accepted real-q derivative theorem
for the source regularization `sqrt (F^2 + ε)`. -/
noncomputable def regularizedSourceLpCurveDerivative (μ : Measure Ω) (F : Ω → ℝ)
    (ε q : ℝ) : ℝ :=
  (2 / q ^ 2) *
    (∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ q ∂μ) ^ (2 / q - 1) *
    ((∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ q *
        Real.log (|Real.sqrt (F x ^ 2 + ε)| ^ q) ∂μ) -
      (∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ q ∂μ) *
        Real.log (∫ x, |Real.sqrt (F x ^ 2 + ε)| ^ q ∂μ))

/-- Differentiability of the actual regularized source curve, including when `F` vanishes. -/
theorem regularizedSourceLpCurve_hasDerivAt
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {B ε q : ℝ}
    (hFmeas : Measurable F) (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (hε : 0 < ε) (hq : 2 ≤ q) :
    HasRealDerivAt (fun r => regularizedSourceLpCurve μ F ε r)
      (regularizedSourceLpCurveDerivative μ F ε q) q := by
  simpa [regularizedSourceLpCurve, regularizedSourceLpCurveDerivative] using
    (regularized_abs_realQLp_normSq_consumer (μ := μ) (g := F) (B := B)
      (ε := ε) (q := q) hFmeas hB hFbound hε hq)

/-- The actual regularized source curve is continuous on the source exponent interval. -/
theorem regularizedSourceLpCurve_continuousOn_Icc
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {B ε p : ℝ}
    (hFmeas : Measurable F) (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (hε : 0 < ε) :
    ContinuousOn (fun q => regularizedSourceLpCurve μ F ε q) (Set.Icc 2 p) := by
  intro q hq
  exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := F) (B := B) (ε := ε)
    hFmeas hB hFbound hε hq.1).continuousAt.continuousWithinAt

/-- The actual regularized source curve is differentiable on the open source exponent interval. -/
theorem regularizedSourceLpCurve_differentiableOn_Ioo
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {B ε p : ℝ}
    (hFmeas : Measurable F) (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (hε : 0 < ε) :
    DifferentiableOn ℝ (fun q => regularizedSourceLpCurve μ F ε q) (Set.Ioo 2 p) := by
  intro q hq
  exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := F) (B := B) (ε := ε)
    hFmeas hB hFbound hε hq.1.le).differentiableAt.differentiableWithinAt

/-- Integrate the actual source curve's derivative upper bound from `2` to `p`.
The derivative bound is an explicit producer premise; the source LSI bridge is its intended
producer. The statement includes `p = 2` and `C = 0`. -/
theorem regularizedSourceLpCurve_increment_of_derivative_upper_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {B ε p C : ℝ}
    (hFmeas : Measurable F) (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (hε : 0 < ε) (hp : 2 ≤ p)
    (hSourceDerivativeUpperBound :
      ∀ q ∈ Set.Icc 2 p, regularizedSourceLpCurveDerivative μ F ε q ≤ C) :
    regularizedSourceLpCurve μ F ε p ≤
      regularizedSourceLpCurve μ F ε 2 + C * (p - 2) := by
  let f : ℝ → ℝ := fun q => regularizedSourceLpCurve μ F ε q
  have hcont : ContinuousOn f (Set.Icc 2 p) := by
    intro q hq
    exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := F) (B := B) (ε := ε)
      hFmeas hB hFbound hε hq.1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc 2 p)) := by
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo 2 p) := by
      intro q hq
      exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := F) (B := B) (ε := ε)
        hFmeas hB hFbound hε hq.1.le).differentiableAt.differentiableWithinAt
    simpa only [interior_Icc] using hdiff'
  have hderiv : ∀ q ∈ interior (Set.Icc 2 p), deriv f q ≤ C := by
    intro q hq
    have hqIcc : q ∈ Set.Icc 2 p := interior_subset hq
    have hqAt := regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := F) (B := B)
      (ε := ε) hFmeas hB hFbound hε hqIcc.1
    have hqEq : deriv f q = regularizedSourceLpCurveDerivative μ F ε q := by
      change deriv (fun r => regularizedSourceLpCurve μ F ε r) q = _
      exact hqAt.deriv
    rw [hqEq]
    exact hSourceDerivativeUpperBound q hqIcc
  have hsegment := (convex_Icc (2 : ℝ) p).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff (C := C) hderiv 2 ⟨le_rfl, hp⟩ p ⟨hp, le_rfl⟩ hp
  have hdiffBound : f p - f 2 ≤ C * (p - 2) := hsegment
  calc
    f p = (f p - f 2) + f 2 := by ring
    _ ≤ C * (p - 2) + f 2 := add_le_add hdiffBound le_rfl
    _ = f 2 + C * (p - 2) := by ring

end

end LOOConcentrationRevision

open InnerProductSpace

namespace LOOConcentration.Revision

noncomputable section

/-- Probability-space monotonicity of the actual gradient second moment. -/
theorem boundedGradientSecondMoment_le_pMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖gradient F x‖ ≤ B)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, ‖gradient F x‖ ^ 2 ∂μ) ≤
      (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
  by_cases hpEq : p = 2
  · subst p
    simp
  have hp' : 2 < p := lt_of_le_of_ne hp (Ne.symm hpEq)
  let g : EuclideanSpace ℝ ι → ℝ := fun x => ‖gradient F x‖
  have hgC : Continuous g := by
    dsimp [g]
    exact ((toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))).norm
  have hq : (p / 2).HolderConjugate (p / (p - 2)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · linarith
    · field_simp
      ring
  have hmemF : MemLp (fun x => g x ^ 2) (ENNReal.ofReal (p / 2)) μ := by
    apply MemLp.of_bound (hgC.pow 2).aestronglyMeasurable (B ^ 2)
    filter_upwards [] with x
    have hgx : 0 ≤ g x := by simp [g]
    change ‖g x ^ 2‖ ≤ B ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg (g x))]
    nlinarith [hbound x]
  have hmemOne : MemLp (fun _ : EuclideanSpace ℝ ι => (1 : ℝ))
      (ENNReal.ofReal (p / (p - 2))) μ := by
    apply MemLp.of_bound aestronglyMeasurable_const 1
    filter_upwards [] with x
    simp
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hq
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x))
    (Filter.Eventually.of_forall fun _ => by norm_num)
    hmemF hmemOne
  have hmass : (∫ x : EuclideanSpace ℝ ι, (1 : ℝ) ∂μ) = 1 := by simp
  have hpow : ∀ x, (g x ^ 2) ^ (p / 2) = g x ^ p := by
    intro x
    rw [← Real.rpow_natCast (g x) 2]
    calc
      (g x ^ (2 : ℝ)) ^ (p / 2) = g x ^ ((2 : ℝ) * (p / 2)) :=
        (Real.rpow_mul (by positivity : 0 ≤ g x) 2 (p / 2)).symm
      _ = g x ^ p := by congr 1; ring
  simp_rw [hpow] at hh
  simpa [g, hmass, div_eq_mul_inv, one_div, mul_comm] using hh

end

end LOOConcentration.Revision

open LOOConcentrationRevision

namespace LOOConcentration.Revision

noncomputable section

/-- The prior actual-curve integration theorem with the derivative bound restricted
to the open exponent interval, the precise range supplied by the LSI producer. -/
theorem actualRegularizedCurveIncrement_of_interior_derivative_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → ℝ}
    {B ε p D : ℝ}
    (hGmeas : Measurable G) (hB : 0 ≤ B) (hGbound : ∀ x, |G x| ≤ B)
    (hε : 0 < ε) (hp : 2 ≤ p)
    (hDerivativeUpperBound :
      ∀ q ∈ Set.Ioo 2 p,
        regularizedSourceLpCurveDerivative μ G ε q ≤ D) :
    regularizedSourceLpCurve μ G ε p ≤
      regularizedSourceLpCurve μ G ε 2 + D * (p - 2) := by
  let f : ℝ → ℝ := fun q => regularizedSourceLpCurve μ G ε q
  have hcont : ContinuousOn f (Set.Icc 2 p) := by
    intro q hq
    exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := G) (B := B)
      (ε := ε) hGmeas hB hGbound hε hq.1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc 2 p)) := by
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo 2 p) := by
      intro q hq
      exact (regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := G) (B := B)
        (ε := ε) hGmeas hB hGbound hε hq.1.le).differentiableAt.differentiableWithinAt
    simpa only [interior_Icc] using hdiff'
  have hderiv : ∀ q ∈ interior (Set.Icc 2 p), deriv f q ≤ D := by
    intro q hq
    have hqInterior : q ∈ Set.Ioo 2 p := by simpa only [interior_Icc] using hq
    have hqIcc : q ∈ Set.Icc 2 p := interior_subset hq
    have hqAt := regularizedSourceLpCurve_hasDerivAt (μ := μ) (F := G) (B := B)
      (ε := ε) hGmeas hB hGbound hε hqIcc.1
    have hqEq : deriv f q = regularizedSourceLpCurveDerivative μ G ε q := by
      change deriv (fun r => regularizedSourceLpCurve μ G ε r) q = _
      exact hqAt.deriv
    rw [hqEq]
    exact hDerivativeUpperBound q hqInterior
  have hsegment := (convex_Icc (2 : ℝ) p).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff (C := D) hderiv 2 ⟨le_rfl, hp⟩ p ⟨hp, le_rfl⟩ hp
  have hdiffBound : f p - f 2 ≤ D * (p - 2) := hsegment
  calc
    f p = (f p - f 2) + f 2 := by ring
    _ ≤ D * (p - 2) + f 2 := add_le_add hdiffBound le_rfl
    _ = f 2 + D * (p - 2) := by ring

end

end LOOConcentration.Revision

open LOOConcentrationRevision

namespace LOOConcentration.Revision

noncomputable section

/-- Centered bounded-smooth source Lp inequality, conditional only on the
actual regularized derivative upper-bound producer (worker2,
`bounded-real-q-derivative-holder-source-v4`). The derivative premise is for
the literal curve above, centered by the literal probability mean. -/
theorem boundedSmoothCenteredLp_of_actualRegularizedDerivativeBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    {p : ℝ} (hp : 2 ≤ p)
    (hDerivativeUpperBound :
      ∀ ε, 0 < ε → ∀ q ∈ Set.Ioo 2 p,
        regularizedSourceLpCurveDerivative μ
          (fun x => F x - ∫ y, F y ∂μ) ε q ≤
        C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)) :
    (∫ x, |F x - ∫ y, F y ∂μ| ^ p ∂μ) ^ (2 / p) ≤
      C * (p - 1) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
  have hFint : Integrable F μ := by
    apply Integrable.of_bound hF.continuous.aestronglyMeasurable B
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using (hbound x).1
  let mean : ℝ := ∫ x, F x ∂μ
  let G : EuclideanSpace ℝ ι → ℝ := fun x => F x - mean
  have hmeanBound : |mean| ≤ B := by
    calc
      |mean| = |∫ x, F x ∂μ| := rfl
      _ ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, B ∂μ := by
        apply integral_mono_ae hFint.abs (integrable_const B)
        exact Filter.Eventually.of_forall fun x => (hbound x).1
      _ = B := by simp
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGbound : ∀ x, |G x| ≤ 2 * B := by
    intro x
    calc
      |G x| = |F x - mean| := rfl
      _ ≤ |F x| + |mean| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbound x).1 hmeanBound
      _ = 2 * B := by ring
  have hGmeas : Measurable G := hGcont.measurable
  have hPoincare := bounded_smooth_intrinsic_poincare μ C hC hLC F hF B hB hbound
  have hGradMoment := boundedGradientSecondMoment_le_pMoment (μ := μ) F hF B hB
    (fun x => (hbound x).2) hp
  have hGradIntNonneg : 0 ≤ ∫ x, ‖gradient F x‖ ^ p ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (norm_nonneg _) _)
  have hGradPowNonneg :
      0 ≤ (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) :=
    Real.rpow_nonneg hGradIntNonneg _
  have hVarianceLp :
      (∫ x, G x ^ 2 ∂μ) ≤
        C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
    calc
      ∫ x, G x ^ 2 ∂μ ≤ C * (∫ x, ‖gradient F x‖ ^ 2 ∂μ) := hPoincare.2
      _ ≤ C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) :=
        mul_le_mul_of_nonneg_left hGradMoment hC
  by_cases hpEq : p = 2
  · subst p
    norm_num [G, mean, Real.rpow_one, Real.rpow_natCast, sq_abs, mul_one] at hPoincare ⊢
    exact hPoincare.2
  · have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hpEq)
    have hGmem : MemLp G (ENNReal.ofReal p) μ := by
      apply MemLp.of_bound hGcont.aestronglyMeasurable (2 * B)
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs] using hGbound x
    have hRawInt : Integrable (fun x => |G x| ^ p) μ := by
      have h := hGmem.integrable_norm_rpow'
      simpa only [Real.norm_eq_abs,
        ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using h
    have hFinal : ∀ ε, 0 < ε →
        (∫ x, |G x| ^ p ∂μ) ^ (2 / p) ≤
          C * (p - 1) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) + ε := by
      intro ε hε
      let H : EuclideanSpace ℝ ι → ℝ := fun x =>
        Real.sqrt (G x ^ 2 + ε)
      have hHcont : Continuous H := by
        dsimp [H]
        fun_prop
      have hHbound : ∀ x, ‖H x‖ ≤ Real.sqrt ((2 * B) ^ 2 + ε) := by
        intro x
        have hsq : G x ^ 2 ≤ (2 * B) ^ 2 := by
          have ha := hGbound x
          have hK : 0 ≤ 2 * B := by positivity
          rw [← sq_abs (G x)]
          exact (sq_le_sq₀ (abs_nonneg (G x)) hK).2 ha
        have hrad : G x ^ 2 + ε ≤ (2 * B) ^ 2 + ε :=
          by nlinarith [hsq]
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt hrad
      have hHmem : MemLp H (ENNReal.ofReal p) μ := by
        apply MemLp.of_bound hHcont.aestronglyMeasurable
          (Real.sqrt ((2 * B) ^ 2 + ε))
        filter_upwards [] with x
        simpa only [Real.norm_eq_abs] using hHbound x
      have hRegInt : Integrable (fun x => |Real.sqrt (G x ^ 2 + ε)| ^ p) μ := by
        have h := hHmem.integrable_norm_rpow'
        simpa only [Real.norm_eq_abs, H,
          abs_of_nonneg (Real.sqrt_nonneg _),
          ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using h
      have hPoint (x : EuclideanSpace ℝ ι) :
          |G x| ^ p ≤ |Real.sqrt (G x ^ 2 + ε)| ^ p := by
        have hbase : |G x| ≤ Real.sqrt (G x ^ 2 + ε) := by
          calc
            |G x| = Real.sqrt (G x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt (G x ^ 2 + ε) :=
              Real.sqrt_le_sqrt (by linarith [sq_nonneg (G x), hε.le])
        have hsqrtNonneg : 0 ≤ Real.sqrt (G x ^ 2 + ε) := Real.sqrt_nonneg _
        exact Real.rpow_le_rpow (abs_nonneg _)
          (by simpa [abs_of_nonneg hsqrtNonneg] using hbase)
          (show 0 ≤ p by linarith)
      have hIntMono :
          (∫ x, |G x| ^ p ∂μ) ≤
            ∫ x, |Real.sqrt (G x ^ 2 + ε)| ^ p ∂μ :=
        integral_mono hRawInt hRegInt hPoint
      have hCurveLower :
          (∫ x, |G x| ^ p ∂μ) ^ (2 / p) ≤
            regularizedSourceLpCurve μ G ε p := by
        unfold regularizedSourceLpCurve
        exact Real.rpow_le_rpow (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (abs_nonneg _) _)) hIntMono
          (by positivity)
      have hCurveIncrement :
          regularizedSourceLpCurve μ G ε p ≤
            regularizedSourceLpCurve μ G ε 2 +
              (C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)) * (p - 2) := by
        apply actualRegularizedCurveIncrement_of_interior_derivative_bound
          (μ := μ) (G := G) (B := 2 * B) (ε := ε) (p := p)
          (D := C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p))
          hGmeas (by positivity) hGbound hε hp
        intro q hq
        have hder := hDerivativeUpperBound ε hε q hq
        simpa [G, mean] using hder
      have hCurveTwo :
          regularizedSourceLpCurve μ G ε 2 = (∫ x, G x ^ 2 ∂μ) + ε := by
        unfold regularizedSourceLpCurve
        rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
        have hGsqInt : Integrable (fun x => G x ^ 2) μ := by
          simpa [G, mean] using hPoincare.1
        have hpoint (x : EuclideanSpace ℝ ι) :
            |Real.sqrt (G x ^ 2 + ε)| ^ (2 : ℝ) = G x ^ 2 + ε := by
          calc
            |Real.sqrt (G x ^ 2 + ε)| ^ (2 : ℝ) =
                Real.sqrt (G x ^ 2 + ε) ^ (2 : ℕ) := by
                  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                  exact Real.rpow_natCast _ 2
            _ = G x ^ 2 + ε :=
              Real.sq_sqrt (show 0 ≤ G x ^ 2 + ε by positivity)
        rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
        rw [integral_add hGsqInt (integrable_const ε)]
        simp
      calc
        (∫ x, |G x| ^ p ∂μ) ^ (2 / p)
            ≤ regularizedSourceLpCurve μ G ε p := hCurveLower
        _ ≤ regularizedSourceLpCurve μ G ε 2 +
              (C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)) * (p - 2) := hCurveIncrement
        _ = (∫ x, G x ^ 2 ∂μ) + ε +
              (C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)) * (p - 2) := by rw [hCurveTwo]
        _ ≤ C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) + ε +
              (C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p)) * (p - 2) := by
              gcongr
        _ = C * (p - 1) * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) + ε := by ring
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa [G, mean] using hFinal ε hε

end

end LOOConcentration.Revision
