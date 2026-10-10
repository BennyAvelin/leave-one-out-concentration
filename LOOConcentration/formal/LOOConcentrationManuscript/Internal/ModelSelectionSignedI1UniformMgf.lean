import LOOConcentrationManuscript.Internal.ModelSelectionDatasetConcentration
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Probability.DeletedTransport
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open LOOConcentration.Revision

private theorem finite_average_exp_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (X : Fin N → Ω → ℝ) (s K : ℝ)
    (hXmeas : ∀ i, AEStronglyMeasurable (X i) P)
    (hXexp : ∀ i, Integrable (fun ω => Real.exp (s * X i ω)) P ∧
      (∫ ω, Real.exp (s * X i ω) ∂P) ≤ Real.exp (K * s ^ 2)) :
    Integrable (fun ω => Real.exp (s * ((∑ i : Fin N, X i ω) / (N : ℝ)))) P ∧
      (∫ ω, Real.exp (s * ((∑ i : Fin N, X i ω) / (N : ℝ))) ∂P) ≤
        Real.exp (K * s ^ 2) := by
  let NR : ℝ := N
  have hNRpos : 0 < NR := by dsimp [NR]; exact_mod_cast hN
  have hNRne : NR ≠ 0 := ne_of_gt hNRpos
  have hweights : (∑ i : Fin N, (1 / NR : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NR]
    field_simp [hNRne]
  have hsumMeas : AEStronglyMeasurable
      (fun ω => ∑ i : Fin N, X i ω) P := by
    have hfun : (∑ i : Fin N, X i) = fun ω => ∑ i : Fin N, X i ω := by
      ext ω
      simp
    exact hfun ▸ Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hXmeas i)
  have havgMeas : AEStronglyMeasurable
      (fun ω => Real.exp (s * ((∑ i : Fin N, X i ω) / NR))) P := by
    have harg : AEStronglyMeasurable
        (fun ω => s * ((∑ i : Fin N, X i ω) / NR)) P := by
      have harg' : AEStronglyMeasurable
          (fun ω => (s / NR) * ∑ i : Fin N, X i ω) P :=
        hsumMeas.const_mul (s / NR)
      convert harg' using 1
      ext ω
      field_simp [hNRne]
    exact Real.continuous_exp.comp_aestronglyMeasurable harg
  have hsumInt : Integrable
      (fun ω => ∑ i : Fin N, Real.exp (s * X i ω)) P := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact (hXexp i).1
  have hjensen (ω : Ω) :
      Real.exp (s * ((∑ i : Fin N, X i ω) / NR)) ≤
        (∑ i : Fin N, Real.exp (s * X i ω)) / NR := by
    have hj := convexOn_exp.map_sum_le
      (t := Finset.univ) (w := fun _ : Fin N => (1 / NR : ℝ))
      (p := fun i => s * X i ω)
      (fun _ _ => by positivity) hweights (fun _ _ => Set.mem_univ _)
    have hleft : (∑ i : Fin N, (1 / NR : ℝ) * (s * X i ω)) =
        s * ((∑ i : Fin N, X i ω) / NR) := by
      simp only [← Finset.mul_sum]
      ring
    have hright : (∑ i : Fin N, (1 / NR : ℝ) * Real.exp (s * X i ω)) =
        (∑ i : Fin N, Real.exp (s * X i ω)) / NR := by
      simp only [← Finset.mul_sum]
      ring
    simpa only [smul_eq_mul, hleft, hright] using hj
  have havgInt : Integrable
      (fun ω => Real.exp (s * ((∑ i : Fin N, X i ω) / NR))) P := by
    apply (hsumInt.div_const NR).mono' havgMeas
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hjensen ω
  have hsumBound :
      (∑ i : Fin N, ∫ ω, Real.exp (s * X i ω) ∂P) ≤
        (N : ℝ) * Real.exp (K * s ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin N, Real.exp (K * s ^ 2) :=
        Finset.sum_le_sum fun i _ => (hXexp i).2
      _ = (N : ℝ) * Real.exp (K * s ^ 2) := by simp
  refine ⟨havgInt, ?_⟩
  calc
    (∫ ω, Real.exp (s * ((∑ i : Fin N, X i ω) / NR)) ∂P) ≤
        ∫ ω, (∑ i : Fin N, Real.exp (s * X i ω)) / NR ∂P :=
      integral_mono_ae havgInt (hsumInt.div_const NR)
        (Filter.Eventually.of_forall fun ω => hjensen ω)
    _ = (∑ i : Fin N, ∫ ω, Real.exp (s * X i ω) ∂P) / NR := by
      rw [integral_div, integral_finsetSum Finset.univ (fun i _ => (hXexp i).1)]
    _ ≤ Real.exp (K * s ^ 2) := by
      apply (div_le_iff₀ hNRpos).2
      simpa only [NR, mul_comm] using hsumBound

private theorem actual_signed_i1_average_mgf_of_section_bounds
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (s K : ℝ)
    (hJoint : Measurable F)
    (hI : Integrable F
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hMeanLoc : LocallyLipschitz
      (fun z => ∫ E, F (E, z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (hSections : ∀ᵐ z ∂μ,
      Integrable (fun E => Real.exp
        (s * ((∫ E', F (E', z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) - F (E, z))))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      (∫ E, Real.exp
        (s * ((∫ E', F (E', z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) - F (E, z)))
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)) ≤ Real.exp (K * s ^ 2)) :
    Integrable
      (fun D : Dataset (Observation k m) (n + 2) => Real.exp
        (s * ((∑ i : Fin (n + 2),
          ((∫ E, F (E, D i) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
            F (deleteAt D i, D i))) / (n + 2 : ℝ))))
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    (∫ D : Dataset (Observation k m) (n + 2), Real.exp
      (s * ((∑ i : Fin (n + 2),
        ((∫ E, F (E, D i) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
          F (deleteAt D i, D i))) / (n + 2 : ℝ)))
      ∂Measure.pi fun _ : Fin (n + 2) => μ) ≤ Real.exp (K * s ^ 2) := by
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
  let H : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
    fun p => Real.exp (s * (f p.2 - F p))
  have hfInt : Integrable f μ := by
    simpa only [f, Q] using hI.integral_prod_right
  have hfMeas : Measurable f := by
    have hcont : Continuous f := by
      simpa only [f, Q] using hMeanLoc.continuous
    exact hcont.measurable
  have hHMeas : Measurable H := by
    dsimp [H]
    exact Real.continuous_exp.measurable.comp
      (measurable_const.mul ((hfMeas.comp measurable_snd).sub hJoint))
  have hHsm : AEStronglyMeasurable H (Q.prod μ) := hHMeas.aestronglyMeasurable
  have hSections' : ∀ᵐ z ∂μ, Integrable (fun E => H (E, z)) Q ∧
      (∫ E, H (E, z) ∂Q) ≤ Real.exp (K * s ^ 2) := by
    simpa only [H, f, Q] using hSections
  have hInnerMeas : AEStronglyMeasurable
      (fun z => ∫ E, ‖H (E, z)‖ ∂Q) μ := hHsm.norm.prod_swap.integral_prod_right'
  have hInnerInt : Integrable (fun z => ∫ E, ‖H (E, z)‖ ∂Q) μ := by
    have hConst : Integrable (fun _ : Observation k m => Real.exp (K * s ^ 2)) μ :=
      integrable_const _
    apply hConst.mono' hInnerMeas
    filter_upwards [hSections'] with z hz
    calc
      ‖∫ E, ‖H (E, z)‖ ∂Q‖ = ∫ E, ‖H (E, z)‖ ∂Q := by
        rw [Real.norm_of_nonneg (integral_nonneg (fun E => norm_nonneg (H (E, z))))]
      _ = ∫ E, H (E, z) ∂Q := by
        apply integral_congr_ae
        filter_upwards with E
        exact Real.norm_of_nonneg (Real.exp_nonneg _)
      _ ≤ Real.exp (K * s ^ 2) := hz.2
  have hHInt : Integrable H (Q.prod μ) :=
    (integrable_prod_iff' hHsm).2 ⟨hSections'.mono fun z hz => hz.1, hInnerInt⟩
  have hOuterInt : Integrable (fun z => ∫ E, H (E, z) ∂Q) μ :=
    hHInt.integral_prod_right
  have hOuterBound : (∫ z, (∫ E, H (E, z) ∂Q) ∂μ) ≤ Real.exp (K * s ^ 2) := by
    have hConst : Integrable (fun _ : Observation k m => Real.exp (K * s ^ 2)) μ :=
      integrable_const _
    calc
      _ ≤ ∫ z, (fun _ : Observation k m => Real.exp (K * s ^ 2)) z ∂μ := by
        apply integral_mono_ae hOuterInt hConst
        filter_upwards [hSections'] with z hz
        exact hz.2
      _ = Real.exp (K * s ^ 2) := by simp
  have hProductIntegral : (∫ p, H p ∂(Q.prod μ)) =
      ∫ z, (∫ E, H (E, z) ∂Q) ∂μ := by
    exact integral_prod_symm H hHInt
  have hHBound : (∫ p, H p ∂(Q.prod μ)) ≤ Real.exp (K * s ^ 2) := by
    rw [hProductIntegral]
    exact hOuterBound
  have hHIntDelete (i : Fin (n + 2)) :
      Integrable (fun D : Dataset (Observation k m) (n + 2) => H (deleteAt D i, D i)) P :=
    deleted_section_integrable μ i H hHInt
  have hHIntegralDelete (i : Fin (n + 2)) :
      (∫ D : Dataset (Observation k m) (n + 2), H (deleteAt D i, D i) ∂P) =
        ∫ p : Dataset (Observation k m) (n + 1) × Observation k m, H p ∂(Q.prod μ) :=
    deleted_section_integral μ i H hHInt
  let X : Fin (n + 2) → Dataset (Observation k m) (n + 2) → ℝ := fun i D =>
    f (D i) - F (deleteAt D i, D i)
  have hXexp : ∀ i : Fin (n + 2),
      Integrable (fun D => Real.exp (s * X i D)) P ∧
      (∫ D, Real.exp (s * X i D) ∂P) ≤ Real.exp (K * s ^ 2) := by
    intro i
    have hEq : (fun D : Dataset (Observation k m) (n + 2) =>
        Real.exp (s * X i D)) = fun D => H (deleteAt D i, D i) := by
      funext D
      simp only [X, H, f]
    have hEqAE : (fun D : Dataset (Observation k m) (n + 2) =>
        H (deleteAt D i, D i)) =ᵐ[P] fun D => Real.exp (s * X i D) := by
      filter_upwards [] with D
      exact (congrFun hEq D).symm
    have hEqAE' : (fun D : Dataset (Observation k m) (n + 2) =>
        Real.exp (s * X i D)) =ᵐ[P] fun D => H (deleteAt D i, D i) := by
      filter_upwards [] with D
      exact congrFun hEq D
    constructor
    · exact (hHIntDelete i).congr hEqAE
    · rw [show (∫ D, Real.exp (s * X i D) ∂P) =
        ∫ D, H (deleteAt D i, D i) ∂P by exact integral_congr_ae hEqAE']
      rw [hHIntegralDelete]
      exact hHBound
  have hXmeas : ∀ i : Fin (n + 2), AEStronglyMeasurable (X i) P := by
    intro i
    have hsum : AEStronglyMeasurable
        (fun D : Dataset (Observation k m) (n + 2) => f (D i)) P :=
      (hfMeas.comp (measurable_pi_apply i)).aestronglyMeasurable
    have hdel : AEStronglyMeasurable
        (fun D : Dataset (Observation k m) (n + 2) => F (deleteAt D i, D i)) P := by
      exact (deleted_section_measurable μ i F hJoint).aestronglyMeasurable
    exact hsum.sub hdel
  have hAvg := finite_average_exp_integrable_bound P (by omega) X s K hXmeas hXexp
  simpa only [P, X, f, Q, Finset.sum_sub_distrib, Finset.sum_div,
    Nat.cast_add, Nat.cast_ofNat] using hAvg

/-- The actual signed short-section I₁ MGF in the bounded-gradient regime.
The fit difference is literal, the short training law has size `n + 1`, and
finite exponential Jensen gives the same sharp proxy for the full `n + 2`
sample average. -/
theorem modelSelection_signed_i1_uniform_mgf_bounded
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hJoint : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hI : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hMeanLoc : LocallyLipschitz (fun z => ∫ E : Dataset (Observation k m) (n + 1),
      fittedLoss (T₀ n) L E z - fittedLoss (T₁ n) L E z
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (hLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
        fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (a : ℝ) (ha : 0 ≤ a)
    (hδ₁ : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hδ₂zero : ∀ᵐ z ∂μ, δ₂ (n + 1) z = 0)
    (s : ℝ) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    Integrable (fun D : Dataset (Observation k m) (n + 2) => Real.exp
      (s * ((∑ i : Fin (n + 2),
        ((∫ E : Dataset (Observation k m) (n + 1),
            fittedLoss (T₀ n) L E (D i) - fittedLoss (T₁ n) L E (D i)
              ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i)))) / (n + 2 : ℝ)))) P ∧
    (∫ D : Dataset (Observation k m) (n + 2), Real.exp
      (s * ((∑ i : Fin (n + 2),
        ((∫ E : Dataset (Observation k m) (n + 1),
            fittedLoss (T₀ n) L E (D i) - fittedLoss (T₁ n) L E (D i)
              ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i)))) / (n + 2 : ℝ))) ∂P) ≤
      Real.exp (((observationLogSobolevConstant μ).toReal * a ^ 2 / 2) * s ^ 2) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
  have hgradBound : ∀ᵐ z ∂μ,
      LocallyLipschitz (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
        F (datasetOfEuclidean x, z)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
        (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean x, z)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean x, z)) x‖ ≤ a := by
    filter_upwards [hLoc, hGrad, hδ₁, hδ₂zero] with z hloc hgrad hδ₁z hδ₂z
    refine ⟨?_, ?_⟩
    · simpa only [F] using hloc
    · filter_upwards [hgrad] with x hx
      refine ⟨?_, ?_⟩
      · simpa only [F] using hx.1
      · calc
          _ ≤ δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖ := hx.2
          _ = δ₁ (n + 1) z := by rw [hδ₂z]; simp
          _ ≤ a := hδ₁z
  have hSections : ∀ᵐ z ∂μ,
      Integrable (fun E => Real.exp
        (s * (f z - F (E, z)))) Q ∧
      (∫ E, Real.exp (s * (f z - F (E, z))) ∂Q) ≤
        Real.exp (((observationLogSobolevConstant μ).toReal * a ^ 2 / 2) * s ^ 2) := by
    filter_upwards [hgradBound] with z hz
    have hmgf := original_dataset_signed_centered_mgf_bounded_gradient μ
      (fun E : Dataset (Observation k m) (n + 1) => F (E, z))
      hfinite hM₂ hz.1 a ha hz.2 (-s)
    dsimp only at hmgf
    have hmean : (∫ E, F (E, z) ∂Q) = f z := by rfl
    have hEq : (fun E : Dataset (Observation k m) (n + 1) =>
        Real.exp (s * (f z - F (E, z)))) = fun E =>
        Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) := by
      funext E
      congr 1
      rw [← hmean]
      ring
    have hEqAE : (fun E : Dataset (Observation k m) (n + 1) =>
        Real.exp (s * (f z - F (E, z)))) =ᵐ[Q] fun E =>
        Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) := by
      filter_upwards [] with E
      exact congrFun hEq E
    constructor
    · exact hmgf.2.1.congr hEqAE.symm
    · have hbound := hmgf.2.2.1
      calc
        _ = ∫ E, Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) ∂Q :=
          integral_congr_ae hEqAE
        _ ≤ Real.exp (((observationLogSobolevConstant μ).toReal * a ^ 2 / 2) * s ^ 2) := by
          have hsq : (-s) ^ 2 = s ^ 2 := by ring
          simpa only [hsq] using hbound
  have h := actual_signed_i1_average_mgf_of_section_bounds μ F s
    ((observationLogSobolevConstant μ).toReal * a ^ 2 / 2)
    (by simpa only [F] using hJoint) (by simpa only [F, Q] using hI)
    (by simpa only [F, Q] using hMeanLoc) hSections
  simpa only [P, Q, F, f, Finset.sum_sub_distrib, Finset.sum_div,
    Nat.cast_add, Nat.cast_ofNat] using h

/-- The actual signed short-section I₁ MGF for positive gradient growth.
The raw observation second moment and native short-size coefficient are kept
unchanged, and the source cutoff is retained exactly. -/
theorem modelSelection_signed_i1_uniform_mgf_positive_growth
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hJoint : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hI : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hMeanLoc : LocallyLipschitz (fun z => ∫ E : Dataset (Observation k m) (n + 1),
      fittedLoss (T₀ n) L E z - fittedLoss (T₁ n) L E z
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (hLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
        fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
            fittedLoss (T₁ n) L (datasetOfEuclidean x) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbpos : 0 < b)
    (hδ₁ : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ a)
    (hδ₂ : ∀ᵐ z ∂μ, δ₂ (n + 1) z ≤ b)
    (s : ℝ)
    (hcut : |s| ≤ 1 /
      (4 * (observationLogSobolevConstant μ).toReal * b)) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    Integrable (fun D : Dataset (Observation k m) (n + 2) => Real.exp
      (s * ((∑ i : Fin (n + 2),
        ((∫ E : Dataset (Observation k m) (n + 1),
            fittedLoss (T₀ n) L E (D i) - fittedLoss (T₁ n) L E (D i)
              ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i)))) / (n + 2 : ℝ)))) P ∧
    (∫ D : Dataset (Observation k m) (n + 2), Real.exp
      (s * ((∑ i : Fin (n + 2),
        ((∫ E : Dataset (Observation k m) (n + 1),
            fittedLoss (T₀ n) L E (D i) - fittedLoss (T₁ n) L E (D i)
              ∂(Measure.pi fun _ : Fin (n + 1) => μ)) -
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i)))) / (n + 2 : ℝ))) ∂P) ≤
      Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
        (a ^ 2 + 2 * b ^ 2 * ((n + 1 : ℕ) : ℝ) *
          (∫ y, observationNormSq y ∂μ)) * s ^ 2)) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ E, F (E, z) ∂Q
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let K : ℝ := 2 * C * (a ^ 2 + 2 * b ^ 2 * ((n + 1 : ℕ) : ℝ) * M₂)
  have hgradGrowth : ∀ᵐ z ∂μ,
      LocallyLipschitz (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
        F (datasetOfEuclidean x, z)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
        (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean x, z)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean x, z)) x‖ ≤
          a + b * ‖x‖ := by
    filter_upwards [hLoc, hGrad, hδ₁, hδ₂] with z hloc hgrad hδ₁z hδ₂z
    refine ⟨?_, ?_⟩
    · simpa only [F] using hloc
    · filter_upwards [hgrad] with x hx
      refine ⟨?_, ?_⟩
      · simpa only [F] using hx.1
      · calc
          _ ≤ δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖ := hx.2
          _ ≤ a + b * ‖x‖ := by
            have hmul := mul_le_mul_of_nonneg_right hδ₂z (norm_nonneg x)
            linarith
  have hSections : ∀ᵐ z ∂μ,
      Integrable (fun E => Real.exp
        (s * (f z - F (E, z)))) Q ∧
      (∫ E, Real.exp (s * (f z - F (E, z))) ∂Q) ≤ Real.exp (K * s ^ 2) := by
    filter_upwards [hgradGrowth] with z hz
    have hmgf := original_dataset_signed_centered_mgf_positive_growth μ
      (fun E : Dataset (Observation k m) (n + 1) => F (E, z))
      hfinite hM₂ hz.1 a b ha hb hbpos hz.2 (-s)
      (by simpa only [abs_neg] using hcut)
    dsimp only at hmgf
    have hmean : (∫ E, F (E, z) ∂Q) = f z := by rfl
    have hEq : (fun E : Dataset (Observation k m) (n + 1) =>
        Real.exp (s * (f z - F (E, z)))) = fun E =>
        Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) := by
      funext E
      congr 1
      rw [← hmean]
      ring
    have hEqAE : (fun E : Dataset (Observation k m) (n + 1) =>
        Real.exp (s * (f z - F (E, z)))) =ᵐ[Q] fun E =>
        Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) := by
      filter_upwards [] with E
      exact congrFun hEq E
    constructor
    · exact hmgf.2.1.congr hEqAE.symm
    · have hbound := hmgf.2.2.1
      calc
        _ = ∫ E, Real.exp ((-s) * (F (E, z) - ∫ E', F (E', z) ∂Q)) ∂Q :=
          integral_congr_ae hEqAE
        _ ≤ Real.exp (K * s ^ 2) := by
          have hsq : (-s) ^ 2 = s ^ 2 := by ring
          simpa only [C, M₂, K, hsq] using hbound
  have h := actual_signed_i1_average_mgf_of_section_bounds μ F s K
    (by simpa only [F] using hJoint) (by simpa only [F, Q] using hI)
    (by simpa only [F, Q] using hMeanLoc) hSections
  simpa only [P, Q, F, f, Finset.sum_sub_distrib, Finset.sum_div,
    Nat.cast_add, Nat.cast_ofNat, C, M₂, K] using h

end LOOConcentration.Manuscript.Internal
