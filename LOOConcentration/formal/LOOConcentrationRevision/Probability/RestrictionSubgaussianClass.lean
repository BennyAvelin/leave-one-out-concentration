import LOOConcentrationRevision.Probability.SubgaussianClassSecondMoment
import LOOConcentrationRevision.Probability.RestrictedSubgaussian
import LOOConcentrationRevision.Probability.LipschitzIntegrability
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Conditional candidate transport for the whole event-local Lipschitz class.
The raw second moment is an internal obligation to be produced from the raw
subgaussian class before applying this helper in the whole infimum theorem. -/
theorem normalizedRestriction_local_hasSubgaussianMGF_of_class_and_norm_sq
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (K : Set (EuclideanSpace ℝ ι)) (hK : MeasurableSet K)
    (hq : 0 < μ.real K) (c : NNReal)
    (hClass : ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
      ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ)
    (hM2 : Integrable (fun x => ‖x‖^2) μ)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, |F x - F y| ≤ ‖x-y‖) :
    let ν := normalizedRestriction μ K
    Integrable F ν ∧ ProbabilityTheory.HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂ν)
      (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(c:ℝ)*Real.log (Real.exp 1/μ.real K))) ν := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  have hFK : LipschitzOnWith 1 F K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
      using hLip x hx y hy
  obtain ⟨G, hG, hEq⟩ := hFK.extend_real
  have hGμ : Integrable G μ := integrable_lipschitz_of_norm_sq μ hM2 G 1 hG
  have hK0 : μ K ≠ 0 := by
    intro hz
    have : μ.real K = 0 := by simp [Measure.real, hz]
    exact hq.ne' this
  have hGν : Integrable G ν := hGμ.restrict.smul_measure (ENNReal.inv_ne_top.mpr hK0)
  have hFG : F =ᵐ[ν] G := by
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem hK] with x hx
    exact hEq hx
  have hFν : Integrable F ν := (integrable_congr hFG).mpr hGν
  let X := fun x => G x - ∫ y, G y ∂μ
  have hXν : (∫ x, X x ∂ν) = (∫ x, G x ∂ν) - ∫ x, G x ∂μ := by
    dsimp [X]
    rw [integral_sub hGν (integrable_const _), integral_const]
    simp
  have hMeanFG : (∫ x, F x ∂ν) = ∫ x, G x ∂ν := integral_congr_ae hFG
  have hCenter : (fun x => X x - ∫ y, X y ∂ν) =ᵐ[ν]
      (fun x => F x - ∫ y, F y ∂ν) := by
    filter_upwards [hFG] with x hx
    rw [hXν, hMeanFG, hx]
    dsimp [X]
    ring
  have hSG := normalizedRestriction_centered_hasSubgaussianMGF μ K hq X c
    (hClass G hGμ hG)
  exact ⟨hFν, hSG.congr hCenter⟩

/-- Literal class-infimum comparison with an explicit internal moment obligation.
The successor source theorem must produce that obligation from membership in
the whole raw class, or treat its genuinely empty class as an infinite infimum. -/
theorem normalizedRestriction_subgaussian_class_infimum_le_of_norm_sq
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (K : Set (EuclideanSpace ℝ ι)) (hK : MeasurableSet K)
    (hq : 0 < μ.real K) (hM2 : Integrable (fun x => ‖x‖^2) μ) :
    let ν := normalizedRestriction μ K
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤
    ENNReal.ofReal ((3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K)) *
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ} := by
  let ν := normalizedRestriction μ K
  let A : Set ENNReal := {d | ∃ c : NNReal, d = (c : ENNReal) ∧
    ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
      ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ}
  let B : Set ENNReal := {d | ∃ c : NNReal, d = (c : ENNReal) ∧
    ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν → LipschitzWith 1 F →
      ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν}
  let a := (3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K)
  have hℓ : 1 ≤ Real.log (Real.exp 1/μ.real K) := by
    have hlog := Real.log_nonpos hq.le (measureReal_le_one (μ := μ) (s := K))
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hCandidate : ∀ d ∈ A, sInf B ≤ ENNReal.ofReal a * d := by
    intro d hd
    obtain ⟨c, rfl, hClass⟩ := hd
    let cν := Real.toNNReal (a*(c:ℝ))
    have hmem : (cν : ENNReal) ∈ B := by
      refine ⟨cν, rfl, ?_⟩
      intro F _hF hF
      have hLocal : ∀ x ∈ K, ∀ y ∈ K, |F x - F y| ≤ ‖x-y‖ := by
        intro x _hx y _hy
        simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
          using hF.dist_le_mul x y
      have h := (normalizedRestriction_local_hasSubgaussianMGF_of_class_and_norm_sq
        μ K hK hq c hClass hM2 F hLocal).2
      convert h using 1
      apply congrArg Real.toNNReal
      dsimp [a]
      ring
    calc
      sInf B ≤ (cν : ENNReal) := sInf_le hmem
      _ = ENNReal.ofReal a * (c:ENNReal) := by
        change ENNReal.ofReal (a*(c:ℝ)) = _
        rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_coe_nnreal]
  have hInf : (⨅ d : A, (d:ENNReal)) = sInf A := by
    apply le_antisymm
    · apply le_sInf
      intro d hd
      exact iInf_le_of_le ⟨d, hd⟩ le_rfl
    · exact le_iInf fun d => sInf_le d.property
  change sInf B ≤ ENNReal.ofReal a * sInf A
  rw [← hInf, ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
  exact le_iInf fun d => hCandidate d d.property

/-- The exact BNT comparison of literal whole subgaussian-class infima.
Every internal moment is produced from true class membership; the empty raw
class has its literal infinite infimum. No optimum or positive optimal proxy
is assumed, and no named surrogate constant is introduced. -/
theorem normalizedRestriction_subgaussian_class_infimum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (K : Set (EuclideanSpace ℝ ι)) (hK : MeasurableSet K)
    (hq : 0 < μ.real K) :
    let ν := normalizedRestriction μ K
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤
    ENNReal.ofReal ((3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K)) *
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ} := by
  classical
  let A : Set ENNReal := {d | ∃ c : NNReal, d = (c : ENNReal) ∧
    ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
      ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ}
  by_cases hA : A.Nonempty
  · obtain ⟨d, c, _hd, hClass⟩ := hA
    have hM2 := integrable_norm_sq_of_lipschitz_subgaussian_class μ c hClass
    exact normalizedRestriction_subgaussian_class_infimum_le_of_norm_sq μ K hK hq hM2
  · have hEmpty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    have hℓ : 1 ≤ Real.log (Real.exp 1/μ.real K) := by
      have hlog := Real.log_nonpos hq.le (measureReal_le_one (μ := μ) (s := K))
      rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
      linarith
    have ha : 0 < (3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K) := by
      positivity
    have ha0 := (ENNReal.ofReal_pos.mpr ha).ne'
    change _ ≤ ENNReal.ofReal ((3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K)) * sInf A
    rw [hEmpty, sInf_empty, ENNReal.mul_top ha0]
    exact le_top

/-- Event-local and ambient global Lipschitz proxy classes agree on the actual
normalized restriction: one McShane extension and AE mean transfer establish
both inclusions. This gives the same full bound on the induced event carrier. -/
theorem normalizedRestriction_local_subgaussian_class_infimum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (K : Set (EuclideanSpace ℝ ι)) (hK : MeasurableSet K)
    (hq : 0 < μ.real K) :
    let ν := normalizedRestriction μ K
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
        (∀ x ∈ K, ∀ y ∈ K, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤
    ENNReal.ofReal ((3*(2:ℝ)^12*Real.exp 2)*Real.log (Real.exp 1/μ.real K)) *
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c μ} := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  have hSets :
      {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
        ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
          (∀ x ∈ K, ∀ y ∈ K, |F x - F y| ≤ ‖x-y‖) →
          ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} =
      {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
        ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν → LipschitzWith 1 F →
          ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} := by
    ext d
    constructor
    · rintro ⟨c, hd, hClass⟩
      refine ⟨c, hd, ?_⟩
      intro F hF hLip
      apply hClass F hF
      intro x _hx y _hy
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
        using hLip.dist_le_mul x y
    · rintro ⟨c, hd, hClass⟩
      refine ⟨c, hd, ?_⟩
      intro F hF hLip
      have hFK : LipschitzOnWith 1 F K := by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
          using hLip x hx y hy
      obtain ⟨G, hG, hEq⟩ := hFK.extend_real
      have hFG : F =ᵐ[ν] G := by
        apply Measure.ae_smul_measure
        filter_upwards [ae_restrict_mem hK] with x hx
        exact hEq hx
      have hGν : Integrable G ν := (integrable_congr hFG).mp hF
      have hMean : (∫ y, F y ∂ν) = ∫ y, G y ∂ν := integral_congr_ae hFG
      have hCenter : (fun x => G x - ∫ y, G y ∂ν) =ᵐ[ν]
          (fun x => F x - ∫ y, F y ∂ν) := by
        filter_upwards [hFG] with x hx
        rw [hx, hMean]
      exact (hClass G hGν hG).congr hCenter
  change sInf _ ≤ _
  rw [hSets]
  exact normalizedRestriction_subgaussian_class_infimum_le μ K hK hq

end LOOConcentration.Revision
