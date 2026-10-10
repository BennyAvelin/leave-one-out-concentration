module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

public section

open Filter MeasureTheory Set Asymptotics
open Metric
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true

namespace LOOConcentration.Correspondence

private def derivativeRemainder {ι α : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι × α → ℝ)
    (L : (EuclideanSpace ℝ ι × α) →
      EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : EuclideanSpace ℝ ι × α)
    (h : EuclideanSpace ℝ ι) : ℝ :=
  F (p.1 + h, p.2) - F p - L p h

private theorem derivativeRemainder_continuous {ι α : Type*} [Fintype ι]
    {F : EuclideanSpace ℝ ι × α → ℝ}
    {L : (EuclideanSpace ℝ ι × α) →
      EuclideanSpace ℝ ι →L[ℝ] ℝ}
    (p : EuclideanSpace ℝ ι × α)
    (hF : ∀ z, Continuous (fun x => F (x, z))) :
    Continuous (derivativeRemainder F L p) := by
  change Continuous (fun h => F (p.1 + h, p.2) - F p - L p h)
  have hshift : Continuous (fun h : EuclideanSpace ℝ ι => p.1 + h) :=
    continuous_const.add continuous_id
  have hfirst : Continuous (fun h : EuclideanSpace ℝ ι => F (p.1 + h, p.2)) :=
    (hF p.2).comp hshift
  exact hfirst.sub continuous_const |>.sub (L p).continuous

private theorem ball_subset_closure_countableDense {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Dense S) {r : ℝ} :
    ball (0 : E) r ⊆ closure (S ∩ ball (0 : E) r) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hxball : dist x 0 < r := by simpa using hx
  have hgap : 0 < r - ‖x‖ := by simpa [dist_zero_right] using sub_pos.mpr hxball
  let ρ := min ε (r - ‖x‖) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ₁ : ρ < ε := by dsimp [ρ]; linarith [min_le_left ε (r - ‖x‖)]
  have hρ₂ : ρ < r - ‖x‖ := by dsimp [ρ]; linarith [min_le_right ε (r - ‖x‖)]
  let V := ball x ρ
  have hVopen : IsOpen V := isOpen_ball
  have hVnonempty : V.Nonempty := ⟨x, by simp [V, hρ]⟩
  obtain ⟨y, hyS, hyV⟩ := hS.exists_mem_open hVopen hVnonempty
  have hyx : dist y x < ρ := by simpa [V] using hyV
  have hyU : y ∈ U := hεU (by simpa [dist_comm] using hyx.trans hρ₁)
  have hyball : y ∈ ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖y‖ = dist y 0 := (dist_zero_right y).symm
      _ ≤ dist y x + dist x 0 := dist_triangle y x 0
      _ < ρ + ‖x‖ := add_lt_add_of_lt_of_le hyx (le_of_eq (dist_zero_right x))
      _ < r := by linarith
  exact ⟨y, hyU, ⟨hyS, hyball⟩⟩

private theorem hasFDerivAt_iff_countableApprox {ι α : Type*}
    [Fintype ι]
    {F : EuclideanSpace ℝ ι × α → ℝ}
    {L : (EuclideanSpace ℝ ι × α) →
      EuclideanSpace ℝ ι →L[ℝ] ℝ}
    (p : EuclideanSpace ℝ ι × α)
    (hF : ∀ z, Continuous (fun x => F (x, z)))
    {S : Set (EuclideanSpace ℝ ι)} (hS_dense : Dense S) :
    HasFDerivAt (fun x => F (x, p.2)) (L p) p.1 ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q ∈ S,
        q ∈ ball 0 ((1 / 2 : ℝ) ^ m) →
          ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖ := by
  constructor
  · intro h n
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at h
    have hε : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hev := h hε
    obtain ⟨r, hr, hr_bound⟩ := Metric.eventually_nhds_iff_ball.mp hev
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨m, fun q hqS hqball => ?_⟩
    have hqnorm : ‖q‖ < (1 / 2 : ℝ) ^ m := by
      simpa [Metric.mem_ball, dist_zero_right] using hqball
    have hqballr : q ∈ ball (0 : EuclideanSpace ℝ ι) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hqnorm.trans hm
    simpa [derivativeRemainder] using hr_bound q hqballr
  · intro h
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨m, hm⟩ := h n
    refine Metric.eventually_nhds_iff_ball.mpr ⟨(1 / 2 : ℝ) ^ m, by positivity, ?_⟩
    intro x hx
    have hclosed : IsClosed {y : EuclideanSpace ℝ ι |
        ‖derivativeRemainder F L p y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖} := by
      apply isClosed_le
      · exact (derivativeRemainder_continuous p hF).norm
      · exact continuous_const.mul continuous_norm
    have hsubset : S ∩ ball (0 : EuclideanSpace ℝ ι) ((1 / 2 : ℝ) ^ m) ⊆
        {y : EuclideanSpace ℝ ι |
          ‖derivativeRemainder F L p y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖} := by
      intro y hy
      exact hm y hy.1 hy.2
    have hmemClosure := (ball_subset_closure_countableDense hS_dense) hx
    have hle := closure_minimal hsubset hclosed hmemClosure
    calc
      ‖derivativeRemainder F L p x‖ ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := hle
      _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- If a jointly measurable real function has continuous data sections, the set on which a
jointly measurable candidate continuous linear map is its data derivative is measurable. -/
theorem measurableSet_hasFDerivAt_with_param
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    [MeasurableSpace (EuclideanSpace ℝ ι)] [BorelSpace (EuclideanSpace ℝ ι)]
    {F : EuclideanSpace ℝ ι × α → ℝ}
    (hF : Measurable F)
    (hF_cont : ∀ z, Continuous (fun x => F (x, z)))
    (L : (EuclideanSpace ℝ ι × α) →
      EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) :
    MeasurableSet {p : EuclideanSpace ℝ ι × α |
      HasFDerivAt (fun x => F (x, p.2)) (L p) p.1} := by
  classical
  let E := EuclideanSpace ℝ ι
  obtain ⟨S, hS_count, hS_dense⟩ : ∃ S : Set E, S.Countable ∧ Dense S :=
    TopologicalSpace.exists_countable_dense E
  let : Countable {q : E // q ∈ S} := hS_count.to_subtype
  have hrem_meas (q : E) :
      Measurable (fun p : E × α => derivativeRemainder F L p q) := by
    have hshift : Measurable (fun p : E × α => (p.1 + q, p.2)) := by
      exact (measurable_fst.add_const q).prodMk measurable_snd
    have hFshift : Measurable (fun p : E × α => F (p.1 + q, p.2)) :=
      hF.comp hshift
    have hLq : Measurable (fun p : E × α => L p q) :=
      (ContinuousLinearMap.measurable_apply q).comp hL
    change Measurable (fun p : E × α =>
      F (p.1 + q, p.2) - F (p.1, p.2) - L p q)
    exact (hFshift.sub hF).sub hLq
  have happrox (n m : ℕ) : MeasurableSet {p : E × α |
      ∀ q ∈ S, q ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
        ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖} := by
    have hform : {p : E × α |
        ∀ q ∈ S, q ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
          ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖} =
        ⋂ q : {q : E // q ∈ S}, {p |
          q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
          ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hp q
        exact hp q.val q.property
      · intro hp q hq
        exact hp ⟨q, hq⟩
    rw [hform]
    apply MeasurableSet.iInter
    intro q
    have hqmeas : Measurable (fun p : E × α =>
        ‖derivativeRemainder F L p q.val‖ - (1 / 2 : ℝ) ^ n * ‖q.val‖) := by
      exact (hrem_meas q.val).norm.sub measurable_const
    have hbound : MeasurableSet {p : E × α |
        ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} := by
      have hpre : MeasurableSet {p : E × α |
          ‖derivativeRemainder F L p q.val‖ - (1 / 2 : ℝ) ^ n * ‖q.val‖ ≤ 0} := by
        exact MeasurableSet.preimage
          (measurableSet_Iic : MeasurableSet (Iic (0 : ℝ))) hqmeas
      have heq : {p : E × α |
          ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} =
          {p | ‖derivativeRemainder F L p q.val‖ - (1 / 2 : ℝ) ^ n * ‖q.val‖ ≤ 0} := by
        ext p
        change (‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖) ↔
          ‖derivativeRemainder F L p q.val‖ - (1 / 2 : ℝ) ^ n * ‖q.val‖ ≤ 0
        exact sub_nonpos.symm
      rw [heq]
      exact hpre
    by_cases hq : q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m)
    · have heq : {p : E × α |
          q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
            ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} =
          {p | ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} := by
        ext p
        change (q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
            ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖) ↔
          ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖
        simp only [hq, true_implies]
      rw [heq]
      exact hbound
    · have heq : {p : E × α |
          q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
            ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖} =
          univ := by
        ext p
        change (q.val ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
            ‖derivativeRemainder F L p q.val‖ ≤ (1 / 2 : ℝ) ^ n * ‖q.val‖) ↔ True
        simp only [hq, false_implies]
      rw [heq]
      exact MeasurableSet.univ
  have hset_eq :
      {p : E × α |
        HasFDerivAt (fun x => F (x, p.2)) (L p) p.1} =
      {p | ∀ n : ℕ, ∃ m : ℕ, ∀ q ∈ S,
        q ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
          ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖} := by
    ext p
    exact hasFDerivAt_iff_countableApprox p hF_cont hS_dense
  rw [hset_eq]
  have hcount_eq : {p : E × α | ∀ n : ℕ, ∃ m : ℕ,
      ∀ q ∈ S, q ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
        ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖} =
      ⋂ n : ℕ, ⋃ m : ℕ, {p : E × α |
        ∀ q ∈ S, q ∈ ball (0 : E) ((1 / 2 : ℝ) ^ m) →
          ‖derivativeRemainder F L p q‖ ≤ (1 / 2 : ℝ) ^ n * ‖q‖} := by
    ext p
    simp
  rw [hcount_eq]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  exact happrox n m

/-- A constant-in-data section gives a direct consumer, even when the finite data index is empty. -/
theorem measurableSet_hasFDerivAt_constantSection_emptyIndex
    {α : Type*} [MeasurableSpace α]
    [MeasurableSpace (EuclideanSpace ℝ (Fin 0))]
    [BorelSpace (EuclideanSpace ℝ (Fin 0))]
    (g : α → ℝ) (hg : Measurable g) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin 0) × α |
      HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 0) => g p.2)
        (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) p.1} := by
  apply measurableSet_hasFDerivAt_with_param (F := fun p => g p.2)
    (L := fun _ => (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ))
  · exact hg.comp measurable_snd
  · intro z
    change Continuous (fun _ : EuclideanSpace ℝ (Fin 0) => g z)
    exact continuous_const
  · exact measurable_const

end LOOConcentration.Correspondence
