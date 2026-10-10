import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization
import LOOConcentration.Probability.DeletedTransport
import LOOConcentration.Probability.FittedConditionalRisk
import LOOConcentration.Probability.LooIntegrability
import LOOConcentration.Probability.SampleTestLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped MeasureTheory

noncomputable def standingRisk {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n) D

noncomputable def standingV {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  (∑ i : Fin (n + 2), meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ)

noncomputable def standingEV {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) : ℝ :=
  ∫ D : Dataset (Observation k m) (n + 2), standingV μ T L δ₁ δ₂ δ₃ c d hSt D
    ∂Measure.pi fun _ : Fin (n + 2) => μ

noncomputable def standingER {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) : ℝ :=
  ∫ D : Dataset (Observation k m) (n + 2), standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D
    ∂Measure.pi fun _ : Fin (n + 2) => μ

noncomputable def standingH {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D - looEstimate (T n) L D

noncomputable def standingI1 {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  standingV μ T L δ₁ δ₂ δ₃ c d hSt D - looEstimate (T n) L D

noncomputable def standingI2 {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  standingEV μ T L δ₁ δ₂ δ₃ c d hSt - standingV μ T L δ₁ δ₂ δ₃ c d hSt D

noncomputable def standingI3 {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D - standingER μ T L δ₁ δ₂ δ₃ c d hSt

noncomputable def standingB {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) : ℝ :=
  standingER μ T L δ₁ δ₂ δ₃ c d hSt - standingEV μ T L δ₁ δ₂ δ₃ c d hSt

/-- Joint held-out integrability follows from the frozen deleted-section field. -/
theorem standingShortLoss_integrable {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    Integrable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T n) L p.1 p.2) ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  let i : Fin (n + 2) := ⟨0, by omega⟩
  let f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
    fun p => fittedLoss (T n) L p.1 p.2
  have hm : Measurable f := hSt.stable.measurable_loss n
  have hc : Integrable (fun D : Dataset (Observation k m) (n + 2) => f (deleteAt D i, D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
    simpa only [f] using hSt.stable.integrable_deleted n i
  exact (deleted_section_integrable_iff μ i f hm.aestronglyMeasurable).mp hc

/-- Exact full-sample integrability for all terms in the risk error. -/
theorem standingLoss_integrability {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    Integrable (standingRisk μ T L δ₁ δ₂ δ₃ c d hSt) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (standingV μ T L δ₁ δ₂ δ₃ c d hSt) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looEstimate (T n) L) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (standingH μ T L δ₁ δ₂ δ₃ c d hSt) (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let f : Observation k m → ℝ := fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z)
  have hj := standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  have hf : Integrable f μ := by simpa only [f, meanFittedLoss] using hj.integral_prod_right
  have hcoord : ∀ i : Fin (n + 2), Integrable (fun D : Dataset (Observation k m) (n + 2) => f (D i)) ν := by
    intro i
    exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hsum : Integrable (fun D : Dataset (Observation k m) (n + 2) => ∑ i : Fin (n + 2), f (D i)) ν :=
    integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  have hV : Integrable (standingV μ T L δ₁ δ₂ δ₃ c d hSt) ν := by
    change Integrable (fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)) ν
    exact hsum.div_const (n + 2 : ℝ)
  have hR : Integrable (standingRisk μ T L δ₁ δ₂ δ₃ c d hSt) ν :=
    L1.integrable_coeFn (looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n))
  have hloo : Integrable (looEstimate (T n) L) ν := integrable_looEstimate μ (T n) L hj
  exact ⟨hR, hV, hloo, hR.sub hloo⟩

/-- The actual risk error is the four requested source components. -/
theorem standingLoss_decomposition {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) :
    standingH μ T L δ₁ δ₂ δ₃ c d hSt D =
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt D + standingI2 μ T L δ₁ δ₂ δ₃ c d hSt D +
      standingI3 μ T L δ₁ δ₂ δ₃ c d hSt D + standingB μ T L δ₁ δ₂ δ₃ c d hSt := by
  simp only [standingH, standingI1, standingI2, standingI3, standingB]
  ring

/-- Integrating the L1 conditional risk returns the full fitted-loss expectation. -/
theorem standingER_eq_joint {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    standingER μ T L δ₁ δ₂ δ₃ c d hSt =
      ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  have hf := hSt.stable.integrable_full n
  have hchar := looRiskL1_characterization μ (T (n + 1)) L hf
  have he := integral_congr_ae hchar
  have hm : MeasurableSpace.comap
      (Prod.fst : Dataset (Observation k m) (n + 2) × Observation k m →
        Dataset (Observation k m) (n + 2)) inferInstance ≤ (inferInstance : MeasurableSpace (Dataset (Observation k m) (n + 2) × Observation k m)) :=
    measurable_fst.comap_le
  calc
    standingER μ T L δ₁ δ₂ δ₃ c d hSt =
        ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (looRiskL1 μ (T (n + 1)) L hf) p.1 ∂(ν.prod μ) := by
      simp only [integral_fun_fst, probReal_univ, one_smul]
      rfl
    _ = ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (ν.prod μ)[(fun q : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T (n + 1)) L q.1 q.2) |
              MeasurableSpace.comap Prod.fst inferInstance] p ∂(ν.prod μ) := he.symm
    _ = ∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          fittedLoss (T (n + 1)) L p.1 p.2 ∂(ν.prod μ) := integral_condExp hm

/-- The expected mean validation equals the short-model product-law risk. -/
theorem standingEV_eq_joint {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    standingEV μ T L δ₁ δ₂ δ₃ c d hSt =
      ∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
        fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let f : Observation k m → ℝ := fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z)
  have hj := standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  have hf : Integrable f μ := by simpa only [f, meanFittedLoss] using hj.integral_prod_right
  have hcoord : ∀ i : Fin (n + 2), Integrable (fun D : Dataset (Observation k m) (n + 2) => f (D i)) ν := by
    intro i
    exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hcoordInt : ∀ i : Fin (n + 2),
      (∫ D : Dataset (Observation k m) (n + 2), f (D i) ∂ν) = ∫ z, f z ∂μ := by
    intro i
    let hmp := sample_coordinate_measurePreserving μ i
    have hfm : AEStronglyMeasurable f (Measure.map (fun D : Dataset (Observation k m) (n + 2) => D i) ν) := by
      rw [hmp.map_eq]
      exact hf.aestronglyMeasurable
    calc
      (∫ D : Dataset (Observation k m) (n + 2), f (D i) ∂ν) =
          ∫ z, f z ∂Measure.map (fun D : Dataset (Observation k m) (n + 2) => D i) ν :=
            (integral_map (measurable_pi_apply i).aemeasurable hfm).symm
      _ = ∫ z, f z ∂μ := by rw [hmp.map_eq]
  have havg : standingEV μ T L δ₁ δ₂ δ₃ c d hSt = ∫ z, f z ∂μ := by
    change (∫ D : Dataset (Observation k m) (n + 2), (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) ∂ν) = _
    rw [integral_div]
    rw [integral_finsetSum Finset.univ (fun i _ => hcoord i)]
    simp_rw [hcoordInt]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp [hN]
    push_cast
    ring
  have hfubini : (∫ z, f z ∂μ) =
      ∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
        fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
    simpa only [f, meanFittedLoss] using (integral_prod_symm
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m => fittedLoss (T n) L p.1 p.2) hj).symm
  exact havg.trans hfubini

/-- Exact frozen stability bias, with its original sample-size index. -/
theorem standingB_abs_le {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    |standingB μ T L δ₁ δ₂ δ₃ c d hSt| ≤ δ₃ (n + 2) := by
  let i : Fin (n + 2) := ⟨0, by omega⟩
  change |standingER μ T L δ₁ δ₂ δ₃ c d hSt -
    standingEV μ T L δ₁ δ₂ δ₃ c d hSt| ≤ δ₃ (n + 2)
  rw [standingER_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt,
    standingEV_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt]
  change |(∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
      fittedLoss (T (n + 1)) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) -
    (∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
      fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))| ≤ δ₃ (n + 2)
  calc
    |(∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) -
      (∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
        fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))| =
      |(∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
          fittedLoss (T n) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) -
        (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          fittedLoss (T (n + 1)) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| := abs_sub_comm _ _
    _ = |(∫ D : Dataset (Observation k m) (n + 2),
          fittedLoss (T n) L (deleteAt D i) (D i) ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          fittedLoss (T (n + 1)) L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| := by
            rw [← integral_heldout_fittedLoss μ (T n) L i (standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt)]
    _ ≤ δ₃ (n + 2) := hSt.stable.bias n i

#print axioms standingShortLoss_integrable
#print axioms standingLoss_integrability
#print axioms standingLoss_decomposition
#print axioms standingER_eq_joint
#print axioms standingEV_eq_joint
#print axioms standingB_abs_le

end LOOConcentration.Revision

namespace LOOConcentration.Revision
open MeasureTheory
private theorem three_component_tail {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (H I₁ I₂ I₃ : Ω → ℝ) (B b u v w ε : ℝ)
    (hEq : ∀ x, H x = I₁ x + I₂ x + I₃ x + B)
    (hB : B ≤ b) (hε : b + u + v + w ≤ ε) :
    ν.real {x | H x > ε} ≤
      ν.real {x | I₁ x > u} + ν.real {x | I₂ x > v} + ν.real {x | I₃ x > w} := by
  have hsub : {x | H x > ε} ⊆
      ({x | I₁ x > u} ∪ {x | I₂ x > v}) ∪ {x | I₃ x > w} := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hn
    have he := hEq x
    change ε < H x at hx
    linarith
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) (le_refl _)))

section
variable {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)

/-- The actual source three-term split, with deterministic bias absorbed into the risk threshold. -/
theorem standingLoss_main_tail_split (ε : ℝ) :
    let ν := Measure.pi fun _ : Fin (n+2) => μ
    let H := standingH μ T L δ₁ δ₂ δ₃ c d hSt
    let I₁ := standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
    let I₂ := standingI2 μ T L δ₁ δ₂ δ₃ c d hSt
    let I₃ := standingI3 μ T L δ₁ δ₂ δ₃ c d hSt
    (ν.real {D | H D > ε} ≤ ν.real {D | I₁ D > ε/3} +
      ν.real {D | I₂ D > ε/3} + ν.real {D | I₃ D > ε/3 - δ₃ (n+2)}) ∧
    (ν.real {D | -H D > ε} ≤ ν.real {D | -I₁ D > ε/3} +
      ν.real {D | -I₂ D > ε/3} + ν.real {D | -I₃ D > ε/3 - δ₃ (n+2)}) := by
  dsimp only
  have hB := standingB_abs_le μ T L δ₁ δ₂ δ₃ c d hSt
  constructor
  · apply three_component_tail _ _ _ _ _ (standingB μ T L δ₁ δ₂ δ₃ c d hSt)
      (δ₃ (n+2)) (ε/3) (ε/3) (ε/3-δ₃ (n+2)) ε
    · exact standingLoss_decomposition μ T L δ₁ δ₂ δ₃ c d hSt
    · exact (le_abs_self _).trans hB
    · linarith
  · apply three_component_tail _ _ _ _ _ (-standingB μ T L δ₁ δ₂ δ₃ c d hSt)
      (δ₃ (n+2)) (ε/3) (ε/3) (ε/3-δ₃ (n+2)) ε
    · intro D
      have he := standingLoss_decomposition μ T L δ₁ δ₂ δ₃ c d hSt D
      linarith
    · exact (neg_le_abs _).trans hB
    · linarith
end
#print axioms standingLoss_main_tail_split
end LOOConcentration.Revision
