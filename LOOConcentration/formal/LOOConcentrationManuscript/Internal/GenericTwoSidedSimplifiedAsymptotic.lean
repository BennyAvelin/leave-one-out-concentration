import LOOConcentrationRevision.Concentration.SimplifiedUniformTailConsumer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LOOConcentration.Manuscript.Internal

private theorem measureReal_mono_subset
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hst : s ⊆ t) : μ.real s ≤ μ.real t := by
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (by finiteness) (measure_mono hst)

private theorem sq_le_sq_of_nonneg_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx)
  nlinarith only [hprod]

/-- The source's generic two-sided eventual concentration clause. A single
Gaussian constant is fixed from the rate parameters before the dimensions, law,
estimator, loss, sample size, and deviation threshold are chosen. -/
theorem generic_eventual_two_sided_sixN :
    (∀ (C A B : NNReal), ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (k m : ℕ) (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
        (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
        (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ c d : ℕ → ℝ)
        (_hC : (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal = (C : ℝ))
        (hstanding : ∀ n, LOOConcentration.Revision.StandingAssumption
          (n := n) μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1)))
        (_hzero : ∀ n z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
        (_hLip : ∀ n z w,
          |LOOConcentration.Revision.meanFittedLoss μ (T n) L z
              ((hstanding n).mean_integrable z) -
            LOOConcentration.Revision.meanFittedLoss μ (T n) L w
              ((hstanding n).mean_integrable w)| ≤
            c (n + 1) * observationNorm (z - w))
        (_hc : ∀ n, c (n + 1) ≤ (B : ℝ))
        (_hδ₁ : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) ∧
          δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ)),
        ∀ (ε : ℝ) (_hε : 0 < ε), ∃ nε : ℕ, ∀ n ≥ nε,
          let ν := Measure.pi fun _ : Fin (n + 2) => μ
          let H := fun D =>
            (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
              ((hstanding n).stable.integrable_full n)) D -
              looEstimate (T n) L D
          ν.real {D | |H D| > ε} ≤
            6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) ∧
          ν.real {D | -H D > ε} ≤
            3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) := by
  intro C A B
  let S : ℝ := 3 * (A : ℝ) + (B : ℝ)
  let K : ℝ := (C : ℝ) * S ^ 2
  let c₀ : ℝ := 1 / (8 * (K + 1))
  refine ⟨c₀, ?_, ?_⟩
  · dsimp [c₀, K, S]
    positivity
  · intro k m μ hμ T L δ₁ δ₂ δ₃ c d hC hstanding hzero hLip hc hδ₁ ε hε
    have hεhalf : 0 < ε / 2 := by linarith
    have hδevent : ∀ᶠ q : ℕ in atTop, δ₃ (q + 2) < ε / 2 := by
      exact (hstanding 0).stable.delta₃_tendsto.eventually
        (Iio_mem_nhds hεhalf)
    obtain ⟨nε, hnε⟩ := Filter.eventually_atTop.1 hδevent
    refine ⟨nε, ?_⟩
    intro n hn
    have hδsmall : δ₃ (n + 2) < ε / 2 := hnε n hn
    let ν : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
        ((hstanding n).stable.integrable_full n)) D -
        looEstimate (T n) L D
    let q : ℝ := (n + 2 : ℝ)
    have hq : 0 < q := by dsimp [q]; positivity
    let a : NNReal := ⟨(A : ℝ) / Real.sqrt (n + 1 : ℝ), by positivity⟩
    have ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) := by
      filter_upwards [hδ₁ n] with z hz
      exact hz.1
    have hδfull : ∀ᵐ z ∂μ,
        δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
      filter_upwards [hδ₁ n] with z hz
      exact hz.2
    have hmean : (∫ z, δ₁ (n + 2) z ∂μ) ≤
        (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
      calc
        (∫ z, δ₁ (n + 2) z ∂μ) ≤
            ∫ _z : Observation k m,
              (A : ℝ) / Real.sqrt (n + 2 : ℝ) ∂μ :=
          integral_mono_ae (hstanding n).delta₁_full_integrable
            (integrable_const _) hδfull
        _ = (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by simp
    have hroot : Real.sqrt (n + 2 : ℝ) ≤ 2 * Real.sqrt (n + 1 : ℝ) := by
      have hs := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hsq : (n + 2 : ℝ) ≤ (2 * Real.sqrt (n + 1 : ℝ)) ^ 2 := by
        nlinarith only [hs, hn]
      have hroot' := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hroot'
      exact hroot'
    have hratio : 1 / Real.sqrt (n + 1 : ℝ) ≤
        2 / Real.sqrt (n + 2 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa using hroot
    have haBound : (a : ℝ) ≤ 2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
      change (A : ℝ) / Real.sqrt (n + 1 : ℝ) ≤ _
      calc
        (A : ℝ) / Real.sqrt (n + 1 : ℝ) =
            (A : ℝ) * (1 / Real.sqrt (n + 1 : ℝ)) := by ring
        _ ≤ (A : ℝ) * (2 / Real.sqrt (n + 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by ring
    have hcBound : c (n + 1) / Real.sqrt (n + 2 : ℝ) ≤
        (B : ℝ) / Real.sqrt (n + 2 : ℝ) :=
      div_le_div_of_nonneg_right (hc n) (Real.sqrt_nonneg _)
    let s : ℝ := (a : ℝ) + c (n + 1) / Real.sqrt (n + 2 : ℝ) +
      ∫ z, δ₁ (n + 2) z ∂μ
    have hsUpper : s ≤ S / Real.sqrt q := by
      dsimp [s, S, q]
      calc
        (a : ℝ) + c (n + 1) / Real.sqrt (n + 2 : ℝ) +
            ∫ z, δ₁ (n + 2) z ∂μ ≤
            2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) +
              (B : ℝ) / Real.sqrt (n + 2 : ℝ) +
              (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
          linarith [haBound, hcBound, hmean]
        _ = (3 * (A : ℝ) + (B : ℝ)) / Real.sqrt (n + 2 : ℝ) := by ring
    have hsNonneg : 0 ≤ s := by
      have hmeanNonneg : 0 ≤ ∫ z, δ₁ (n + 2) z ∂μ :=
        integral_nonneg fun z => (hstanding n).stable.delta₁_nonneg (n + 1) z
      have haNonneg : 0 ≤ (a : ℝ) := NNReal.coe_nonneg _
      have hcNonneg : 0 ≤ c (n + 1) := (hstanding n).c_nonneg
      dsimp [s]
      linarith [div_nonneg hcNonneg (Real.sqrt_nonneg (n + 2 : ℝ)), hmeanNonneg]
    have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
    have hupperNonneg : 0 ≤ S / Real.sqrt q :=
      div_nonneg hSnonneg (Real.sqrt_nonneg _)
    have hsSquared : s ^ 2 ≤ (S / Real.sqrt q) ^ 2 :=
      sq_le_sq_of_nonneg_le hsNonneg hsUpper
    have hsScale : s ^ 2 ≤ S ^ 2 / q := by
      calc
        s ^ 2 ≤ (S / Real.sqrt q) ^ 2 := hsSquared
        _ = S ^ 2 / q := by rw [div_pow, Real.sq_sqrt (le_of_lt hq)]
    let V : ℝ := (C : ℝ) * s ^ 2
    have hVnonneg : 0 ≤ V := by dsimp [V]; positivity
    have hVscale : V ≤ K / q := by
      dsimp [V, K]
      calc
        (C : ℝ) * s ^ 2 ≤ (C : ℝ) * (S ^ 2 / q) :=
          mul_le_mul_of_nonneg_left hsScale (by positivity)
        _ = ((C : ℝ) * S ^ 2) / q := by ring
    have hVq : V * q ≤ K := (le_div_iff₀ hq).mp hVscale
    have hTail := LOOConcentration.Revision.simplified_uniform_tail μ T L δ₁ δ₂ δ₃
      (c (n + 1)) (d (n + 1))
      (hstanding n) (hzero n) (hLip n) a ha (ε / 2) hεhalf
    have hSourceTailAbs : ν.real {D | |H D| > δ₃ (n + 2) + ε / 2} ≤
        2 * (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) := by
      simpa [ν, H, s, V, hC] using hTail.1
    have hSourceTailOpp : ν.real {D | -H D > δ₃ (n + 2) + ε / 2} ≤
        (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) := by
      simpa [ν, H, s, V, hC] using hTail.2.2
    have hAbsSub : {D | |H D| > ε} ⊆
        {D | |H D| > δ₃ (n + 2) + ε / 2} := by
      intro D hD
      change ε < |H D| at hD
      change δ₃ (n + 2) + ε / 2 < |H D|
      linarith
    have hOppSub : {D | -H D > ε} ⊆
        {D | -H D > δ₃ (n + 2) + ε / 2} := by
      intro D hD
      change ε < -H D at hD
      change δ₃ (n + 2) + ε / 2 < -H D
      linarith
    have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
    have hKplus : 0 < K + 1 := by linarith
    have hGauss : (if V = 0 then 0 else
        Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) ≤
        Real.exp (-(c₀ * ε ^ 2 * q)) := by
      by_cases hVzero : V = 0
      · simp [hVzero]
        exact (Real.exp_pos _).le
      · have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hVzero)
        have hfactor : q / (K + 1) ≤ 1 / V := by
          apply (div_le_div_iff₀ hKplus hVpos).2
          calc
            q * V = V * q := by ring
            _ ≤ K := hVq
            _ ≤ K + 1 := le_add_of_nonneg_right (by norm_num)
            _ = 1 * (K + 1) := by ring
        have harg : c₀ * ε ^ 2 * q ≤
            (ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2) := by
          calc
            c₀ * ε ^ 2 * q = (ε ^ 2 / 8) * (q / (K + 1)) := by
              dsimp [c₀]
              field_simp [hKplus.ne']
            _ ≤ (ε ^ 2 / 8) * (1 / V) :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            _ = (ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2) := by
              rw [← show (C : ℝ) * s ^ 2 = V by rfl]
              field_simp [hVpos.ne']
              ring
        simpa [hVzero] using Real.exp_le_exp.mpr (neg_le_neg harg)
    have h3q : 1 ≤ 3 * q := by
      have hq2 : 2 ≤ q := by
        dsimp [q]
        have hn : 0 ≤ (n : ℝ) := by positivity
        linarith only [hn]
      linarith only [hq2]
    have h6q : 2 ≤ 6 * q := by nlinarith only [h3q]
    have hAbsGauss :
        2 * (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) ≤
        6 * q * Real.exp (-(c₀ * ε ^ 2 * q)) := by
      calc
        _ ≤ 2 * Real.exp (-(c₀ * ε ^ 2 * q)) :=
          mul_le_mul_of_nonneg_left hGauss (by norm_num)
        _ ≤ 6 * q * Real.exp (-(c₀ * ε ^ 2 * q)) :=
          mul_le_mul_of_nonneg_right h6q (Real.exp_nonneg _)
    have hOppGauss :
        (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) ≤
        3 * q * Real.exp (-(c₀ * ε ^ 2 * q)) := by
      calc
        _ ≤ Real.exp (-(c₀ * ε ^ 2 * q)) := hGauss
        _ ≤ 3 * q * Real.exp (-(c₀ * ε ^ 2 * q)) := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right h3q (Real.exp_nonneg _))
    refine ⟨?_, ?_⟩
    · calc
        ν.real {D | |H D| > ε} ≤
            ν.real {D | |H D| > δ₃ (n + 2) + ε / 2} :=
          measureReal_mono_subset hAbsSub
        _ ≤ 2 * (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) := hSourceTailAbs
        _ ≤ 6 * q * Real.exp (-(c₀ * ε ^ 2 * q)) := hAbsGauss
    · calc
        ν.real {D | -H D > ε} ≤
            ν.real {D | -H D > δ₃ (n + 2) + ε / 2} :=
          measureReal_mono_subset hOppSub
        _ ≤ (if V = 0 then 0 else
          Real.exp (-((ε / 2) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) := hSourceTailOpp
        _ ≤ 3 * q * Real.exp (-(c₀ * ε ^ 2 * q)) := hOppGauss

end LOOConcentration.Manuscript.Internal
