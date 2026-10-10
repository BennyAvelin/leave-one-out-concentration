import LOOConcentration.Results.GoodSetExtension
import LOOConcentration.Probability.SampleMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# L² control and mean transfer for the good-set extension

This file consumes the reviewed McShane extension from
`LOOConcentration.Results.GoodSetExtension` and the exact dataset second-moment identity.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

private theorem datasetNorm_measurable_for_mean_transfer {k m n : ℕ} :
    Measurable (datasetNorm (k := k) (m := m) (n := n)) := by
  unfold datasetNorm datasetNormSq observationNormSq
  fun_prop

private theorem datasetNorm_eLpNorm_two {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ) :
    eLpNorm (datasetNorm (k := k) (m := m) (n := n)) 2
      (Measure.pi fun _ : Fin n => μ) =
      ENNReal.ofReal (Real.sqrt ((n : ℝ) * ∫ z, observationNormSq z ∂μ)) := by
  let ν := Measure.pi fun _ : Fin n => μ
  have hmeas : AEStronglyMeasurable (datasetNorm (k := k) (m := m) (n := n)) ν :=
    (datasetNorm_measurable_for_mean_transfer (k := k) (m := m) (n := n)).aestronglyMeasurable
  have hsq : Integrable (fun D : Dataset (Observation k m) n =>
      datasetNorm D ^ 2) ν := by
    convert (integrable_datasetNormSq (k := k) (m := m) (n := n) μ hM₂) using 1
    funext D
    exact datasetNorm_sq D
  have hmem : MemLp (datasetNorm (k := k) (m := m) (n := n)) 2 ν :=
    (memLp_two_iff_integrable_sq hmeas).2 hsq
  have hformula' := hmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hformula : eLpNorm (datasetNorm (k := k) (m := m) (n := n)) 2 ν =
      ENNReal.ofReal ((∫ D, ‖datasetNorm D‖ ^ (2 : ℝ) ∂ν) ^ ((1 / 2 : ℝ))) := by
    simpa using hformula'
  have hmoment := integral_datasetNormSq (k := k) (m := m) (n := n) μ hM₂
  rw [hformula]
  congr 1
  have hnormsq :
      (∫ D : Dataset (Observation k m) n, ‖datasetNorm D‖ ^ (2 : ℝ) ∂ν) =
        (n : ℝ) * ∫ z, observationNormSq z ∂μ := by
    calc
      _ = ∫ D : Dataset (Observation k m) n, datasetNorm D ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with D
        rw [Real.norm_eq_abs]
        change |Real.sqrt (datasetNormSq D)| ^ (2 : ℝ) = _
        rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two,
          Real.sq_sqrt (datasetNormSq_nonneg D), datasetNorm_sq]
      _ = ∫ D : Dataset (Observation k m) n, datasetNormSq D ∂ν := by
        apply integral_congr_ae
        filter_upwards with D
        exact datasetNorm_sq D
      _ = (n : ℝ) * ∫ z, observationNormSq z ∂μ := hmoment
  rw [hnormsq]
  have hnonneg : 0 ≤ (n : ℝ) * ∫ z, observationNormSq z ∂μ := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z)
  rw [Real.sqrt_eq_rpow]

/-- The reviewed good-set extension has the exact L² bound from the source
second-moment calculation on the full product law. -/
theorem goodSetLipschitzExtension_eLpNorm_le {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    eLpNorm (goodSetLipschitzExtension D₀ hD₀ hLK hLip) 2 ν ≤
      ENNReal.ofReal (|H D₀| + LK *
        (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀)) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let E := goodSetLipschitzExtension D₀ hD₀ hLK hLip
  let a : ℝ := |H D₀| + LK * datasetNorm D₀
  let s : ℝ := Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ)
  have hsnonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hanonneg : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg (abs_nonneg _) (mul_nonneg hLK (Real.sqrt_nonneg _))
  have hLKs : 0 ≤ LK * s := mul_nonneg hLK hsnonneg
  have hanchor := goodSetLipschitzExtension_anchor_bound D₀ hD₀ hLK hLip
  have hdom : ∀ᵐ D ∂ν, ‖E D‖ ≤ a + LK * datasetNorm D := by
    filter_upwards with D
    have h := hanchor D
    dsimp [E, a]
    nlinarith [h]
  have hmono := eLpNorm_mono_ae_real (p := (2 : ENNReal)) hdom
  have htri := eLpNorm_add_le (p := (2 : ENNReal))
    (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Dataset (Observation (k + 1) (m + 1)) (n + 2) => a) ν)
    ((datasetNorm_measurable_for_mean_transfer (k := k + 1) (m := m + 1) (n := n + 2)).aestronglyMeasurable.const_smul LK)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hconst : eLpNorm (fun _ : Dataset (Observation (k + 1) (m + 1)) (n + 2) => a) 2 ν =
      ENNReal.ofReal a := by
    rw [eLpNorm_const (c := a) (p := (2 : ENNReal)) (by norm_num) (by
      intro hν
      have hu := congrArg (fun μ : Measure _ => μ Set.univ) hν
      simp [ν] at hu)]
    simp [ν, Real.enorm_eq_ofReal hanonneg]
  have hX := datasetNorm_eLpNorm_two (k := k + 1) (m := m + 1) (n := n + 2) μ hM₂
  have hscale : eLpNorm (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
      LK * datasetNorm D) 2 ν ≤ ENNReal.ofReal (LK * s) := by
    calc
      _ ≤ ‖LK‖ₑ * eLpNorm (datasetNorm (k := k + 1) (m := m + 1) (n := n + 2)) 2 ν := by
        change eLpNorm (LK • datasetNorm (k := k + 1) (m := m + 1) (n := n + 2))
          2 ν ≤ _
        exact eLpNorm_const_smul_le (p := (2 : ENNReal)) (c := LK)
      _ = ENNReal.ofReal LK * ENNReal.ofReal s := by
        rw [Real.enorm_eq_ofReal hLK, hX]
        congr 1
        simp [s]
      _ = ENNReal.ofReal (LK * s) := by rw [ENNReal.ofReal_mul hLK]
  have hsum := calc
      eLpNorm (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
          a + LK * datasetNorm D) 2 ν
          ≤ ENNReal.ofReal a + ENNReal.ofReal (LK * s) := by
            have hfun : (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
                a + LK * datasetNorm D) = (fun _ => a) + LK • datasetNorm := by
              funext D
              simp [smul_eq_mul]
            rw [hfun]
            exact htri.trans (add_le_add hconst.le hscale)
      _ = ENNReal.ofReal (a + LK * s) := by
            rw [← ENNReal.ofReal_add hanonneg hLKs]
  calc
    eLpNorm E 2 ν ≤ eLpNorm (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        a + LK * datasetNorm D) 2 ν := hmono
    _ ≤ ENNReal.ofReal (a + LK * s) := hsum
    _ = ENNReal.ofReal (|H D₀| + LK * (s + datasetNorm D₀)) := by
      congr 1
      dsimp [a]
      ring

/-- The exact extension bound also supplies the `MemLp` and integrability
obligations needed for its real-valued integral. -/
theorem goodSetLipschitzExtension_memLp {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    MemLp (goodSetLipschitzExtension D₀ hD₀ hLK hLip) 2 ν := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let E := goodSetLipschitzExtension D₀ hD₀ hLK hLip
  have hmeas : Measurable E := by
    exact goodSetLipschitzExtension_measurable D₀ hD₀ hLK hLip
  have hbound := goodSetLipschitzExtension_eLpNorm_le μ hM₂ D₀ hD₀ hLK hLip
  have hA : 0 ≤ |H D₀| + LK *
      (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀) := by
    exact add_nonneg (abs_nonneg _) <| mul_nonneg hLK <| add_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt hbound
  exact ENNReal.ofReal_lt_top

/-- Integrability of the reviewed extension under the full product law. -/
theorem goodSetLipschitzExtension_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    Integrable (goodSetLipschitzExtension D₀ hD₀ hLK hLip) ν := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  exact (goodSetLipschitzExtension_memLp μ hM₂ D₀ hD₀ hLK hLip).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)

private theorem memLp_two_of_finite_eLpNorm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) (B : ℝ) (hf : Measurable f)
    (hbound : eLpNorm f 2 ν ≤ ENNReal.ofReal B) : MemLp f 2 ν := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  exact hbound.trans_lt ENNReal.ofReal_lt_top

/-- Restricted Cauchy–Schwarz: if two functions agree on a measurable set, the
difference of their means is controlled by the bad-set probability and their
two `L²` bounds. Integrability is obtained from the finite `eLpNorm` bounds. -/
theorem restrictedL2_mean_transfer {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (E H : α → ℝ) (K : Set α) (hK : MeasurableSet K)
    (hEmeas : Measurable E) (hHmeas : Measurable H)
    (hagree : ∀ x ∈ K, E x = H x)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hEnorm : eLpNorm E 2 ν ≤ ENNReal.ofReal A)
    (hHnorm : eLpNorm H 2 ν ≤ ENNReal.ofReal B) :
    |∫ x, E x ∂ν - ∫ x, H x ∂ν| ≤
      Real.sqrt (ν.real Kᶜ) * (A + B) := by
  classical
  let bad : Set α := Kᶜ
  let diff : α → ℝ := fun x => E x - H x
  have hEmem := memLp_two_of_finite_eLpNorm ν E A hEmeas hEnorm
  have hHmem := memLp_two_of_finite_eLpNorm ν H B hHmeas hHnorm
  have hEint := hEmem.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hHint := hHmem.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hDiffMem : MemLp diff 2 ν := by
    exact hEmem.sub hHmem
  have hDiffBound : eLpNorm diff 2 ν ≤ ENNReal.ofReal (A + B) := by
    calc
      eLpNorm diff 2 ν ≤ eLpNorm E 2 ν + eLpNorm H 2 ν := by
        exact eLpNorm_sub_le hEmeas.aestronglyMeasurable hHmeas.aestronglyMeasurable
          (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal B := add_le_add hEnorm hHnorm
      _ = ENNReal.ofReal (A + B) := by rw [← ENNReal.ofReal_add hA hB]
  have hDiffSqNonneg : 0 ≤ ∫ x, diff x ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (diff x))
  have hDiffFormula : eLpNorm diff 2 ν =
      ENNReal.ofReal (Real.sqrt (∫ x, diff x ^ 2 ∂ν)) := by
    have hformula := hDiffMem.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    have hpow : (∫ x, ‖diff x‖ ^ (2 : ℝ) ∂ν) = ∫ x, diff x ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [show (2 : ENNReal).toReal = 2 by norm_num] at hformula
    rw [hpow] at hformula
    rw [hformula, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hsumNonneg : 0 ≤ A + B := add_nonneg hA hB
  have hrootBound : Real.sqrt (∫ x, diff x ^ 2 ∂ν) ≤ A + B := by
    apply (ENNReal.ofReal_le_ofReal_iff hsumNonneg).mp
    rw [← hDiffFormula]
    exact hDiffBound
  have hbadMeas : MeasurableSet bad := hK.compl
  have hbadNonneg : 0 ≤ ν.real bad := measureReal_nonneg
  have hIndicatorMem : MemLp (bad.indicator (fun _ : α => (1 : ℝ)))
      (ENNReal.ofReal 2) ν := by
    simpa using (memLp_const (1 : ℝ)).indicator hbadMeas
  have hDiffAbsMem : MemLp (fun x => |diff x|) (ENNReal.ofReal 2) ν := by
    convert (show MemLp (fun x => |diff x|) 2 ν from by
      simpa only [Real.norm_eq_abs] using hDiffMem.norm) using 1
    norm_num
  have hIndicatorNonneg : 0 ≤ᵐ[ν] bad.indicator (fun _ : α => (1 : ℝ)) := by
    filter_upwards with x
    by_cases hx : x ∈ bad
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hDiffAbsNonneg : 0 ≤ᵐ[ν] fun x => |diff x| :=
    ae_of_all _ fun x => abs_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) (p := 2) (q := 2) Real.HolderConjugate.two_two
    hIndicatorNonneg hDiffAbsNonneg hIndicatorMem hDiffAbsMem
  have hIndicatorSq :
      (∫ x, (bad.indicator (fun _ : α => (1 : ℝ)) x) ^ (2 : ℝ) ∂ν) = ν.real bad := by
    calc
      _ = ∫ x, (bad.indicator (fun _ : α => (1 : ℝ)) x) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        exact Real.rpow_two _
      _ = ∫ x, bad.indicator (fun _ : α => (1 : ℝ)) x ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ bad
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      _ = ν.real bad := integral_indicator_one hbadMeas
  have hDiffAbsSq : (∫ x, |diff x| ^ (2 : ℝ) ∂ν) = ∫ x, diff x ^ 2 ∂ν := by
    calc
      _ = ∫ x, |diff x| ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        exact Real.rpow_two _
      _ = ∫ x, diff x ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        exact sq_abs _
  have hIntegralDiff : ∫ x, diff x ∂ν = ∫ x, bad.indicator diff x ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ bad
    · simp [Set.indicator_of_mem hx, diff]
    · have hxK : x ∈ K := by simpa [bad] using hx
      simp [Set.indicator_of_notMem hx, diff, hagree x hxK]
  have hIntegralNorm :
      (∫ x, ‖bad.indicator diff x‖ ∂ν) =
        ∫ x, bad.indicator (fun _ : α => (1 : ℝ)) x * |diff x| ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ bad
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hMeanSub : ∫ x, E x ∂ν - ∫ x, H x ∂ν = ∫ x, diff x ∂ν := by
    rw [integral_sub hEint hHint]
  calc
    |∫ x, E x ∂ν - ∫ x, H x ∂ν| = ‖∫ x, diff x ∂ν‖ := by
      rw [hMeanSub, Real.norm_eq_abs]
    _ = ‖∫ x, bad.indicator diff x ∂ν‖ := by rw [hIntegralDiff]
    _ ≤ ∫ x, ‖bad.indicator diff x‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ x, bad.indicator (fun _ : α => (1 : ℝ)) x * |diff x| ∂ν := hIntegralNorm
    _ ≤ (∫ x, (bad.indicator (fun _ : α => (1 : ℝ)) x) ^ 2 ∂ν) ^ (1 / 2) *
        (∫ x, |diff x| ^ 2 ∂ν) ^ (1 / 2) := hHolder
    _ = Real.sqrt (ν.real bad) * Real.sqrt (∫ x, diff x ^ 2 ∂ν) := by
      rw [hIndicatorSq, hDiffAbsSq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (ν.real bad) * (A + B) := by
      exact mul_le_mul_of_nonneg_left hrootBound (Real.sqrt_nonneg _)

/-- The reviewed McShane extension transfers the mean under the actual full
dataset product law with the source's exact constants. -/
theorem goodSetLipschitzExtension_mean_transfer {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    (hK : MeasurableSet K)
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ}
    (hHmeas : Measurable H) (B LK : ℝ)
    (hB : 0 ≤ B) (hLK : 0 ≤ LK)
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2)) (hD₀ : D₀ ∈ K)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E))
    (hHnorm : eLpNorm H 2
      (Measure.pi fun _ : Fin (n + 2) => μ) ≤ ENNReal.ofReal B) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    |∫ D, goodSetLipschitzExtension D₀ hD₀ hLK hLip D ∂ν - ∫ D, H D ∂ν| ≤
      Real.sqrt (ν.real Kᶜ) *
        (B + |H D₀| + LK *
          (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀)) := by
  dsimp only
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let E := goodSetLipschitzExtension D₀ hD₀ hLK hLip
  let A := |H D₀| + LK *
    (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀)
  have hEmorm := goodSetLipschitzExtension_eLpNorm_le μ hM₂ D₀ hD₀ hLK hLip
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (abs_nonneg _) <| mul_nonneg hLK <| add_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hextMeas : Measurable E := goodSetLipschitzExtension_measurable D₀ hD₀ hLK hLip
  have hagree : ∀ D ∈ K, E D = H D :=
    goodSetLipschitzExtension_eqOn D₀ hD₀ hLK hLip
  have htransfer := restrictedL2_mean_transfer ν E H K hK hextMeas hHmeas hagree
    A B hA hB hEmorm hHnorm
  have htransfer' : |∫ D, E D ∂ν - ∫ D, H D ∂ν| ≤
      Real.sqrt (ν.real Kᶜ) * (B + A) := by
    calc
      _ ≤ Real.sqrt (ν.real Kᶜ) * (A + B) := htransfer
      _ = Real.sqrt (ν.real Kᶜ) * (B + A) := by rw [add_comm A B]
  simpa [ν, E, A, add_assoc] using htransfer'

/-- Combining mean transfer with a source bound on the original mean gives
the `δ₃ + η` extension-mean estimate. -/
theorem goodSetLipschitzExtension_mean_bound {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    (hK : MeasurableSet K)
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ}
    (hHmeas : Measurable H) (B δ₃ LK : ℝ)
    (hB : 0 ≤ B) (_hδ₃ : 0 ≤ δ₃) (hLK : 0 ≤ LK)
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2)) (hD₀ : D₀ ∈ K)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E))
    (hHnorm : eLpNorm H 2
      (Measure.pi fun _ : Fin (n + 2) => μ) ≤ ENNReal.ofReal B)
    (hHmean : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ δ₃) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    |∫ D, goodSetLipschitzExtension D₀ hD₀ hLK hLip D ∂ν| ≤
      δ₃ + Real.sqrt (ν.real Kᶜ) *
        (B + |H D₀| + LK *
          (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀)) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let E := goodSetLipschitzExtension D₀ hD₀ hLK hLip
  have htransfer := goodSetLipschitzExtension_mean_transfer μ hM₂ hK hHmeas B LK
    hB hLK D₀ hD₀ hLip hHnorm
  have hEint := goodSetLipschitzExtension_integrable μ hM₂ D₀ hD₀ hLK hLip
  have hHint := (memLp_two_of_finite_eLpNorm ν H B hHmeas hHnorm).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  let η : ℝ := Real.sqrt (ν.real Kᶜ) *
    (B + |H D₀| + LK *
      (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀))
  have hη : |∫ D, E D ∂ν - ∫ D, H D ∂ν| ≤ η := by
    simpa [η, E] using htransfer
  change |∫ D, E D ∂ν| ≤ δ₃ + η
  calc
    |∫ D, E D ∂ν| = |(∫ D, E D ∂ν - ∫ D, H D ∂ν) + ∫ D, H D ∂ν| := by
      congr 1
      ring
    _ ≤ |∫ D, E D ∂ν - ∫ D, H D ∂ν| + |∫ D, H D ∂ν| := abs_add_le _ _
    _ ≤ η + δ₃ := add_le_add hη (by simpa [ν] using hHmean)
    _ = δ₃ + η := by ring

end LOOConcentration

#print axioms LOOConcentration.goodSetLipschitzExtension_eLpNorm_le
#print axioms LOOConcentration.goodSetLipschitzExtension_memLp
#print axioms LOOConcentration.goodSetLipschitzExtension_integrable
#print axioms LOOConcentration.restrictedL2_mean_transfer
#print axioms LOOConcentration.goodSetLipschitzExtension_mean_transfer
#print axioms LOOConcentration.goodSetLipschitzExtension_mean_bound
