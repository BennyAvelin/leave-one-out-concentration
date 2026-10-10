import LOOConcentration.Concentration.ExponentialTestEnergy
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.Concentration.EntropyVariational
import LOOConcentration.Concentration.TiltedNormMoment
import LOOConcentration.FunctionalInequalities.ProductLSI
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Exact weighted energy for exponential tilts

The pointwise chain estimate below retains the exact factor `exp (λ F)`.
The product log-Sobolev inequality is an explicit predecessor: tensorization
of the frozen one-observation `HasLogSobolev` API is not proved here.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem continuous_datasetToEuclidean_tiltedEnergy {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation k m) N →
      EuclideanSpace ℝ (DatasetCoordinate k m N)) := by
  change Continuous (fun D : Dataset (Observation k m) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

private theorem continuousAt_datasetNorm_sub_tiltedEnergy {k m N : ℕ}
    (D : Dataset (Observation k m) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation k m) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean_tiltedEnergy.comp
      (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    exact datasetNorm_eq_euclidean (E - D)
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

private theorem locallyLipschitzDataFunction_continuous_tiltedEnergy
    {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n) : Continuous F.1 := by
  rw [continuous_iff_continuousAt]
  intro D
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨U, hU, K, hK, hLip⟩ := F.2 D
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hzero : datasetNorm (D - D) = 0 := by
    simp [datasetNorm, datasetNormSq, observationNormSq]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
    (continuousAt_datasetNorm_sub_tiltedEnergy D) (ε / (K + 1)) (by positivity)
  let δ := min ρ η
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hdist
  have hEU : E ∈ U := hρU (by
    dsimp [δ] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _))
  have hnorm : datasetNorm (E - D) < ε / (K + 1) := by
    have hdist' := hηbound (by
      dsimp [δ] at hdist
      exact lt_of_lt_of_le hdist (min_le_right _ _))
    have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hdist'
    exact hdist'
  have hbound := hLip E hEU D (mem_of_mem_nhds hU)
  rw [Real.dist_eq]
  change |F.1 E - F.1 D| < ε
  calc
    |F.1 E - F.1 D| ≤ K * datasetNorm (E - D) := hbound
    _ < ε := by
      have hnormNonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      have hKmul : K * datasetNorm (E - D) ≤
          (K + 1) * datasetNorm (E - D) := by nlinarith [hnormNonneg]
      have hkp : 0 < K + 1 := by linarith
      have hlt : (K + 1) * datasetNorm (E - D) <
          (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hnorm hkp
      have heq : (K + 1) * (ε / (K + 1)) = ε := by field_simp
      rw [heq] at hlt
      exact hKmul.trans_lt hlt

private theorem measurable_locallyLipschitzDataFunction_tiltedEnergy
    {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n) : Measurable F.1 :=
  (locallyLipschitzDataFunction_continuous_tiltedEnergy F).measurable

/-- Exact pointwise weighted chain rule for the squared slope of the
exponential test. In particular, the density is evaluated at `D`; no global
range bound is used in this coefficient. -/
theorem datasetLocalSlope_expTiltedTestFunction_exact_sq_le {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (D : DataCarrier k m n) :
    datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2 ≤
      (lam ^ 2 / 4) * Real.exp (lam * F.1 D) *
        (a + b * datasetNorm D) ^ 2 := by
  let u := expTiltedTestFunction F lam B hB hBound
  have hchain := datasetLocalSlope_expTiltedTestFunction_chain_le
    F lam B hB hBound D
  have hsource := hSlope D
  have hnorm : 0 ≤ datasetNorm D := Real.sqrt_nonneg _
  have hlinear : 0 ≤ a + b * datasetNorm D := add_nonneg ha (mul_nonneg hb hnorm)
  have huNonneg : 0 ≤ datasetLocalSlope u D := datasetLocalSlope_nonneg u D
  have hfactor : 0 ≤ |lam / 2| * Real.exp ((lam / 2) * F.1 D) := by positivity
  have hupper : datasetLocalSlope u D ≤
      (|lam / 2| * Real.exp ((lam / 2) * F.1 D)) *
        (a + b * datasetNorm D) :=
    hchain.trans (mul_le_mul_of_nonneg_left hsource hfactor)
  have hsq := (sq_le_sq₀ huNonneg
    (mul_nonneg hfactor hlinear)).2 hupper
  have hhalf : (|lam / 2|) ^ 2 = lam ^ 2 / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_abs lam]
  have hexp : Real.exp ((lam / 2) * F.1 D) ^ 2 =
      Real.exp (lam * F.1 D) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    datasetLocalSlope u D ^ 2 ≤
        ((|lam / 2| * Real.exp ((lam / 2) * F.1 D)) *
          (a + b * datasetNorm D)) ^ 2 := hsq
    _ = (lam ^ 2 / 4) * Real.exp (lam * F.1 D) *
          (a + b * datasetNorm D) ^ 2 := by
      rw [mul_pow, mul_pow, hhalf, hexp]

private theorem integrable_exp_mul_bounded_tiltedEnergy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (_hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => Real.exp (t * F ω)) μ := by
  have hmeas : Measurable (fun ω => Real.exp (t * F ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hFmeas)
  have hbound : ∀ ω, ‖Real.exp (t * F ω)‖ ≤ Real.exp (|t| * B) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * F ω ≤ |t * F ω| := le_abs_self _
      _ = |t| * |F ω| := abs_mul _ _
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg _)
  exact Integrable.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)

private theorem integrable_tiltWeighted_growth_sq {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (_hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    Integrable
      (fun D : DataCarrier k m n => Real.exp (lam * F.1 D) *
        (a + b * datasetNorm D) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let ν := Measure.pi fun _ : Fin (n + 1) => μ
  let w : DataCarrier k m n → ℝ := fun D => Real.exp (lam * F.1 D)
  have hcontF : Continuous F.1 := locallyLipschitzDataFunction_continuous_tiltedEnergy F
  have hwmeas : Measurable w := by
    dsimp [w]
    exact (Real.continuous_exp.comp (continuous_const.mul hcontF)).measurable
  have hwbound : ∀ᵐ D ∂ν, ‖w D‖ ≤ Real.exp (|lam| * B) := by
    filter_upwards with D
    have harg : lam * F.1 D ≤ |lam| * B := by
      calc
        lam * F.1 D ≤ |lam * F.1 D| := le_abs_self _
        _ = |lam| * |F.1 D| := abs_mul _ _
        _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hBound D) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr harg
  have hwInt : Integrable w ν :=
    Integrable.of_bound hwmeas.aestronglyMeasurable _ hwbound
  have hnormSq : Integrable
      (datasetNormSq (k := k + 1) (m := m + 1) (n := n + 1)) ν :=
    integrable_datasetNormSq μ hM2
  have hweightedNormSq : Integrable (fun D : DataCarrier k m n =>
      w D * datasetNormSq D) ν := hnormSq.bdd_mul hwmeas.aestronglyMeasurable hwbound
  have hExpanded : Integrable (fun D : DataCarrier k m n =>
      w D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) ν := by
    have hfirst : Integrable (fun D : DataCarrier k m n => w D * (2 * a ^ 2)) ν :=
      hwInt.mul_const (2 * a ^ 2)
    have hsecond : Integrable (fun D : DataCarrier k m n =>
        w D * (2 * b ^ 2 * datasetNormSq D)) ν := by
      convert hweightedNormSq.const_mul (2 * b ^ 2) using 1
      ext D
      ring
    have hsplit : (fun D : DataCarrier k m n =>
        w D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) =
        (fun D => w D * (2 * a ^ 2)) +
          (fun D => w D * (2 * b ^ 2 * datasetNormSq D)) := by
      funext D
      simp only [Pi.add_apply]
      rw [mul_add]
    rw [hsplit]
    exact hfirst.add hsecond
  have htargetMeas : Measurable (fun D : DataCarrier k m n =>
      w D * (a + b * datasetNorm D) ^ 2) := by
    have hnorm : Continuous (datasetNorm (k := k + 1) (m := m + 1) (n := n + 1)) := by
      rw [show (datasetNorm (k := k + 1) (m := m + 1) (n := n + 1)) =
          fun D => ‖datasetToEuclidean D‖ by
        funext D
        rw [datasetNorm_eq_euclidean]
        ]
      exact continuous_norm.comp continuous_datasetToEuclidean_tiltedEnergy
    have hq : Continuous (fun D : DataCarrier k m n =>
        (a + b * datasetNorm D) ^ 2) := by fun_prop
    exact hwmeas.mul hq.measurable
  have hWeightedQ : Integrable (fun D : DataCarrier k m n =>
      w D * (a + b * datasetNorm D) ^ 2) ν := by
    apply Integrable.mono' hExpanded htargetMeas.aestronglyMeasurable
    filter_upwards with D
    have hNorm : 0 ≤ datasetNorm D := Real.sqrt_nonneg _
    have hQ : (a + b * datasetNorm D) ^ 2 ≤
        2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D := by
      calc
        (a + b * datasetNorm D) ^ 2 ≤
            2 * a ^ 2 + 2 * b ^ 2 * datasetNorm D ^ 2 := by
              nlinarith [sq_nonneg (a - b * datasetNorm D)]
        _ = 2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D := by rw [datasetNorm_sq]
    have hwD : 0 ≤ w D := Real.exp_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwD (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hQ hwD
  exact hWeightedQ

/-- Finite energy admission using the exact weighted pointwise estimate.
As in wave 4, the only unresolved input is strong measurability of the
squared local slope; boundedness and the finite second moment provide the
integrable majorant. -/
theorem integrable_expTiltedTestFunction_energy_of_aestronglyMeasurable_exact
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hMeas : AEStronglyMeasurable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  apply Integrable.mono'
    (by
      have hQ := integrable_tiltWeighted_growth_sq μ hM2 F lam B a b
        hB hBound ha hb
      simpa [mul_assoc] using hQ.const_mul (lam ^ 2 / 4))
    hMeas
  filter_upwards with D
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [mul_assoc] using (datasetLocalSlope_expTiltedTestFunction_exact_sq_le
    F lam B a b hB hBound ha hb hSlope D)

private theorem tiltEntropy_eq_looconcentrationEntropy_exp_div {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    tiltEntropy μ F t =
      looconcentrationEntropy μ (fun ω => Real.exp (t * F ω)) /
        tiltPartition μ F t := by
  let w : Ω → ℝ := fun ω => Real.exp (t * F ω)
  have hZ : 0 < tiltPartition μ F t := tiltPartition_pos hFmeas hB hF
  have hIpos : 0 < (∫ ω, Real.exp (t * F ω) ∂μ) := by
    simpa [tiltPartition] using hZ
  have hW : Integrable w μ := integrable_exp_mul_bounded_tiltedEnergy hFmeas hB hF
  have hWF : Integrable (fun ω => w ω * F ω) μ := by
    have hFbound : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ B := by
      filter_upwards with ω
      simpa [Real.norm_eq_abs] using hF ω
    convert hW.bdd_mul hFmeas.aestronglyMeasurable hFbound using 1
    ext ω
    ring
  have hWlog : ∫ ω, w ω * Real.log (w ω) ∂μ =
      t * (∫ ω, F ω * Real.exp (t * F ω) ∂μ) := by
    calc
      (∫ ω, w ω * Real.log (w ω) ∂μ) =
          ∫ ω, t * (F ω * Real.exp (t * F ω)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            simp [w, Real.log_exp]
            ring
      _ = t * (∫ ω, F ω * Real.exp (t * F ω) ∂μ) := integral_const_mul t _
  have hMean :
      (∫ ω, tiltDensity μ F t ω * F ω ∂μ) =
        (∫ ω, F ω * Real.exp (t * F ω) ∂μ) / tiltPartition μ F t := by
    calc
      (∫ ω, tiltDensity μ F t ω * F ω ∂μ) =
          ∫ ω, (F ω * Real.exp (t * F ω)) *
            (tiltPartition μ F t)⁻¹ ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            simp [tiltDensity, div_eq_mul_inv]
            ring
      _ = (∫ ω, F ω * Real.exp (t * F ω) ∂μ) *
            (tiltPartition μ F t)⁻¹ :=
            integral_mul_const _ _
      _ = (∫ ω, F ω * Real.exp (t * F ω) ∂μ) /
            tiltPartition μ F t := by rw [div_eq_mul_inv]
  rw [tiltEntropy_eq_tiltMean_sub_logPartition hFmeas hB hF, hMean]
  unfold looconcentrationEntropy
  dsimp [w]
  rw [hWlog, tiltPartition]
  field_simp [ne_of_gt hIpos]

/-- Apply an explicit exact-constant product LSI predecessor to the bounded
exponential test. The first bound uses the exact tilted expectation of
`(a+b‖D‖)^2`; the second is its standard quadratic expansion. Both preserve
the source coefficient. The theorem remains conditional on product LSI and
the squared-slope measurability bridge. -/
theorem tiltEntropy_le_of_datasetProductLogSobolev
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) (lam B a b C : ℝ)
    (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hSlopeMeas : AEStronglyMeasurable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ))
    (hC : 0 < C)
    (hProductLSI :
      Integrable (fun D : DataCarrier k m n =>
          (expTiltedTestFunction F lam B hB hBound).1 D ^ 2)
          (Measure.pi fun _ : Fin (n + 1) => μ) →
        Integrable (fun D : DataCarrier k m n =>
          (expTiltedTestFunction F lam B hB hBound).1 D ^ 2 *
            Real.log ((expTiltedTestFunction F lam B hB hBound).1 D ^ 2))
          (Measure.pi fun _ : Fin (n + 1) => μ) →
        Integrable
          (fun D : DataCarrier k m n =>
            datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2)
          (Measure.pi fun _ : Fin (n + 1) => μ) →
        looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
            (fun D : DataCarrier k m n =>
              (expTiltedTestFunction F lam B hB hBound).1 D ^ 2) ≤
          2 * C * (∫ D : DataCarrier k m n,
            datasetLocalSlope (expTiltedTestFunction F lam B hB hBound) D ^ 2
              ∂Measure.pi fun _ : Fin (n + 1) => μ)) :
    tiltEntropy (Measure.pi fun _ : Fin (n + 1) => μ) F.1 lam ≤
        (C * lam ^ 2 / 2) *
          (∫ D, tiltDensity (Measure.pi fun _ : Fin (n + 1) => μ) F.1 lam D *
            (a + b * datasetNorm D) ^ 2 ∂Measure.pi fun _ : Fin (n + 1) => μ) ∧
      tiltEntropy (Measure.pi fun _ : Fin (n + 1) => μ) F.1 lam ≤
        C * lam ^ 2 *
          (a ^ 2 + b ^ 2 *
            (∫ D, tiltDensity (Measure.pi fun _ : Fin (n + 1) => μ)
              F.1 lam D * datasetNormSq D ∂Measure.pi fun _ : Fin (n + 1) => μ)) := by
  let ν := Measure.pi fun _ : Fin (n + 1) => μ
  let u := expTiltedTestFunction F lam B hB hBound
  let w : DataCarrier k m n → ℝ := fun D => Real.exp (lam * F.1 D)
  let Q : DataCarrier k m n → ℝ := fun D => (a + b * datasetNorm D) ^ 2
  have hFmeas : Measurable F.1 := measurable_locallyLipschitzDataFunction_tiltedEnergy F
  have hZ : 0 < tiltPartition ν F.1 lam := tiltPartition_pos hFmeas hB hBound
  have huSq : (fun D : DataCarrier k m n => u.1 D ^ 2) = w := by
    funext D
    change Real.exp ((lam / 2) * F.1 D) ^ 2 = Real.exp (lam * F.1 D)
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hExpW : Integrable w ν :=
    integrable_exp_mul_bounded_tiltedEnergy
      (μ := ν) (F := F.1) (t := lam) hFmeas hB hBound
  have hU2 : Integrable (fun D : DataCarrier k m n => u.1 D ^ 2) ν := by
    rw [huSq]
    exact hExpW
  have hFbound : ∀ᵐ D ∂ν, ‖F.1 D‖ ≤ B := by
    filter_upwards with D
    simpa [Real.norm_eq_abs] using hBound D
  have hWF : Integrable (fun D : DataCarrier k m n => w D * F.1 D) ν := by
    have h := hExpW.bdd_mul hFmeas.aestronglyMeasurable hFbound
    convert h using 1
    ext D
    ring
  have hULogEq :
      (fun D : DataCarrier k m n =>
        u.1 D ^ 2 * Real.log (u.1 D ^ 2)) =
      (fun D => lam * (w D * F.1 D)) := by
    funext D
    rw [show u.1 D ^ 2 = w D by exact congrFun huSq D]
    simp [w, Real.log_exp]
    ring
  have hULog : Integrable (fun D : DataCarrier k m n =>
      u.1 D ^ 2 * Real.log (u.1 D ^ 2)) ν := by
    rw [hULogEq]
    exact hWF.const_mul lam
  have hEnergy := integrable_expTiltedTestFunction_energy_of_aestronglyMeasurable_exact
    μ hM2 F lam B a b hB hBound ha hb hSlope hSlopeMeas
  have hWQ : Integrable (fun D : DataCarrier k m n => w D * Q D) ν :=
    integrable_tiltWeighted_growth_sq μ hM2 F lam B a b hB hBound ha hb
  have hPoint : ∀ D : DataCarrier k m n,
      datasetLocalSlope u D ^ 2 ≤ (lam ^ 2 / 4) * (w D * Q D) := by
    intro D
    simpa [u, w, Q, mul_assoc] using datasetLocalSlope_expTiltedTestFunction_exact_sq_le
      F lam B a b hB hBound ha hb hSlope D
  have hEnergyMajorant : Integrable
      (fun D : DataCarrier k m n => (lam ^ 2 / 4) * (w D * Q D)) ν :=
    hWQ.const_mul (lam ^ 2 / 4)
  have hIntSlope :
      (∫ D : DataCarrier k m n, datasetLocalSlope u D ^ 2 ∂ν) ≤
        (lam ^ 2 / 4) * (∫ D : DataCarrier k m n, w D * Q D ∂ν) := by
    calc
      (∫ D : DataCarrier k m n, datasetLocalSlope u D ^ 2 ∂ν) ≤
          ∫ D : DataCarrier k m n, (lam ^ 2 / 4) * (w D * Q D) ∂ν :=
            integral_mono hEnergy hEnergyMajorant (fun D => hPoint D)
      _ = (lam ^ 2 / 4) * (∫ D : DataCarrier k m n, w D * Q D ∂ν) :=
            integral_const_mul _ _
  have hLSIentropy := hProductLSI hU2 hULog hEnergy
  have hEntropyIdentity := tiltEntropy_eq_looconcentrationEntropy_exp_div
    (μ := ν) (t := lam) hFmeas hB hBound
  have hLOOConcentration : looconcentrationEntropy ν (fun D : DataCarrier k m n => u.1 D ^ 2) =
      tiltPartition ν F.1 lam * tiltEntropy ν F.1 lam := by
    rw [huSq]
    calc
      looconcentrationEntropy ν w = tiltEntropy ν F.1 lam * tiltPartition ν F.1 lam :=
        (div_eq_iff (ne_of_gt hZ)).mp hEntropyIdentity.symm
      _ = tiltPartition ν F.1 lam * tiltEntropy ν F.1 lam := mul_comm _ _
  have hUnnorm :
      tiltPartition ν F.1 lam * tiltEntropy ν F.1 lam ≤
        (C * lam ^ 2 / 2) *
          (∫ D : DataCarrier k m n, w D * Q D ∂ν) := by
    have hLSI' := hLSIentropy
    rw [hLOOConcentration] at hLSI'
    have hLSIenergy :
        2 * C * (∫ D : DataCarrier k m n, datasetLocalSlope u D ^ 2 ∂ν) ≤
          2 * C * ((lam ^ 2 / 4) * (∫ D : DataCarrier k m n, w D * Q D ∂ν)) :=
      mul_le_mul_of_nonneg_left hIntSlope (by positivity)
    calc
      tiltPartition ν F.1 lam * tiltEntropy ν F.1 lam ≤
          2 * C * (∫ D : DataCarrier k m n, datasetLocalSlope u D ^ 2 ∂ν) := hLSI'
      _ ≤ 2 * C * ((lam ^ 2 / 4) *
          (∫ D : DataCarrier k m n, w D * Q D ∂ν)) := hLSIenergy
      _ = (C * lam ^ 2 / 2) *
          (∫ D : DataCarrier k m n, w D * Q D ∂ν) := by ring
  have hTiltWeighted :
      (∫ D : DataCarrier k m n,
        tiltDensity ν F.1 lam D * Q D ∂ν) =
        (∫ D : DataCarrier k m n, w D * Q D ∂ν) /
          tiltPartition ν F.1 lam := by
    calc
      (∫ D : DataCarrier k m n,
          tiltDensity ν F.1 lam D * Q D ∂ν) =
          ∫ D : DataCarrier k m n,
            (w D * Q D) * (tiltPartition ν F.1 lam)⁻¹ ∂ν := by
              apply integral_congr_ae
              filter_upwards with D
              simp [tiltDensity, w, div_eq_mul_inv]
              ring
      _ = (∫ D : DataCarrier k m n, w D * Q D ∂ν) *
            (tiltPartition ν F.1 lam)⁻¹ := integral_mul_const _ _
      _ = (∫ D : DataCarrier k m n, w D * Q D ∂ν) /
            tiltPartition ν F.1 lam := by rw [div_eq_mul_inv]
  have hFirst : tiltEntropy ν F.1 lam ≤
      (C * lam ^ 2 / 2) * (∫ D : DataCarrier k m n,
        tiltDensity ν F.1 lam D * Q D ∂ν) := by
    have hscale : tiltPartition ν F.1 lam *
        ((C * lam ^ 2 / 2) *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * Q D ∂ν)) =
        (C * lam ^ 2 / 2) *
          (∫ D : DataCarrier k m n, w D * Q D ∂ν) := by
      rw [hTiltWeighted]
      field_simp [ne_of_gt hZ]
    have hScaled : tiltPartition ν F.1 lam * tiltEntropy ν F.1 lam ≤
        tiltPartition ν F.1 lam *
          ((C * lam ^ 2 / 2) *
            (∫ D : DataCarrier k m n,
              tiltDensity ν F.1 lam D * Q D ∂ν)) := by
      rw [hscale]
      exact hUnnorm
    exact le_of_mul_le_mul_left hScaled hZ
  have hTiltNorm : Integrable (fun D : DataCarrier k m n =>
      tiltDensity ν F.1 lam D * datasetNormSq D) ν :=
    integrable_datasetNormSq_tiltDensity_mul μ hM2 F.1 hFmeas hB hBound
  have hDensityInt : Integrable (tiltDensity ν F.1 lam) ν := by
    have hExp := integrable_exp_mul_bounded_tiltedEnergy
      (μ := ν) (F := F.1) (t := lam) hFmeas hB hBound
    change Integrable
      (fun D : DataCarrier k m n => Real.exp (lam * F.1 D) /
        tiltPartition ν F.1 lam) ν
    simpa only [div_eq_mul_inv] using hExp.mul_const (tiltPartition ν F.1 lam)⁻¹
  have hTiltQ : Integrable (fun D : DataCarrier k m n =>
      tiltDensity ν F.1 lam D * Q D) ν := by
    convert hWQ.mul_const (tiltPartition ν F.1 lam)⁻¹ using 1
    ext D
    simp [tiltDensity, w, div_eq_mul_inv]
    ring
  have hExpandedTilt : Integrable (fun D : DataCarrier k m n =>
      tiltDensity ν F.1 lam D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) ν := by
    have hfirst : Integrable (fun D : DataCarrier k m n =>
        tiltDensity ν F.1 lam D * (2 * a ^ 2)) ν := hDensityInt.mul_const _
    have hsecond : Integrable (fun D : DataCarrier k m n =>
        tiltDensity ν F.1 lam D * (2 * b ^ 2 * datasetNormSq D)) ν := by
      convert hTiltNorm.const_mul (2 * b ^ 2) using 1
      ext D
      ring
    have hsplit : (fun D : DataCarrier k m n =>
        tiltDensity ν F.1 lam D * (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D)) =
        (fun D => tiltDensity ν F.1 lam D * (2 * a ^ 2)) +
          (fun D => tiltDensity ν F.1 lam D * (2 * b ^ 2 * datasetNormSq D)) := by
      funext D
      simp only [Pi.add_apply]
      rw [mul_add]
    rw [hsplit]
    exact hfirst.add hsecond
  have hQbound : ∀ D : DataCarrier k m n,
      tiltDensity ν F.1 lam D * Q D ≤
        tiltDensity ν F.1 lam D *
          (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D) := by
    intro D
    have hlin : (a + b * datasetNorm D) ^ 2 ≤
        2 * a ^ 2 + 2 * b ^ 2 * datasetNorm D ^ 2 := by
      nlinarith [sq_nonneg (a - b * datasetNorm D)]
    have hdensity : 0 ≤ tiltDensity ν F.1 lam D := by
      exact div_nonneg (Real.exp_nonneg _) hZ.le
    have hnormSq : datasetNorm D ^ 2 = datasetNormSq D := datasetNorm_sq D
    have hlin' : (a + b * datasetNorm D) ^ 2 ≤
        2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D := by
      simpa [datasetNorm_sq] using hlin
    change tiltDensity ν F.1 lam D * (a + b * datasetNorm D) ^ 2 ≤ _
    exact mul_le_mul_of_nonneg_left hlin' hdensity
  have hIntQ :
      (∫ D : DataCarrier k m n, tiltDensity ν F.1 lam D * Q D ∂ν) ≤
        2 * a ^ 2 + 2 * b ^ 2 *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * datasetNormSq D ∂ν) := by
    have h := integral_mono hTiltQ hExpandedTilt hQbound
    have hOne := tiltDensity_integral_eq_one
      (μ := ν) (F := F.1) (t := lam) hFmeas hB hBound
    calc
      (∫ D : DataCarrier k m n, tiltDensity ν F.1 lam D * Q D ∂ν) ≤
          ∫ D : DataCarrier k m n, tiltDensity ν F.1 lam D *
            (2 * a ^ 2 + 2 * b ^ 2 * datasetNormSq D) ∂ν := h
      _ = 2 * a ^ 2 + 2 * b ^ 2 *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * datasetNormSq D ∂ν) := by
        rw [show (fun D : DataCarrier k m n =>
            tiltDensity ν F.1 lam D * (2 * a ^ 2 +
              2 * b ^ 2 * datasetNormSq D)) =
            (fun D => tiltDensity ν F.1 lam D * (2 * a ^ 2)) +
              (fun D => tiltDensity ν F.1 lam D *
                (2 * b ^ 2 * datasetNormSq D)) by
          funext D
          simp only [Pi.add_apply]
          rw [mul_add]]
        rw [integral_add' (by
          exact hDensityInt.mul_const (2 * a ^ 2)) (by
          convert hTiltNorm.const_mul (2 * b ^ 2) using 1
          ext D
          ring)]
        rw [integral_mul_const, hOne]
        have hSecond :
            (∫ D : DataCarrier k m n,
              tiltDensity ν F.1 lam D * (2 * b ^ 2 * datasetNormSq D) ∂ν) =
              2 * b ^ 2 * (∫ D : DataCarrier k m n,
                tiltDensity ν F.1 lam D * datasetNormSq D ∂ν) := by
          calc
            (∫ D : DataCarrier k m n,
                tiltDensity ν F.1 lam D *
                  (2 * b ^ 2 * datasetNormSq D) ∂ν) =
                ∫ D : DataCarrier k m n,
                  (tiltDensity ν F.1 lam D * datasetNormSq D) *
                    (2 * b ^ 2) ∂ν := by
                      apply integral_congr_ae
                      filter_upwards with D
                      ring
            _ = (∫ D : DataCarrier k m n,
                  tiltDensity ν F.1 lam D * datasetNormSq D ∂ν) *
                    (2 * b ^ 2) := integral_mul_const _ _
            _ = 2 * b ^ 2 * (∫ D : DataCarrier k m n,
                  tiltDensity ν F.1 lam D * datasetNormSq D ∂ν) := by ring
        rw [hSecond]
        ring
  have hCoeff : 0 ≤ C * lam ^ 2 / 2 := by positivity
  refine ⟨hFirst, ?_⟩
  calc
    tiltEntropy ν F.1 lam ≤
        (C * lam ^ 2 / 2) *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * Q D ∂ν) := hFirst
    _ ≤ (C * lam ^ 2 / 2) *
        (2 * a ^ 2 + 2 * b ^ 2 *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * datasetNormSq D ∂ν)) :=
          mul_le_mul_of_nonneg_left hIntQ hCoeff
    _ = C * lam ^ 2 *
        (a ^ 2 + b ^ 2 *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 lam D * datasetNormSq D ∂ν)) := by ring

end LOOConcentration
