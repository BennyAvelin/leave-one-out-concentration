import LOOConcentration.Results.GoodSetMeanTransfer
import LOOConcentration.Concentration.SubGaussianSum
import Mathlib.Tactic

/-!
# Good-set tail and event transfer

The only open analytic input in the actual extension result is an all-real
sub-Gaussian MGF for the centered reviewed McShane extension. The good-set
event transfer and the zero-scale branch are proved here.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- Two-sided strict-tail Chernoff bounds for a centered sub-Gaussian
observable, with its exact zero-scale convention. -/
private theorem centeredSubGaussianMGF_strict_sign_tails
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {C s : NNReal} {X : α → ℝ}
    (hC : 0 < C)
    (hX : LOOConcentration.Concentration.CenteredSubGaussianMGF ν C s X)
    (t : ℝ) (ht : 0 < t) :
    ν.real {x | X x > t} ≤
        (if (s : ℝ) = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * (C : ℝ) * (s : ℝ) ^ 2)))) ∧
      ν.real {x | -X x > t} ≤
        (if (s : ℝ) = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * (C : ℝ) * (s : ℝ) ^ 2)))) := by
  by_cases hs : (s : ℝ) = 0
  · have hsNN : s = 0 := by exact_mod_cast hs
    have hproxy : LOOConcentration.Concentration.subGaussianProxy C s = 0 := by
      simp [LOOConcentration.Concentration.subGaussianProxy, hsNN]
    have hmgfZero : ProbabilityTheory.HasSubgaussianMGF X 0 ν := by
      simpa [hproxy] using hX.mgf
    have hzero : X =ᵐ[ν] 0 :=
      hmgfZero.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hupper : {x | X x > t} =ᵐ[ν] (∅ : Set α) := by
      filter_upwards [hzero] with x hx
      have hx' : X x = 0 := by simpa using hx
      apply propext
      change X x > t ↔ False
      constructor
      · intro h
        rw [hx'] at h
        linarith
      · intro h
        exact False.elim h
    have hlower : {x | -X x > t} =ᵐ[ν] (∅ : Set α) := by
      filter_upwards [hzero] with x hx
      have hx' : X x = 0 := by simpa using hx
      apply propext
      change -X x > t ↔ False
      constructor
      · intro h
        rw [hx'] at h
        simp only [neg_zero] at h
        linarith
      · intro h
        exact False.elim h
    constructor <;> rw [measureReal_congr (by assumption)] <;> simp [hs]
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2 (Ne.symm hs)
    have hproxypos : 0 < (LOOConcentration.Concentration.subGaussianProxy C s : ℝ) := by
      rw [LOOConcentration.Concentration.coe_subGaussianProxy]
      exact mul_pos hC (sq_pos_of_pos hspos)
    have hupper := hX.mgf.measure_ge_le (le_of_lt ht)
    have hupperMono : ν.real {x | X x > t} ≤ ν.real {x | t ≤ X x} := by
      have hsubset : {x | X x > t} ⊆ {x | t ≤ X x} := by
        intro x hx
        change X x > t at hx
        exact le_of_lt hx
      exact measureReal_mono hsubset (measure_ne_top ν _)
    have hlower := hX.mgf.neg.measure_ge_le (le_of_lt ht)
    have hlowerMono : ν.real {x | -X x > t} ≤ ν.real {x | t ≤ -X x} := by
      have hsubset : {x | -X x > t} ⊆ {x | t ≤ -X x} := by
        intro x hx
        change -X x > t at hx
        exact le_of_lt hx
      exact measureReal_mono hsubset (measure_ne_top ν _)
    have hrate : Real.exp (-(t ^ 2 / (2 * (LOOConcentration.Concentration.subGaussianProxy C s : ℝ)))) =
        Real.exp (-(t ^ 2 / (2 * (C : ℝ) * (s : ℝ) ^ 2))) := by
      congr 1
      rw [LOOConcentration.Concentration.coe_subGaussianProxy]
      ring
    constructor
    · rw [if_neg hs]
      calc
        ν.real {x | X x > t} ≤ ν.real {x | t ≤ X x} := hupperMono
        _ ≤ Real.exp (-(t ^ 2 / (2 * (LOOConcentration.Concentration.subGaussianProxy C s : ℝ)))) := by
          simpa [div_eq_mul_inv] using hupper
        _ = Real.exp (-(t ^ 2 / (2 * (C : ℝ) * (s : ℝ) ^ 2))) := hrate
    · rw [if_neg hs]
      calc
        ν.real {x | -X x > t} ≤ ν.real {x | t ≤ -X x} := hlowerMono
        _ ≤ Real.exp (-(t ^ 2 / (2 * (LOOConcentration.Concentration.subGaussianProxy C s : ℝ)))) := by
          simpa [div_eq_mul_inv] using hlower
        _ = Real.exp (-(t ^ 2 / (2 * (C : ℝ) * (s : ℝ) ^ 2))) := hrate

/-- Transfer positive, negative and absolute strict-tail events from an
extension to a function agreeing with it on `K`. The bad set enters once in
the absolute-tail estimate. -/
theorem goodSetTailEventTransfer
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (E H : α → ℝ) (K : Set α) (_hK : MeasurableSet K)
    (hEmeas : Measurable E) (hHmeas : Measurable H)
    (hagree : ∀ x ∈ K, E x = H x)
    (m d t tail : ℝ) (hmean : |m| ≤ d)
    (hupper : ν.real {x | E x - m > t} ≤ tail)
    (hlower : ν.real {x | m - E x > t} ≤ tail) :
    (MeasurableSet {x | |H x| > d + t} ∧
      MeasurableSet {x | H x > d + t} ∧
      MeasurableSet {x | -H x > d + t}) ∧
    (ν.real {x | |H x| > d + t} ≤ ν.real Kᶜ + 2 * tail ∧
      ν.real {x | H x > d + t} ≤ ν.real Kᶜ + tail ∧
      ν.real {x | -H x > d + t} ≤ ν.real Kᶜ + tail) := by
  have hmUpper : m ≤ d := (abs_le.mp hmean).2
  have hmLower : -d ≤ m := (abs_le.mp hmean).1
  have habsMeas : MeasurableSet {x | |H x| > d + t} := by
    change MeasurableSet {x | d + t < |H x|}
    exact measurableSet_lt measurable_const hHmeas.abs
  have hupperMeas : MeasurableSet {x | H x > d + t} := by
    change MeasurableSet {x | d + t < H x}
    exact measurableSet_lt measurable_const hHmeas
  have hlowerMeas : MeasurableSet {x | -H x > d + t} := by
    change MeasurableSet {x | d + t < -H x}
    exact measurableSet_lt measurable_const hHmeas.neg
  have hcenterUpperMeas : MeasurableSet {x | E x - m > t} := by
    change MeasurableSet {x | t < E x - m}
    exact measurableSet_lt measurable_const (hEmeas.sub measurable_const)
  have hcenterLowerMeas : MeasurableSet {x | m - E x > t} := by
    change MeasurableSet {x | t < m - E x}
    exact measurableSet_lt measurable_const (measurable_const.sub hEmeas)
  have hupperSub : {x | H x > d + t} ⊆ Kᶜ ∪ {x | E x - m > t} := by
    intro x hx
    by_cases hxK : x ∈ K
    · right
      change H x > d + t at hx
      have hEq := hagree x hxK
      change E x - m > t
      rw [hEq]
      linarith
    · exact Or.inl hxK
  have hlowerSub : {x | -H x > d + t} ⊆ Kᶜ ∪ {x | m - E x > t} := by
    intro x hx
    by_cases hxK : x ∈ K
    · right
      change -H x > d + t at hx
      have hEq := hagree x hxK
      change m - E x > t
      rw [hEq]
      linarith
    · exact Or.inl hxK
  have habsSub : {x | |H x| > d + t} ⊆
      Kᶜ ∪ ({x | E x - m > t} ∪ {x | m - E x > t}) := by
    intro x hx
    by_cases hpos : H x > d + t
    · rcases hupperSub hpos with hbad | htail
      · exact Or.inl hbad
      · exact Or.inr (Or.inl htail)
    · have hneg : -H x > d + t := by
        by_contra hn
        have hHle : H x ≤ d + t := le_of_not_gt hpos
        have hnegLe : -H x ≤ d + t := le_of_not_gt hn
        have habs : |H x| ≤ d + t := abs_le.mpr ⟨by linarith, hHle⟩
        exact (not_lt_of_ge habs) hx
      rcases hlowerSub hneg with hbad | htail
      · exact Or.inl hbad
      · exact Or.inr (Or.inr htail)
  have hupperProb : ν.real {x | H x > d + t} ≤ ν.real Kᶜ + tail := by
    calc
      ν.real {x | H x > d + t} ≤ ν.real (Kᶜ ∪ {x | E x - m > t}) :=
        measureReal_mono hupperSub
      _ ≤ ν.real Kᶜ + ν.real {x | E x - m > t} := measureReal_union_le _ _
      _ ≤ ν.real Kᶜ + tail := add_le_add le_rfl hupper
  have hlowerProb : ν.real {x | -H x > d + t} ≤ ν.real Kᶜ + tail := by
    calc
      ν.real {x | -H x > d + t} ≤ ν.real (Kᶜ ∪ {x | m - E x > t}) :=
        measureReal_mono hlowerSub
      _ ≤ ν.real Kᶜ + ν.real {x | m - E x > t} := measureReal_union_le _ _
      _ ≤ ν.real Kᶜ + tail := add_le_add le_rfl hlower
  have habsProb : ν.real {x | |H x| > d + t} ≤ ν.real Kᶜ + 2 * tail := by
    calc
      ν.real {x | |H x| > d + t} ≤
          ν.real (Kᶜ ∪ ({x | E x - m > t} ∪ {x | m - E x > t})) :=
        measureReal_mono habsSub
      _ ≤ ν.real Kᶜ + ν.real ({x | E x - m > t} ∪ {x | m - E x > t}) :=
        measureReal_union_le _ _
      _ ≤ ν.real Kᶜ + (ν.real {x | E x - m > t} + ν.real {x | m - E x > t}) :=
        add_le_add le_rfl (measureReal_union_le _ _)
      _ ≤ ν.real Kᶜ + (tail + tail) := by gcongr
      _ = ν.real Kᶜ + 2 * tail := by ring
  exact ⟨⟨habsMeas, hupperMeas, hlowerMeas⟩,
    ⟨habsProb, hupperProb, hlowerProb⟩⟩

/-- Exact data-dependent strict-tail bounds for the selected measurable error.
The only open predecessor is the all-real Gaussian MGF for the centered
reviewed extension at its frozen norm Lipschitz scale. -/
theorem goodSetLipschitzExtension_tail_bounds {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    (hK : MeasurableSet K)
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ}
    (hHmeas : Measurable H) (B δ₃ LK : ℝ)
    (hB : 0 ≤ B) (hδ₃ : 0 ≤ δ₃) (hLK : 0 ≤ LK)
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2)) (hD₀ : D₀ ∈ K)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E))
    (hHnorm : eLpNorm H 2
      (Measure.pi fun _ : Fin (n + 2) => μ) ≤ ENNReal.ofReal B)
    (hHmean : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ δ₃)
    (t : ℝ) (ht : 0 < t)
    (hMGF : ProbabilityTheory.HasSubgaussianMGF
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        goodSetLipschitzExtension D₀ hD₀ hLK hLip D -
          ∫ E, goodSetLipschitzExtension D₀ hD₀ hLK hLip E
            ∂Measure.pi fun _ : Fin (n + 2) => μ)
      (LOOConcentration.Concentration.subGaussianProxy ⟨C, hC.le⟩ ⟨LK, hLK⟩)
      (Measure.pi fun _ : Fin (n + 2) => μ)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let p := ν.real Kᶜ
    let η := Real.sqrt p *
      (B + |H D₀| + LK *
        (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀))
    let tail := if LK = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * LK ^ 2)))
    (MeasurableSet {D | |H D| > δ₃ + η + t} ∧
      MeasurableSet {D | H D > δ₃ + η + t} ∧
      MeasurableSet {D | -H D > δ₃ + η + t}) ∧
    (ν.real {D | |H D| > δ₃ + η + t} ≤ p + 2 * tail ∧
      ν.real {D | H D > δ₃ + η + t} ≤ p + tail ∧
      ν.real {D | -H D > δ₃ + η + t} ≤ p + tail) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let E := goodSetLipschitzExtension D₀ hD₀ hLK hLip
  let p : ℝ := ν.real Kᶜ
  let η : ℝ := Real.sqrt p *
    (B + |H D₀| + LK *
      (Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ) + datasetNorm D₀))
  let tail : ℝ := if LK = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * LK ^ 2)))
  let meanE : ℝ := ∫ D, E D ∂ν
  let X : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ := fun D => E D - meanE
  have hEmeas : Measurable E := goodSetLipschitzExtension_measurable D₀ hD₀ hLK hLip
  have hEint := goodSetLipschitzExtension_integrable μ hM₂ D₀ hD₀ hLK hLip
  have hMean := goodSetLipschitzExtension_mean_bound μ hM₂ hK hHmeas B δ₃ LK
    hB hδ₃ hLK D₀ hD₀ hLip hHnorm hHmean
  have hMean' : |meanE| ≤ δ₃ + η := by
    simpa [meanE, E, ν, p, η] using hMean
  have hXint : Integrable X ν := by
    exact hEint.sub (integrable_const meanE)
  have hXmean : ∫ D, X D ∂ν = 0 := by
    calc
      ∫ D, X D ∂ν = ∫ D, E D ∂ν - ∫ D, meanE ∂ν := by
        simpa [X] using (integral_sub hEint (integrable_const meanE))
      _ = meanE - meanE := by simp [meanE]
      _ = 0 := sub_self _
  let Cnn : NNReal := ⟨C, hC.le⟩
  let LKnn : NNReal := ⟨LK, hLK⟩
  have hCnn : 0 < Cnn := by exact_mod_cast hC
  have hCentered : LOOConcentration.Concentration.CenteredSubGaussianMGF ν Cnn LKnn X := by
    exact ⟨hXint, hXmean, by simpa [X, E, meanE, ν, Cnn, LKnn] using hMGF⟩
  have hChernoff := centeredSubGaussianMGF_strict_sign_tails hCnn hCentered t ht
  have hAgree : ∀ D ∈ K, E D = H D :=
    goodSetLipschitzExtension_eqOn D₀ hD₀ hLK hLip
  have hCnnVal : (Cnn : ℝ) = C := rfl
  have hLKnnVal : (LKnn : ℝ) = LK := rfl
  have hupperRaw : ν.real {D | X D > t} ≤
      (if (LKnn : ℝ) = 0 then 0 else
        Real.exp (-(t ^ 2 / (2 * (Cnn : ℝ) * (LKnn : ℝ) ^ 2)))) := hChernoff.1
  have hlowerRaw : ν.real {D | -X D > t} ≤
      (if (LKnn : ℝ) = 0 then 0 else
        Real.exp (-(t ^ 2 / (2 * (Cnn : ℝ) * (LKnn : ℝ) ^ 2)))) := hChernoff.2
  have hupperTail : ν.real {D | X D > t} ≤ tail := by
    rw [hLKnnVal, hCnnVal] at hupperRaw
    simpa [tail] using hupperRaw
  have hlowerTail : ν.real {D | -X D > t} ≤ tail := by
    rw [hLKnnVal, hCnnVal] at hlowerRaw
    simpa [tail] using hlowerRaw
  have hnegEvent : {D | meanE - E D > t} = {D | -X D > t} := by
    ext D
    simp only [Set.mem_ofPred_eq]
    rw [show meanE - E D = -X D by dsimp [X]; ring]
  have hlowerCentered : ν.real {D | meanE - E D > t} ≤ tail := by
    rw [hnegEvent]
    exact hlowerTail
  have htransfer := goodSetTailEventTransfer ν E H K hK hEmeas hHmeas hAgree
    meanE (δ₃ + η) t tail hMean' hupperTail hlowerCentered
  simpa [ν, p, η, tail, E] using htransfer

end LOOConcentration

#print axioms LOOConcentration.goodSetTailEventTransfer
#print axioms LOOConcentration.goodSetLipschitzExtension_tail_bounds
