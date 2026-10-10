import LOOConcentration.Geometry.NormTransport
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Lipschitz extension from a good set

The infimal extension is formed with the frozen, unnormalized dataset norm.
Its pointwise properties are independent of the probability law; continuity
then gives measurability for the full-sample product law.
-/

set_option autoImplicit false

namespace LOOConcentration

open scoped MeasureTheory Topology

private theorem datasetNorm_neg {k m N : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) N) :
    datasetNorm (-D) = datasetNorm D := by
  rw [datasetNorm_eq_euclidean, datasetNorm_eq_euclidean]
  have hneg : datasetToEuclidean (-D) = -datasetToEuclidean D := by
    apply PiLp.ext
    intro q
    rcases q with ⟨i, c⟩
    cases c <;> simp [datasetToEuclidean]
  rw [hneg, norm_neg]

private theorem datasetNorm_sub_symm {k m N : ℕ}
    (D E : Dataset (Observation (k + 1) (m + 1)) N) :
    datasetNorm (D - E) = datasetNorm (E - D) := by
  have h : E - D = -(D - E) := by
    ext i <;> simp only [Pi.sub_apply, Pi.neg_apply] <;> ring_nf
  rw [h, datasetNorm_neg]

private theorem datasetNorm_sub_triangle {k m N : ℕ}
    (D E F : Dataset (Observation (k + 1) (m + 1)) N) :
    datasetNorm (D - F) ≤ datasetNorm (D - E) + datasetNorm (E - F) := by
  have h : D - F = (D - E) + (E - F) := by
    ext i <;> simp only [Pi.sub_apply, Pi.add_apply] <;> ring_nf
  rw [h]
  exact datasetNorm_add_le _ _

/-- The source's McShane infimum, specialized to the exact full dataset
carrier and frozen dataset norm. The anchor and pairwise control are required
at construction time, so each public instance has a finite source infimum. -/
noncomputable def goodSetLipschitzExtension {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (_hD₀ : D₀ ∈ K) (_hLK : 0 ≤ LK)
    (_hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ :=
  fun D => ⨅ V : {V // V ∈ K}, H V.1 + LK * datasetNorm (D - V.1)

private theorem goodSetLipschitzExtension_bddBelow {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E))
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) :
    BddBelow (Set.range fun V : {V // V ∈ K} =>
      H V.1 + LK * datasetNorm (D - V.1)) := by
  refine ⟨H D₀ - LK * datasetNorm (D - D₀), ?_⟩
  rintro y ⟨V, rfl⟩
  have hpair := (abs_le.mp (hLip D₀ hD₀ V.1 V.2)).2
  have htri₀ := datasetNorm_sub_triangle D₀ D V.1
  have htri : datasetNorm (D₀ - V.1) ≤
      datasetNorm (D - D₀) + datasetNorm (D - V.1) := by
    calc
      datasetNorm (D₀ - V.1) ≤
          datasetNorm (D₀ - D) + datasetNorm (D - V.1) := htri₀
      _ = datasetNorm (D - D₀) + datasetNorm (D - V.1) := by
        rw [datasetNorm_sub_symm]
  have hmul := mul_le_mul_of_nonneg_left htri hLK
  rw [mul_add] at hmul
  linarith

/-- On the good set, the infimal extension agrees pointwise with the original
function. -/
theorem goodSetLipschitzExtension_eqOn {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    ∀ D ∈ K, goodSetLipschitzExtension D₀ hD₀ hLK hLip D = H D := by
  classical
  have hKne : Nonempty {V // V ∈ K} := ⟨⟨D₀, hD₀⟩⟩
  intro D hD
  have hB := goodSetLipschitzExtension_bddBelow D₀ hD₀ hLK hLip D
  unfold goodSetLipschitzExtension
  refine le_antisymm ?_ ?_
  · have hzero : datasetNorm (0 : Dataset (Observation (k + 1) (m + 1)) (n + 2)) = 0 := by
      simp [datasetNorm, datasetNormSq, observationNormSq]
    simpa [hzero] using (ciInf_le hB ⟨D, hD⟩)
  · apply le_ciInf
    intro V
    have hupper := (abs_le.mp (hLip D hD V.1 V.2)).2
    linarith

/-- The infimum is globally Lipschitz with the exact frozen-norm constant. -/
theorem goodSetLipschitzExtension_lipschitz {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    ∀ D E, |goodSetLipschitzExtension D₀ hD₀ hLK hLip D -
      goodSetLipschitzExtension D₀ hD₀ hLK hLip E| ≤ LK * datasetNorm (D - E) := by
  classical
  have hKne : Nonempty {V // V ∈ K} := ⟨⟨D₀, hD₀⟩⟩
  intro D E
  have hupperAll : ∀ D E, goodSetLipschitzExtension D₀ hD₀ hLK hLip D ≤
      goodSetLipschitzExtension D₀ hD₀ hLK hLip E + LK * datasetNorm (D - E) := by
    intro D E
    unfold goodSetLipschitzExtension
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun V => ?_
    rw [sub_le_iff_le_add]
    have htri := datasetNorm_sub_triangle D E V.1
    have htri' : datasetNorm (D - V.1) ≤
        datasetNorm (E - V.1) + datasetNorm (D - E) := by
      calc
        datasetNorm (D - V.1) ≤
            datasetNorm (D - E) + datasetNorm (E - V.1) := htri
        _ = datasetNorm (E - V.1) + datasetNorm (D - E) := by ac_rfl
    have hmul := mul_le_mul_of_nonneg_left htri' hLK
    rw [mul_add] at hmul
    calc
      (⨅ V : {V // V ∈ K}, H V.1 + LK * datasetNorm (D - V.1)) ≤
          H V.1 + LK * datasetNorm (D - V.1) :=
        ciInf_le (goodSetLipschitzExtension_bddBelow D₀ hD₀ hLK hLip D) V
      _ ≤ H V.1 + LK * (datasetNorm (E - V.1) + datasetNorm (D - E)) := by
        nlinarith [hmul]
      _ = H V.1 + LK * datasetNorm (E - V.1) +
            LK * datasetNorm (D - E) := by ring
  have hupper := hupperAll D E
  have hlower : -(LK * datasetNorm (D - E)) ≤
      goodSetLipschitzExtension D₀ hD₀ hLK hLip D -
        goodSetLipschitzExtension D₀ hD₀ hLK hLip E := by
    have hreverse := hupperAll E D
    have hnorm := datasetNorm_sub_symm D E
    rw [← hnorm] at hreverse
    linarith
  have hupper' : goodSetLipschitzExtension D₀ hD₀ hLK hLip D -
      goodSetLipschitzExtension D₀ hD₀ hLK hLip E ≤ LK * datasetNorm (D - E) := by
    linarith
  exact abs_le.mpr ⟨hlower, hupper'⟩

/-- The anchor gives a finite, explicit two-sided bound on every infimum. -/
theorem goodSetLipschitzExtension_anchor_bound {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    ∀ D, |goodSetLipschitzExtension D₀ hD₀ hLK hLip D| ≤
      |H D₀| + LK * (datasetNorm D + datasetNorm D₀) := by
  classical
  have hKne : Nonempty {V // V ∈ K} := ⟨⟨D₀, hD₀⟩⟩
  intro D
  have hlower : H D₀ - LK * datasetNorm (D - D₀) ≤
      goodSetLipschitzExtension D₀ hD₀ hLK hLip D := by
    unfold goodSetLipschitzExtension
    apply le_ciInf
    intro V
    have hpair := (abs_le.mp (hLip D₀ hD₀ V.1 V.2)).2
    have htri₀ := datasetNorm_sub_triangle D₀ D V.1
    have htri : datasetNorm (D₀ - V.1) ≤
        datasetNorm (D - D₀) + datasetNorm (D - V.1) := by
      calc
        datasetNorm (D₀ - V.1) ≤
            datasetNorm (D₀ - D) + datasetNorm (D - V.1) := htri₀
        _ = datasetNorm (D - D₀) + datasetNorm (D - V.1) := by
          rw [datasetNorm_sub_symm]
    have hmul := mul_le_mul_of_nonneg_left htri hLK
    rw [mul_add] at hmul
    linarith
  have hB := goodSetLipschitzExtension_bddBelow D₀ hD₀ hLK hLip D
  have hupper : goodSetLipschitzExtension D₀ hD₀ hLK hLip D ≤
      H D₀ + LK * datasetNorm (D - D₀) := by
    unfold goodSetLipschitzExtension
    simpa using (ciInf_le hB ⟨D₀, hD₀⟩)
  have hnormD₀ : 0 ≤ datasetNorm D₀ := Real.sqrt_nonneg _
  have hnormDiff : datasetNorm (D - D₀) ≤ datasetNorm D + datasetNorm D₀ := by
    calc
      datasetNorm (D - D₀) ≤ datasetNorm (D - 0) + datasetNorm (0 - D₀) :=
        datasetNorm_sub_triangle D 0 D₀
      _ = datasetNorm D + datasetNorm D₀ := by simp [datasetNorm_neg]
  have hcoef : 0 ≤ LK * (datasetNorm D + datasetNorm D₀) :=
    mul_nonneg hLK (add_nonneg (Real.sqrt_nonneg _) hnormD₀)
  have hleft : -( |H D₀| + LK * (datasetNorm D + datasetNorm D₀)) ≤
      goodSetLipschitzExtension D₀ hD₀ hLK hLip D := by
    have habs : -|H D₀| ≤ H D₀ := neg_abs_le _
    have hmul := mul_le_mul_of_nonneg_left hnormDiff hLK
    linarith
  have hright : goodSetLipschitzExtension D₀ hD₀ hLK hLip D ≤
      |H D₀| + LK * (datasetNorm D + datasetNorm D₀) := by
    have habs : H D₀ ≤ |H D₀| := le_abs_self _
    have hmul := mul_le_mul_of_nonneg_left hnormDiff hLK
    linarith
  exact abs_le.mpr ⟨hleft, hright⟩

private theorem continuous_datasetToEuclidean {k m N : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation (k + 1) (m + 1)) N →
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) N)) := by
  change Continuous (fun D : Dataset (Observation (k + 1) (m + 1)) N =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate (k + 1) (m + 1) N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate (k + 1) (m + 1) N => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl a => exact ((continuous_apply a).comp continuous_fst).comp (continuous_apply i)
    | inr b => exact ((continuous_apply b).comp continuous_snd).comp (continuous_apply i))

private theorem continuousAt_datasetNorm_sub {k m N : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) N) :
    ContinuousAt (fun E => datasetNorm (E - D)) D := by
  have hcont : Continuous fun E : Dataset (Observation (k + 1) (m + 1)) N =>
      datasetToEuclidean (E - D) :=
    continuous_datasetToEuclidean.comp (continuous_id.sub continuous_const)
  have heq : (fun E => datasetNorm (E - D)) =
      fun E => ‖datasetToEuclidean (E - D)‖ := by
    funext E
    exact datasetNorm_eq_euclidean (E - D)
  rw [heq]
  exact (continuous_norm.comp hcont).continuousAt

/-- The infimal extension is continuous, hence measurable on the Borel full
dataset carrier with its usual product topology. -/
theorem goodSetLipschitzExtension_measurable {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    Measurable (goodSetLipschitzExtension D₀ hD₀ hLK hLip) := by
  have hcont : Continuous (goodSetLipschitzExtension D₀ hD₀ hLK hLip) := by
    rw [continuous_iff_continuousAt]
    intro D
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp
      (continuousAt_datasetNorm_sub D) (ε / (LK + 1)) (by positivity)
    refine ⟨η, hη, ?_⟩
    intro E hE
    have hnorm : datasetNorm (E - D) < ε / (LK + 1) := by
      have hdist := hηbound hE
      have hzero : datasetNorm (D - D) = 0 := by
        simp [datasetNorm, datasetNormSq, observationNormSq]
      have hnonneg : 0 ≤ datasetNorm (E - D) := Real.sqrt_nonneg _
      rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnonneg] at hdist
      exact hdist
    have hbound := goodSetLipschitzExtension_lipschitz D₀ hD₀ hLK hLip E D
    rw [Real.dist_eq]
    change |goodSetLipschitzExtension D₀ hD₀ hLK hLip E -
      goodSetLipschitzExtension D₀ hD₀ hLK hLip D| < ε
    calc
      |goodSetLipschitzExtension D₀ hD₀ hLK hLip E -
          goodSetLipschitzExtension D₀ hD₀ hLK hLip D| ≤
            LK * datasetNorm (E - D) := hbound
      _ < ε := by
        have hKmul : LK * datasetNorm (E - D) ≤
            (LK + 1) * datasetNorm (E - D) := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact Real.sqrt_nonneg _
        have hkp : 0 < LK + 1 := by linarith
        have hlt : (LK + 1) * datasetNorm (E - D) <
            (LK + 1) * (ε / (LK + 1)) := mul_lt_mul_of_pos_left hnorm hkp
        have heq : (LK + 1) * (ε / (LK + 1)) = ε := by field_simp
        rw [heq] at hlt
        exact hKmul.trans_lt hlt
  exact hcont.measurable

end LOOConcentration
