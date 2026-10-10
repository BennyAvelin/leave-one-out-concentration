import LOOConcentrationRevision.FunctionalInequalities.SmoothGeneratorLSI
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.Concentration.EntropyVariational
import LOOConcentration.Concentration.EntropyToMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# The bounded smooth Herbst argument

The generator inequality gives the tilted entropy estimate for every real
parameter. The bounded-observable calculus then yields the centered MGF bound.
-/

set_option autoImplicit false

open MeasureTheory
open InnerProductSpace

namespace LOOConcentration.Revision

noncomputable section

private theorem gradient_exp_const_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a : ℝ)
    (x : EuclideanSpace ℝ ι) :
    gradient (fun y => Real.exp (a * F y)) x =
      (a * Real.exp (a * F x)) • gradient F x := by
  rw [gradient, gradient]
  have hd : DifferentiableAt ℝ F x := hF.contDiffAt.differentiableAt (by simp)
  rw [fderiv_exp (hd.const_mul a), fderiv_const_mul hd a]
  simp only [map_smul, smul_smul]
  congr 1
  ring

private theorem integrable_sq_gradient_of_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℝ ι → ℝ)
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, ‖gradient H x‖ ≤ K) :
    Integrable (fun x => ‖gradient H x‖ ^ 2) μ := by
  let E := EuclideanSpace ℝ ι
  have hgradCont : Continuous (gradient H) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hH.continuous_fderiv (by simp))
  have hmeas : Measurable (fun x : E => ‖gradient H x‖ ^ 2) :=
    (hgradCont.norm.pow 2).measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable (K ^ 2) ?_
  filter_upwards with x
  change |‖gradient H x‖ ^ 2| ≤ K ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hK).2 (hbound x)

private theorem tiltEntropy_eq_looconcentrationEntropy_exp_div
    {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} [IsProbabilityMeasure μ]
    {F : ι → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    LOOConcentration.tiltEntropy μ F t =
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (t * F x)) /
        LOOConcentration.tiltPartition μ F t := by
  let w : ι → ℝ := fun x => Real.exp (t * F x)
  have hZ : 0 < LOOConcentration.tiltPartition μ F t :=
    LOOConcentration.tiltPartition_pos hFmeas hB hF
  have hIpos : 0 < (∫ x, Real.exp (t * F x) ∂μ) := by
    simpa [LOOConcentration.tiltPartition] using hZ
  have hW : Integrable w μ :=
    LOOConcentration.logPartition_integrable hFmeas hF
  have hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ B := by
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hF x
  have hWF : Integrable (fun x => w x * F x) μ := by
    convert hW.bdd_mul hFmeas.aestronglyMeasurable hFbound using 1
    ext x
    ring
  have hWlog : (∫ x, w x * Real.log (w x) ∂μ) =
      t * (∫ x, F x * Real.exp (t * F x) ∂μ) := by
    calc
      (∫ x, w x * Real.log (w x) ∂μ) =
          ∫ x, t * (F x * Real.exp (t * F x)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [w, Real.log_exp]
            ring
      _ = t * (∫ x, F x * Real.exp (t * F x) ∂μ) := integral_const_mul t _
  have hMean :
      (∫ x, LOOConcentration.tiltDensity μ F t x * F x ∂μ) =
        (∫ x, F x * Real.exp (t * F x) ∂μ) /
          LOOConcentration.tiltPartition μ F t := by
    calc
      (∫ x, LOOConcentration.tiltDensity μ F t x * F x ∂μ) =
          ∫ x, (F x * Real.exp (t * F x)) *
            (LOOConcentration.tiltPartition μ F t)⁻¹ ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              simp [LOOConcentration.tiltDensity, div_eq_mul_inv]
              ring
      _ = (∫ x, F x * Real.exp (t * F x) ∂μ) *
            (LOOConcentration.tiltPartition μ F t)⁻¹ := integral_mul_const _ _
      _ = _ := by rw [div_eq_mul_inv]
  rw [LOOConcentration.tiltEntropy_eq_tiltMean_sub_logPartition
    hFmeas hB hF, hMean]
  unfold LOOConcentration.looconcentrationEntropy
  dsimp [w]
  rw [hWlog, LOOConcentration.tiltPartition]
  field_simp [ne_of_gt hIpos]

private theorem bounded_smooth_tiltEntropy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hGradBound : ∀ x, ‖gradient F x‖ ≤ L)
    (u : ℝ) :
    LOOConcentration.tiltEntropy μ F u ≤ (C * L ^ 2 / 2) * u ^ 2 := by
  let a : ℝ := u / 2
  let G : EuclideanSpace ℝ ι → ℝ := fun x => Real.exp (a * F x)
  let A : ℝ := Real.exp (|a| * B)
  let D : ℝ := |a| * A * L
  have hA : 0 ≤ A := Real.exp_nonneg _
  have hD : 0 ≤ D := by positivity
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    dsimp [G]
    fun_prop
  have hFmeas : Measurable F := hF.continuous.measurable
  have hGbound : ∀ x, |G x| ≤ A ∧ ‖gradient G x‖ ≤ D := by
    intro x
    dsimp [G, A, D]
    constructor
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        a * F x ≤ |a * F x| := le_abs_self _
        _ = |a| * |F x| := abs_mul _ _
        _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hFbound x) (abs_nonneg _)
    · rw [gradient_exp_const_mul_eq hF a, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_of_pos (Real.exp_pos _)]
      have hExp : Real.exp (a * F x) ≤ A := by
        dsimp [A]
        apply Real.exp_le_exp.mpr
        calc
          a * F x ≤ |a * F x| := le_abs_self _
          _ = |a| * |F x| := abs_mul _ _
          _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hFbound x) (abs_nonneg _)
      calc
        |a| * Real.exp (a * F x) * ‖gradient F x‖ ≤
            |a| * A * ‖gradient F x‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hExp (abs_nonneg _)) (norm_nonneg _)
        _ ≤ |a| * A * L :=
          mul_le_mul_of_nonneg_left (hGradBound x) (mul_nonneg (abs_nonneg _) hA)
  have hGpair : ∀ x, |G x| ≤ A + D ∧ ‖gradient G x‖ ≤ A + D := by
    intro x
    constructor
    · exact (hGbound x).1.trans (le_add_of_nonneg_right hD)
    · exact (hGbound x).2.trans (le_add_of_nonneg_left hA)
  have hGexpSq : (fun x => G x ^ 2) = fun x => Real.exp (u * F x) := by
    funext x
    dsimp [G, a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hGradGInt : Integrable (fun x => ‖gradient G x‖ ^ 2) μ :=
    integrable_sq_gradient_of_bound μ G hGsmooth hD (fun x => (hGbound x).2)
  have hFexpInt : Integrable (fun x => Real.exp (u * F x)) μ :=
    LOOConcentration.logPartition_integrable hFmeas hFbound
  let Q : ℝ := (u ^ 2 / 4) * L ^ 2
  have hMajorInt : Integrable (fun x => Q * Real.exp (u * F x)) μ := by
    simpa [Q] using hFexpInt.const_mul ((u ^ 2 / 4) * L ^ 2)
  have hEnergyPoint : ∀ x, ‖gradient G x‖ ^ 2 ≤
      Q * Real.exp (u * F x) := by
    intro x
    have hGradNorm : ‖gradient G x‖ = |a| * Real.exp (a * F x) *
        ‖gradient F x‖ := by
      rw [gradient_exp_const_mul_eq hF a, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_of_pos (Real.exp_pos _)]
    have hFactor : 0 ≤ |a| * Real.exp (a * F x) := by positivity
    have hNormUpper : |a| * Real.exp (a * F x) * ‖gradient F x‖ ≤
        |a| * Real.exp (a * F x) * L :=
      mul_le_mul_of_nonneg_left (hGradBound x) hFactor
    have hNormUpper' : ‖gradient G x‖ ≤
        |a| * Real.exp (a * F x) * L := by
      rw [hGradNorm]
      exact hNormUpper
    have hSqUpper := (sq_le_sq₀ (norm_nonneg _) (by positivity :
        0 ≤ |a| * Real.exp (a * F x) * L)).2 hNormUpper'
    have hExpSq : Real.exp (u / 2 * F x) ^ 2 = Real.exp (u * F x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hFactorSq : (|a| * Real.exp (a * F x) * L) ^ 2 =
        Q * Real.exp (u * F x) := by
      dsimp [Q, a]
      rw [mul_pow, mul_pow, sq_abs, hExpSq]
      ring
    rw [hGradNorm]
    have hSqUpper' :
        (|a| * Real.exp (a * F x) * ‖gradient F x‖) ^ 2 ≤
          Q * Real.exp (u * F x) := by
      rw [hGradNorm] at hSqUpper
      exact hSqUpper.trans (le_of_eq hFactorSq)
    exact hSqUpper'
  have hEnergy :
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤ Q * LOOConcentration.logPartition μ F u := by
    calc
      (∫ x, ‖gradient G x‖ ^ 2 ∂μ) ≤
          ∫ x, Q * Real.exp (u * F x) ∂μ :=
            integral_mono hGradGInt hMajorInt (fun x => hEnergyPoint x)
      _ = Q * LOOConcentration.logPartition μ F u := by
            rw [integral_const_mul]
            rfl
  have hBase := bounded_smooth_entropy_le_of_logSobolevConstant_le
    μ C hC hLC G hGsmooth (A + D) (by positivity) hGpair
  change LOOConcentration.looconcentrationEntropy μ (fun x => G x ^ 2) ≤
    2 * C * ∫ x, ‖gradient G x‖ ^ 2 ∂μ at hBase
  rw [hGexpSq] at hBase
  have hRaw : LOOConcentration.looconcentrationEntropy μ
      (fun x => Real.exp (u * F x)) ≤
      ((C * L ^ 2 / 2) * u ^ 2) * LOOConcentration.logPartition μ F u := by
    calc
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (u * F x)) ≤
          2 * C * (∫ x, ‖gradient G x‖ ^ 2 ∂μ) := hBase
      _ ≤ 2 * C * (Q * LOOConcentration.logPartition μ F u) :=
          mul_le_mul_of_nonneg_left hEnergy (mul_nonneg (by norm_num) hC)
      _ = _ := by dsimp [Q]; ring
  have hZ : 0 < LOOConcentration.tiltPartition μ F u :=
    LOOConcentration.tiltPartition_pos hFmeas hB hFbound
  have hZeq : LOOConcentration.tiltPartition μ F u =
      LOOConcentration.logPartition μ F u := rfl
  have hDiv :
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (u * F x)) /
        LOOConcentration.tiltPartition μ F u ≤ (C * L ^ 2 / 2) * u ^ 2 := by
    rw [hZeq]
    exact (div_le_iff₀ (by simpa [hZeq] using hZ)).2 (by simpa [hZeq] using hRaw)
  calc
    LOOConcentration.tiltEntropy μ F u =
        LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (u * F x)) /
          LOOConcentration.tiltPartition μ F u :=
      tiltEntropy_eq_looconcentrationEntropy_exp_div hFmeas hB hFbound
    _ ≤ (C * L ^ 2 / 2) * u ^ 2 := hDiv

/-- For every parameter, the centered exponential is integrable and has the
sharp MGF bound with the same log-Sobolev constant. -/
theorem bounded_smooth_centered_exp_integrable_and_mgf_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hGradBound : ∀ x, ‖gradient F x‖ ≤ L)
    (lam : ℝ) :
    Integrable (fun x => Real.exp (lam * (F x - ∫ y, F y ∂μ))) μ ∧
      (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
        Real.exp ((C * L ^ 2 / 2) * lam ^ 2) := by
  let m : ℝ := ∫ y, F y ∂μ
  have hFmeas : Measurable F := hF.continuous.measurable
  have hEntropy : ∀ u, 0 < |u| → |u| ≤ |lam| + 1 →
      LOOConcentration.tiltEntropy μ F u ≤ (C * L ^ 2 / 2) * u ^ 2 := by
    intro u _hu _huΛ
    exact bounded_smooth_tiltEntropy_le μ C hC hLC F hF B L hB hL
      hFbound hGradBound u
  have hLog := LOOConcentration.boundedObservable_logPartitionLog_centered_of_entropy_bound
    (μ := μ) (F := F) hFmeas (B := B) (V := C * L ^ 2 / 2) (Λ := |lam| + 1)
    (t := lam) hB hFbound hEntropy (by linarith [abs_nonneg lam])
  have hZpos : 0 < LOOConcentration.logPartition μ F lam :=
    LOOConcentration.logPartition_pos hFmeas hFbound
  have hExpInt : Integrable (fun x => Real.exp (lam * F x)) μ :=
    LOOConcentration.logPartition_integrable hFmeas hFbound
  have hCenterEq :
      (fun x => Real.exp (lam * (F x - m))) =
        fun x => Real.exp (-lam * m) * Real.exp (lam * F x) := by
    funext x
    rw [show lam * (F x - m) = (-lam * m) + lam * F x by ring, Real.exp_add]
  constructor
  · rw [hCenterEq]
    exact hExpInt.const_mul _
  · have hIntegral :
      (∫ x, Real.exp (lam * (F x - m)) ∂μ) =
          Real.exp (-lam * m) * LOOConcentration.logPartition μ F lam := by
      rw [hCenterEq, integral_const_mul]
      rfl
    change (∫ x, Real.exp (lam * (F x - m)) ∂μ) ≤ _
    rw [hIntegral]
    calc
      Real.exp (-lam * m) * LOOConcentration.logPartition μ F lam =
          Real.exp (Real.log (LOOConcentration.logPartition μ F lam) + (-lam * m)) := by
            rw [Real.exp_add, Real.exp_log hZpos]
            ring
      _ = Real.exp (LOOConcentration.logPartitionLog μ F lam - lam * m) := by
            congr 1
            simp [LOOConcentration.logPartitionLog]
            ring
      _ ≤ Real.exp ((C * L ^ 2 / 2) * lam ^ 2) :=
            Real.exp_le_exp.mpr hLog

/-- Mathlib's standard sub-Gaussian interface, produced from the actual
centered MGF estimate above. -/
theorem bounded_smooth_hasSubgaussianMGF_of_logSobolevConstant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : LOOConcentration.Revision.logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hGradBound : ∀ x, ‖gradient F x‖ ≤ L) :
    ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ)
      (NNReal.mk (C * L ^ 2) (mul_nonneg hC (sq_nonneg L))) μ := by
  constructor
  · intro lam
    exact (bounded_smooth_centered_exp_integrable_and_mgf_le μ C hC hLC F hF
      B L hB hL hFbound hGradBound lam).1
  · intro lam
    have h := (bounded_smooth_centered_exp_integrable_and_mgf_le μ C hC hLC F hF
      B L hB hL hFbound hGradBound lam).2
    change (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
      Real.exp (((C * L ^ 2) * lam ^ 2) / 2)
    calc
      (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
          Real.exp ((C * L ^ 2 / 2) * lam ^ 2) := h
      _ = Real.exp (((C * L ^ 2) * lam ^ 2) / 2) := by
            congr 1
            ring

end
end LOOConcentration.Revision
