import LOOConcentrationRevision.Analysis.RealQLpDerivativeZeroRemoval
import LOOConcentrationRevision.Analysis.RegularizedPowerLSISource
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open InnerProductSpace
open scoped ENNReal

/-- On a probability space, a bounded nonnegative function has increasing
real-power moments. This is the Lq-to-Lp step used after weighted Holder. -/
private theorem bounded_nonneg_moment_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (g : EuclideanSpace ℝ ι → ℝ) (hg : Continuous g)
    (hgnonneg : ∀ x, 0 ≤ g x) (B : ℝ)
    (hgbound : ∀ x, g x ≤ B) (q p : ℝ) (hq : 0 < q) (hqp : q ≤ p) :
    (∫ x, g x ^ q ∂μ) ^ (2 / q) ≤ (∫ x, g x ^ p ∂μ) ^ (2 / p) := by
  by_cases hpq : p = q
  · subst p
    rfl
  have hqp' : q < p := lt_of_le_of_ne hqp (Ne.symm hpq)
  let u : ℝ := p / q
  let v : ℝ := p / (p - q)
  have hu : 1 < u := by
    dsimp [u]
    rw [lt_div_iff₀ hq]
    linarith
  have hv : 1 < v := by
    have hpqdiff : 0 < p - q := by linarith
    dsimp [v]
    rw [lt_div_iff₀ hpqdiff]
    linarith
  have huv : u⁻¹ + v⁻¹ = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt hq, ne_of_gt (lt_of_lt_of_le hq hqp)]
    ring
  have hqnonneg : 0 ≤ q := hq.le
  have hqfun : Continuous (fun x => g x ^ q) :=
    (Real.continuous_rpow_const hqnonneg).comp hg
  have hpfun : Continuous (fun x => g x ^ p) :=
    (Real.continuous_rpow_const (le_trans hqnonneg hqp)).comp hg
  have hqbound (x : EuclideanSpace ℝ ι) :
      ‖g x ^ q‖ ≤ max B 1 ^ q := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hgnonneg x) _)]
    exact Real.rpow_le_rpow (hgnonneg x)
      ((hgbound x).trans (le_max_left _ _)) hqnonneg
  have hqMem : MemLp (fun x => g x ^ q) (ENNReal.ofReal u) μ :=
    MemLp.of_bound hqfun.aestronglyMeasurable (max B 1 ^ q)
      (Filter.Eventually.of_forall hqbound)
  have h1Mem : MemLp (fun _ : EuclideanSpace ℝ ι => (1 : ℝ))
      (ENNReal.ofReal v) μ :=
    MemLp.of_bound continuous_const.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun _ => by norm_num)
  have hqvnonneg : ∀ᵐ x ∂μ, 0 ≤ g x ^ q :=
    Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hgnonneg x) _
  have h1nonneg : ∀ᵐ x ∂μ, 0 ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => zero_le_one
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨hu, huv⟩)
    hqvnonneg h1nonneg hqMem h1Mem
  have hPower (x : EuclideanSpace ℝ ι) : (g x ^ q) ^ u = g x ^ p := by
    calc
      (g x ^ q) ^ u = g x ^ (q * u) := (Real.rpow_mul (hgnonneg x) q u).symm
      _ = g x ^ p := by congr 1; dsimp [u]; field_simp
  have hIntegralPower :
      (∫ x, (g x ^ q) ^ u ∂μ) = ∫ x, g x ^ p ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hPower x)
  have hMomentqInt : Integrable (fun x => g x ^ q) μ := by
    refine (integrable_const (max B 1 ^ q)).mono' hqfun.measurable.aestronglyMeasurable ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hgnonneg x) _)] using hqbound x
  have hMomentpInt : Integrable (fun x => g x ^ p) μ := by
    have hpbound (x : EuclideanSpace ℝ ι) :
        ‖g x ^ p‖ ≤ max B 1 ^ p := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hgnonneg x) _)]
      exact Real.rpow_le_rpow (hgnonneg x)
        ((hgbound x).trans (le_max_left _ _)) (le_trans hqnonneg hqp)
    refine (integrable_const (max B 1 ^ p)).mono' hpfun.measurable.aestronglyMeasurable ?_
    filter_upwards with x
    exact hpbound x
  have hqnonnegInt : 0 ≤ ∫ x, g x ^ q ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (hgnonneg x) _
  have hpnonnegInt : 0 ≤ ∫ x, g x ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (hgnonneg x) _
  have hMomentHolder :
      (∫ x, g x ^ q ∂μ) ≤ (∫ x, g x ^ p ∂μ) ^ (q / p) := by
    calc
      (∫ x, g x ^ q ∂μ) = ∫ x, (g x ^ q) * 1 ∂μ := by simp
      _ ≤ (∫ x, (g x ^ q) ^ u ∂μ) ^ (1 / u) *
          (∫ x, (1 : ℝ) ^ v ∂μ) ^ (1 / v) := hHolder
      _ = (∫ x, g x ^ p ∂μ) ^ (q / p) := by
        rw [hIntegralPower]
        have hSecond : (∫ x, (1 : ℝ) ^ v ∂μ) ^ (1 / v) = 1 := by
          simp
        rw [hSecond]
        dsimp [u]
        field_simp [ne_of_gt hq, ne_of_gt (lt_of_lt_of_le hq hqp)]
  have hMomentHolder' := Real.rpow_le_rpow hqnonnegInt hMomentHolder (by positivity : 0 ≤ 2 / q)
  calc
    (∫ x, g x ^ q ∂μ) ^ (2 / q) ≤
        ((∫ x, g x ^ p ∂μ) ^ (q / p)) ^ (2 / q) := hMomentHolder'
    _ = (∫ x, g x ^ p ∂μ) ^ (2 / p) := by
      calc
        ((∫ x, g x ^ p ∂μ) ^ (q / p)) ^ (2 / q) =
            (∫ x, g x ^ p ∂μ) ^ ((q / p) * (2 / q)) :=
              (Real.rpow_mul hpnonnegInt (q / p) (2 / q)).symm
        _ = (∫ x, g x ^ p ∂μ) ^ (2 / p) := by congr 1; field_simp


/-- The actual regularized real-q derivative bound for a bounded smooth
source. The entropy producer is the separate proposal
`bounded_smooth_regularized_power_entropy_le`; this theorem constructs the
exact derivative consumer, weighted Holder factors, integrability, and
probability moment comparison internally. -/
theorem bounded_smooth_regularized_realQ_derivative_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (F : EuclideanSpace ℝ ι → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B ∧ ‖gradient F x‖ ≤ B)
    (ε q p : ℝ) (hε : 0 < ε) (hq : 2 < q) (hqp : q ≤ p) :
    deriv (fun r : ℝ => (∫ x,
      |Real.sqrt (F x ^ 2 + ε)| ^ r ∂μ) ^ (2 / r)) q ≤
      C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
  let R : EuclideanSpace ℝ ι → ℝ := fun x => F x ^ 2 + ε
  let V : EuclideanSpace ℝ ι → ℝ := fun x => R x ^ (q / 2 - 1)
  let G : EuclideanSpace ℝ ι → ℝ := fun x => ‖gradient F x‖
  let H : EuclideanSpace ℝ ι → ℝ := fun x => G x ^ (2 : ℕ)
  let M : ℝ := ∫ x, R x ^ (q / 2) ∂μ
  let Rmax : ℝ := B ^ 2 + ε
  let r : ℝ := q / (q - 2)
  let s : ℝ := q / 2
  have hq2 : 0 < q - 2 := by linarith
  have hs : 0 < s := by dsimp [s]; linarith
  have halpha : 0 < q / 2 - 1 := by linarith
  have hRmax : 0 < Rmax := by dsimp [Rmax]; positivity
  have hRbounds (x : EuclideanSpace ℝ ι) : 0 < R x ∧ R x ≤ Rmax := by
    constructor
    · dsimp [R]
      positivity
    · have hsq : F x ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg (F x)) hB).2 (hbound x).1
      dsimp [R, Rmax]
      linarith
  have hRcontDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := by
    dsimp [R]
    exact (hF.pow 2).add contDiff_const
  have hRpowContDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => R x ^ (q / 2)) :=
    hRcontDiff.rpow_const_of_ne fun x => ne_of_gt (hRbounds x).1
  have hVContDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := by
    dsimp [V]
    exact hRcontDiff.rpow_const_of_ne fun x => ne_of_gt (hRbounds x).1
  have hRpowCont : Continuous (fun x => R x ^ (q / 2)) := hRpowContDiff.continuous
  have hVCont : Continuous V := hVContDiff.continuous
  have hRpowBound (x : EuclideanSpace ℝ ι) :
      R x ^ (q / 2) ≤ Rmax ^ (q / 2) :=
    Real.rpow_le_rpow (le_of_lt (hRbounds x).1) (hRbounds x).2 (by linarith)
  have hRpowNonneg (x : EuclideanSpace ℝ ι) : 0 ≤ R x ^ (q / 2) :=
    Real.rpow_nonneg (le_of_lt (hRbounds x).1) _
  have hMInt : Integrable (fun x => R x ^ (q / 2)) μ := by
    refine (integrable_const (Rmax ^ (q / 2))).mono' hRpowCont.measurable.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hRpowNonneg x)]
    exact hRpowBound x
  have hRlower (x : EuclideanSpace ℝ ι) : ε ≤ R x := by
    dsimp [R]
    nlinarith [sq_nonneg (F x)]
  have hMlower : ε ^ (q / 2) ≤ M := by
    calc
      ε ^ (q / 2) = ∫ _x : EuclideanSpace ℝ ι, ε ^ (q / 2) ∂μ := by simp
      _ ≤ ∫ x, R x ^ (q / 2) ∂μ := by
        apply integral_mono_ae (integrable_const (ε ^ (q / 2))) hMInt
        filter_upwards with x
        exact Real.rpow_le_rpow hε.le (hRlower x) (by linarith)
  have hMpos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hε _) hMlower
  have hGradCont : Continuous (gradient F) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hF.continuous_fderiv (by simp))
  have hGCont : Continuous G := by
    dsimp [G]
    exact hGradCont.norm
  have hGnonneg (x : EuclideanSpace ℝ ι) : 0 ≤ G x := by dsimp [G]; positivity
  have hGbound (x : EuclideanSpace ℝ ι) : G x ≤ B := by
    dsimp [G]
    exact (hbound x).2
  have hHCont : Continuous H := by
    dsimp [H]
    exact hGCont.pow 2
  have hHnonneg (x : EuclideanSpace ℝ ι) : 0 ≤ H x := by dsimp [H]; positivity
  have hHbound (x : EuclideanSpace ℝ ι) : H x ≤ B ^ 2 := by
    dsimp [H]
    exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x).2
  have hRweightBound (x : EuclideanSpace ℝ ι) :
      V x ≤ Rmax ^ (q / 2 - 1) := by
    dsimp [V]
    exact Real.rpow_le_rpow (le_of_lt (hRbounds x).1) (hRbounds x).2 halpha.le
  have hVnonneg (x : EuclideanSpace ℝ ι) : 0 ≤ V x := by
    dsimp [V]
    exact Real.rpow_nonneg (le_of_lt (hRbounds x).1) _
  have hVMem : MemLp V (ENNReal.ofReal r) μ := by
    apply MemLp.of_bound hVCont.aestronglyMeasurable (Rmax ^ (q / 2 - 1))
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnonneg x)]
    exact hRweightBound x
  have hHMem : MemLp H (ENNReal.ofReal s) μ := by
    apply MemLp.of_bound hHCont.aestronglyMeasurable (B ^ 2)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg x)]
    exact hHbound x
  have hr_gt_one : 1 < r := by
    dsimp [r]
    rw [lt_div_iff₀ hq2]
    linarith
  have hrs_inv : r⁻¹ + s⁻¹ = 1 := by
    dsimp [r, s]
    field_simp [ne_of_gt hq2, ne_of_gt (by linarith : 0 < q)]
    ring
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨hr_gt_one, hrs_inv⟩)
    (Filter.Eventually.of_forall hVnonneg)
    (Filter.Eventually.of_forall hHnonneg) hVMem hHMem
  have hVpower (x : EuclideanSpace ℝ ι) :
      V x ^ r = R x ^ (q / 2) := by
    dsimp [V, r]
    calc
      (R x ^ (q / 2 - 1)) ^ (q / (q - 2)) =
          R x ^ ((q / 2 - 1) * (q / (q - 2))) :=
        (Real.rpow_mul (le_of_lt (hRbounds x).1) _ _).symm
      _ = R x ^ (q / 2) := by congr 1; field_simp [ne_of_gt hq2]
  have hHpower (x : EuclideanSpace ℝ ι) :
      H x ^ s = G x ^ q := by
    dsimp [H, G, s]
    calc
      (‖gradient F x‖ ^ (2 : ℕ)) ^ (q / 2) =
          (‖gradient F x‖ ^ (2 : ℝ)) ^ (q / 2) := by rw [← Real.rpow_two]
      _ = ‖gradient F x‖ ^ ((2 : ℝ) * (q / 2)) :=
        (Real.rpow_mul (norm_nonneg (gradient F x)) _ _).symm
      _ = ‖gradient F x‖ ^ q := by congr 1; ring
  have hMassV : (∫ x, V x ^ r ∂μ) = M :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hVpower x)
  have hMassH : (∫ x, H x ^ s ∂μ) = ∫ x, G x ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hHpower x)
  have hHolderBound :
      (∫ x, V x * H x ∂μ) ≤
        M ^ (1 - 2 / q) * (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
    calc
      (∫ x, V x * H x ∂μ) ≤
          (∫ x, V x ^ r ∂μ) ^ (1 / r) *
            (∫ x, H x ^ s ∂μ) ^ (1 / s) := hHolder
      _ = M ^ (1 - 2 / q) * (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
        rw [hMassV, hMassH]
        congr 2 <;> dsimp [r, s] <;> field_simp [ne_of_gt hq2, ne_of_gt (by linarith : 0 < q)]
  have hEntropy := bounded_smooth_regularized_power_entropy_le
    μ C hC hLC F hF B hB hbound ε q hε hq
  have hEntropy' :
      (∫ x, R x ^ (q / 2) * Real.log (R x ^ (q / 2)) ∂μ) -
        M * Real.log M ≤
      (C * q ^ 2 / 2) * ∫ x, V x * H x ∂μ := by
    simpa [R, V, H, M] using hEntropy
  have hDeriv :=
    (LOOConcentrationRevision.regularized_abs_realQLp_normSq_consumer
      (μ := μ) (g := F) (B := B) (ε := ε) (q := q)
      hF.continuous.measurable hB (fun x => (hbound x).1) hε (by linarith : 2 ≤ q)).deriv
  have hSqrtPower (x : EuclideanSpace ℝ ι) :
      |Real.sqrt (R x)| ^ q = R x ^ (q / 2) := by
    calc
      |Real.sqrt (R x)| ^ q = (R x ^ (1 / (2 : ℝ))) ^ q := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
      _ = R x ^ ((1 / (2 : ℝ)) * q) :=
        (Real.rpow_mul (le_of_lt (hRbounds x).1) _ _).symm
      _ = R x ^ (q / 2) := by congr 1; ring
  have hDeriv' :
      deriv (fun r : ℝ => (∫ x, |Real.sqrt (R x)| ^ r ∂μ) ^ (2 / r)) q =
        (2 / q ^ 2) * M ^ (2 / q - 1) *
          ((∫ x, R x ^ (q / 2) * Real.log (R x ^ (q / 2)) ∂μ) -
            M * Real.log M) := by
    simpa [R, M, hSqrtPower] using hDeriv
  have hRaw :
      deriv (fun r : ℝ => (∫ x, |Real.sqrt (R x)| ^ r ∂μ) ^ (2 / r)) q ≤
        C * M ^ (2 / q - 1) * (∫ x, V x * H x ∂μ) := by
    rw [hDeriv']
    calc
      (2 / q ^ 2) * M ^ (2 / q - 1) *
          ((∫ x, R x ^ (q / 2) * Real.log (R x ^ (q / 2)) ∂μ) -
            M * Real.log M) ≤
        (2 / q ^ 2) * M ^ (2 / q - 1) *
          ((C * q ^ 2 / 2) * ∫ x, V x * H x ∂μ) :=
        mul_le_mul_of_nonneg_left hEntropy' (by positivity)
      _ = C * M ^ (2 / q - 1) * (∫ x, V x * H x ∂μ) := by
        field_simp [ne_of_gt (by linarith : 0 < q)]
  have hqMoment := bounded_nonneg_moment_mono μ G hGCont hGnonneg B hGbound q p
    (by linarith : 0 < q) hqp
  have hBoundq :
      deriv (fun r : ℝ => (∫ x, |Real.sqrt (R x)| ^ r ∂μ) ^ (2 / r)) q ≤
        C * (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
    have hCoeff : 0 ≤ C * M ^ (2 / q - 1) :=
      mul_nonneg hC (Real.rpow_nonneg (le_of_lt hMpos) _)
    calc
      _ ≤ C * M ^ (2 / q - 1) * (∫ x, V x * H x ∂μ) := hRaw
      _ ≤ C * M ^ (2 / q - 1) *
            (M ^ (1 - 2 / q) * (∫ x, G x ^ q ∂μ) ^ (2 / q)) :=
          mul_le_mul_of_nonneg_left hHolderBound hCoeff
      _ = C * (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
        calc
          C * M ^ (2 / q - 1) *
              (M ^ (1 - 2 / q) * (∫ x, G x ^ q ∂μ) ^ (2 / q)) =
              C * (M ^ (2 / q - 1) * M ^ (1 - 2 / q)) *
                (∫ x, G x ^ q ∂μ) ^ (2 / q) := by ring
          _ = C * (M ^ ((2 / q - 1) + (1 - 2 / q))) *
                (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
              rw [← Real.rpow_add hMpos]
          _ = C * (∫ x, G x ^ q ∂μ) ^ (2 / q) := by
              have hexp : (2 / q - 1) + (1 - 2 / q) = 0 := by ring
              rw [hexp, Real.rpow_zero]
              ring
  calc
    _ = deriv (fun r : ℝ => (∫ x, |Real.sqrt (R x)| ^ r ∂μ) ^ (2 / r)) q := by
      rfl
    _ ≤ C * (∫ x, G x ^ q ∂μ) ^ (2 / q) := hBoundq
    _ ≤ C * (∫ x, G x ^ p ∂μ) ^ (2 / p) :=
      mul_le_mul_of_nonneg_left hqMoment hC
    _ = C * (∫ x, ‖gradient F x‖ ^ p ∂μ) ^ (2 / p) := by
      rfl

#print axioms bounded_smooth_regularized_realQ_derivative_le

end LOOConcentration.Revision
