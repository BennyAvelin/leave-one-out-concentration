import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory
open LOOConcentration

namespace LOOConcentrationRevision

noncomputable section


variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual `q`-moment of a positive scalar observable. -/
noncomputable def realQLpMoment (μ : Measure Ω) (g : Ω → ℝ) (q : ℝ) : ℝ :=
  ∫ ω, g ω ^ q ∂μ

/-- Literal entropy of the actual `q`-power, with no normalization change. -/
noncomputable def realQLpEntropy (μ : Measure Ω) (g : Ω → ℝ) (q : ℝ) : ℝ :=
  (∫ ω, g ω ^ q * Real.log (g ω ^ q) ∂μ) -
    (∫ ω, g ω ^ q ∂μ) * Real.log (∫ ω, g ω ^ q ∂μ)

/-- Real scalar derivative using the canonical real normed-ring structures. -/
abbrev HasRealDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedCommRing.toAddCommGroup
    ((NormedAlgebra.toNormedSpace ℝ).toModule) _ _ f f' x

private theorem abs_log_between {a b x : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hlow := Real.log_le_log ha hax
  have hupp := Real.log_le_log hx hxb
  apply (abs_le).2
  constructor
  · calc
      -( |Real.log a| + |Real.log b|) ≤ -|Real.log a| := by
        have := abs_nonneg (Real.log b)
        linarith
      _ ≤ Real.log a := neg_abs_le _
      _ ≤ Real.log x := hlow
  · calc
      Real.log x ≤ Real.log b := hupp
      _ ≤ |Real.log b| := le_abs_self _
      _ ≤ |Real.log a| + |Real.log b| := by
        linarith [abs_nonneg (Real.log a)]

/-- Conditional positive-carrier formula. The uniform lower bound is retained explicitly:
this helper does not cover observables that vanish. Entropy is the literal integral expression. -/
theorem positive_realQLp_normSq_hasDerivAt
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {a b q : ℝ}
    (hmeas : Measurable g) (ha : 0 < a)
    (hlo : ∀ ω, a ≤ g ω) (hhi : ∀ ω, g ω ≤ b)
    (hq : 2 ≤ q) :
    HasRealDerivAt (fun p => realQLpMoment μ g p ^ (2 / p))
      ((2 / q ^ 2) * realQLpMoment μ g q ^ (2 / q - 1) *
        realQLpEntropy μ g q) q := by
  let F : Ω → ℝ := fun ω => Real.log (g ω)
  let K : ℝ := |Real.log a| + |Real.log b|
  have hK : 0 ≤ K := by positivity
  have hFmeas : Measurable F := Real.measurable_log.comp hmeas
  have hFbound : ∀ ω, |F ω| ≤ K := by
    intro ω
    exact abs_log_between ha (hlo ω) (hhi ω)
  let Z : ℝ → ℝ := logPartition μ F
  have hZpos : 0 < Z q := logPartition_pos hFmeas hFbound
  have hZder : HasRealDerivAt Z (∫ ω, F ω * Real.exp (q * F ω) ∂μ) q := by
    simpa [HasRealDerivAt, LOOConcentration.instAddCommGroupReal_lOOConcentration,
      LOOConcentration.instModuleReal_lOOConcentration] using
        (logPartition_hasDerivAt hFmeas hK hFbound)
  have hM : ∀ p, realQLpMoment μ g p = Z p := by
    intro p
    change (∫ ω, g ω ^ p ∂μ) = logPartition μ F p
    rw [logPartition]
    apply integral_congr_ae
    filter_upwards with ω
    dsimp [F]
    rw [Real.rpow_def_of_pos (lt_of_lt_of_le ha (hlo ω))]
    congr 1
    ring
  have hMq : 0 < realQLpMoment μ g q := by rw [hM q]; exact hZpos
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hexp : HasRealDerivAt (fun p : ℝ => 2 / p) (-2 / q ^ 2) q := by
    have h := (hasDerivAt_const q (2 : ℝ)).mul (hasDerivAt_inv hqne)
    convert h using 1
    · funext p
      simp [div_eq_mul_inv]
    · ring
  have hpow : HasRealDerivAt (fun p : ℝ => Z p ^ (2 / p))
      ((∫ ω, F ω * Real.exp (q * F ω) ∂μ) * (2 / q) * Z q ^ (2 / q - 1) +
        (-2 / q ^ 2) * Z q ^ (2 / q) * Real.log (Z q)) q :=
    hZder.rpow hexp hZpos
  have hpowM : (fun p : ℝ => Z p ^ (2 / p)) =
      (fun p => realQLpMoment μ g p ^ (2 / p)) := by
    funext p
    rw [← hM p]
  have hactual :
      (∫ ω, g ω ^ q * Real.log (g ω ^ q) ∂μ) =
        q * (∫ ω, F ω * Real.exp (q * F ω) ∂μ) := by
    calc
      (∫ ω, g ω ^ q * Real.log (g ω ^ q) ∂μ) =
          ∫ ω, q * (F ω * Real.exp (q * F ω)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [F]
        rw [Real.log_rpow (lt_of_lt_of_le ha (hlo ω)) q,
          Real.rpow_def_of_pos (lt_of_lt_of_le ha (hlo ω))]
        ring
      _ = q * (∫ ω, F ω * Real.exp (q * F ω) ∂μ) := integral_const_mul q _
  have hInt : (∫ ω, g ω ^ q ∂μ) = Z q := by
    simpa [realQLpMoment] using hM q
  have hrpowZ : Z q ^ (2 / q) = Z q ^ (2 / q - 1) * Z q := by
    calc
      Z q ^ (2 / q) = Z q ^ ((2 / q - 1) + 1) := by congr 1; ring
      _ = Z q ^ (2 / q - 1) * Z q ^ (1 : ℝ) := Real.rpow_add hZpos _ _
      _ = Z q ^ (2 / q - 1) * Z q := by rw [Real.rpow_one]
  rw [hpowM] at hpow
  convert hpow using 1
  rw [realQLpEntropy, hInt, hM q, hactual, hrpowZ]
  field_simp [hqne]
  ring

/-- The source-shaped regularized consumer. It applies the conditional formula to
`gε = sqrt (g^2 + ε)` and derives the required positive lower and finite upper bounds from
boundedness of `g`; it is not the unregularized source theorem. -/
theorem regularized_realQLp_normSq_hasDerivAt
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {B ε q : ℝ}
    (hmeas : Measurable g) (hB : 0 ≤ B) (hbound : ∀ ω, |g ω| ≤ B)
    (hε : 0 < ε) (hq : 2 ≤ q) :
    let gε : Ω → ℝ := fun ω => Real.sqrt (g ω ^ 2 + ε)
    HasRealDerivAt (fun p => realQLpMoment μ gε p ^ (2 / p))
      ((2 / q ^ 2) * realQLpMoment μ gε q ^ (2 / q - 1) *
        realQLpEntropy μ gε q) q := by
  dsimp
  let gε : Ω → ℝ := fun ω => Real.sqrt (g ω ^ 2 + ε)
  have ha : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hlo : ∀ ω, Real.sqrt ε ≤ gε ω := by
    intro ω
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (g ω)]
  have hhi : ∀ ω, gε ω ≤ Real.sqrt (B ^ 2 + ε) := by
    intro ω
    apply Real.sqrt_le_sqrt
    have hsquare : g ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (g ω)) hB).2 (hbound ω)
    nlinarith
  have hgεmeas : Measurable gε := by
    dsimp [gε]
    fun_prop
  exact positive_realQLp_normSq_hasDerivAt hgεmeas ha hlo hhi hq

end

end LOOConcentrationRevision
