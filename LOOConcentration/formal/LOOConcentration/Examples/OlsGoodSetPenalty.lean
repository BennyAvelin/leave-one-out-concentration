import LOOConcentration.Examples.OlsObservationGoodSet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped ENNReal Topology

/-!
# Actual OLS good-set penalty decay

This file instantiates the good-set penalty from the data-dependent
concentration formula with the actual observation Gaussian law, transported
OLS good set, wave-13 reference point, and exact pairwise constant. It proves
the scalar penalty decay only; it does not apply the concentration theorem to
the OLS error.
-/

/-- The real-valued probability of leaving the actual observation good set. -/
noncomputable def olsObservationGoodSetBadMass (n : ℕ) : ℝ :=
  (gaussianObservationSampleLaw (n + 3)).real (olsObservationGoodSet n)ᶜ

/-- The literal bad-set penalty from data-dependent concentration for the
actual OLS observation carrier: `B = sqrt 12`, the wave-13 reference point,
`LK = 36007 / sqrt N`, and the actual one-observation second moment. -/
noncomputable def olsObservationGoodSetPenalty (n : ℕ) : ℝ :=
  Real.sqrt (olsObservationGoodSetBadMass n) *
    (Real.sqrt 12 +
      |olsObservationTestError (olsObservationReferencePoint n)| +
      (36007 / Real.sqrt (n + 3 : ℝ)) *
        (Real.sqrt ((n + 3 : ℝ) *
          (∫ z : Observation 1 1, observationNormSq z ∂gaussianObservationLaw)) +
          datasetNorm (olsObservationReferencePoint n)))

/-- Universal scalar rate selected from `eps` for the two exponential terms
with exponents `1/128` and `eps^2/(8 * 36007^2)`. -/
noncomputable def olsObservationTailRate (eps : ℝ) : ℝ :=
  min (1 / 128 : ℝ) (eps ^ 2 / (8 * (36007 : ℝ) ^ 2))

/-- The scalar envelope obtained by adding the good-set probability bound and
the Gaussian term at threshold `eps / 2`, after substituting
`LK = 36007 / sqrt N`. -/
noncomputable def olsObservationScalarTailBound (eps : ℝ) (n : ℕ) : ℝ :=
  olsObservationGoodSetBadMass n +
    2 * Real.exp (-(((eps / 2) ^ 2) /
      (2 * (36007 / Real.sqrt (n + 3 : ℝ)) ^ 2)))

/-- The actual observation good-set bad mass is bounded by the transported
Gaussian tail. The ENNReal-to-real step uses finiteness of the probability
measure on the complement. -/
theorem olsObservationGoodSetBadMass_le {n : ℕ} (hN : 192 ≤ n + 3) :
    olsObservationGoodSetBadMass n ≤
      4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128)) := by
  let μ := gaussianObservationSampleLaw (n + 3)
  let K := olsObservationGoodSet n
  have hprob : IsProbabilityMeasure μ := gaussianObservationSampleLaw_isProbability (n + 3)
  have hfiniteMeasure : IsFiniteMeasure μ := ⟨by
    rw [hprob.measure_univ]
    exact ENNReal.one_lt_top
  ⟩
  have hfinite : μ Kᶜ ≠ ∞ := @measure_ne_top _ _ μ hfiniteMeasure Kᶜ
  have htail : μ Kᶜ ≤ ENNReal.ofReal
      (4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128))) := by
    simpa only [μ, K, Nat.cast_add, Nat.cast_ofNat, neg_div] using
      (measure_compl_olsObservationGoodSet_le (n := n) hN)
  change (μ Kᶜ).toReal ≤ _
  have htoReal := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 htail
  have hnonneg : 0 ≤ 4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128)) := by
    positivity
  rw [ENNReal.toReal_ofReal hnonneg] at htoReal
  exact htoReal

private theorem olsObservationGoodSetPenalty_bracket_le (n : ℕ) :
    Real.sqrt 12 +
      |olsObservationTestError (olsObservationReferencePoint n)| +
      (36007 / Real.sqrt (n + 3 : ℝ)) *
        (Real.sqrt ((n + 3 : ℝ) *
          (∫ z : Observation 1 1, observationNormSq z ∂gaussianObservationLaw)) +
          datasetNorm (olsObservationReferencePoint n)) ≤
      Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1) := by
  have hNpos : 0 < (n + 3 : ℝ) := by positivity
  have hsqrtN : 0 < Real.sqrt (n + 3 : ℝ) := Real.sqrt_pos.2 hNpos
  have hmoment :
      (∫ z : Observation 1 1, observationNormSq z ∂gaussianObservationLaw) = 2 :=
    gaussianObservationLaw_M2
  have hrefNorm := olsObservationReferencePoint_norm n
  have hrefError := olsObservationReferencePoint_testError_abs_lt_one n
  have hscale :
      (36007 / Real.sqrt (n + 3 : ℝ)) *
          (Real.sqrt ((n + 3 : ℝ) * 2) + Real.sqrt (n + 3 : ℝ)) =
        36007 * (Real.sqrt 2 + 1) := by
    rw [Real.sqrt_mul (le_of_lt hNpos)]
    field_simp [hsqrtN.ne']
  rw [hmoment, hrefNorm]
  calc
    _ = Real.sqrt 12 +
        |olsObservationTestError (olsObservationReferencePoint n)| +
        36007 * (Real.sqrt 2 + 1) := by rw [hscale]
    _ ≤ Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1) := by
      exact add_le_add_left (add_le_add_right hrefError.le _) _

/-- Actual OLS good-set penalty is bounded by the explicit exponential
envelope with the source constants. -/
theorem olsObservationGoodSetPenalty_le {n : ℕ} (hN : 192 ≤ n + 3) :
    olsObservationGoodSetPenalty n ≤
      Real.sqrt (4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128))) *
        (Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1)) := by
  have hp := olsObservationGoodSetBadMass_le hN
  have hbracket := olsObservationGoodSetPenalty_bracket_le n
  have hconstant : 0 ≤ Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1) := by
    positivity
  unfold olsObservationGoodSetPenalty
  calc
    _ ≤ Real.sqrt (olsObservationGoodSetBadMass n) *
          (Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1)) :=
        mul_le_mul_of_nonneg_left hbracket (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (4 * (n + 3 : ℝ) *
          Real.exp (-((n + 3 : ℝ) / 128))) *
          (Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1)) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hp) hconstant

private theorem olsObservationGoodSetPenaltyEnvelope_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt (4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128))) *
          (Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1)))
      atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n + 3 : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right atTop (3 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hdecay0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (1 : ℝ) (1 / 128 : ℝ) (by norm_num)
  have hdecay := hdecay0.comp hN
  have hdecay' : Tendsto
      (fun n : ℕ => (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128)))
      atTop (𝓝 0) := by
    convert hdecay using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_one]
    congr 2
    ring
  have hrad : Tendsto
      (fun n : ℕ => 4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128)))
      atTop (𝓝 0) := by
    simpa [mul_assoc] using tendsto_const_nhds.mul hdecay'
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt
        (4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hrad)
  simpa using hsqrt.mul_const (Real.sqrt 12 + 1 + 36007 * (Real.sqrt 2 + 1))

theorem olsObservationGoodSetPenalty_nonneg (n : ℕ) :
    0 ≤ olsObservationGoodSetPenalty n := by
  have hmass : 0 ≤ olsObservationGoodSetBadMass n := MeasureTheory.measureReal_nonneg
  unfold olsObservationGoodSetPenalty
  apply mul_nonneg (Real.sqrt_nonneg _)
  have hN : 0 ≤ (n + 3 : ℝ) := by positivity
  have hM₂ : 0 ≤
      ∫ z : Observation 1 1, observationNormSq z ∂gaussianObservationLaw := by
    rw [gaussianObservationLaw_M2]
    norm_num
  have hnorm : 0 ≤ datasetNorm (olsObservationReferencePoint n) := by
    rw [olsObservationReferencePoint_norm]
    exact Real.sqrt_nonneg _
  dsimp only [olsObservationGoodSetBadMass] at hmass
  positivity

/-- The actual penalty tends to zero, by its explicit exponential envelope. -/
theorem tendsto_olsObservationGoodSetPenalty_atTop :
    Tendsto olsObservationGoodSetPenalty atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall olsObservationGoodSetPenalty_nonneg)
    ?_ olsObservationGoodSetPenaltyEnvelope_tendsto_zero
  filter_upwards [eventually_ge_atTop (189 : ℕ)] with n hn
  exact olsObservationGoodSetPenalty_le (by omega)

/-- For every positive `eps`, the actual good-set penalty is eventually less
than `eps / 4`. This follows from the proved penalty decay. -/
theorem olsObservationGoodSetPenalty_eventually_lt (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, olsObservationGoodSetPenalty n < eps / 4 := by
  have hmem : Set.Iio (eps / 4) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by linarith)
  exact tendsto_olsObservationGoodSetPenalty_atTop.eventually hmem

theorem olsObservationTailRate_pos {eps : ℝ} (heps : 0 < eps) :
    0 < olsObservationTailRate eps := by
  exact lt_min (by norm_num) (by positivity)

private theorem olsObservationGaussianTail_exponent (eps : ℝ) (n : ℕ) :
    -(((eps / 2) ^ 2) /
      (2 * (36007 / Real.sqrt (n + 3 : ℝ)) ^ 2)) =
      -(((n + 3 : ℝ) * eps ^ 2) / (8 * (36007 : ℝ) ^ 2)) := by
  have hNpos : 0 < (n + 3 : ℝ) := by positivity
  have hroot : Real.sqrt (n + 3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
  have hsq : (36007 / Real.sqrt (n + 3 : ℝ)) ^ 2 =
      (36007 : ℝ) ^ 2 / (n + 3 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hNpos)]
  rw [hsq]
  field_simp [hNpos.ne', hroot, (by norm_num : (8 : ℝ) ≠ 0),
    (by norm_num : (36007 : ℝ) ≠ 0)]
  ring

/-- The scalar sum `p + 2 exp(-t²/(2 LK²))`, at `t = eps/2` and the actual
`LK`, has an exponential envelope. This is the scalar right-hand-side bound;
it does not assert an OLS event-probability theorem. -/
theorem olsObservationScalarTailBound_le {eps : ℝ} {n : ℕ}
    (hN : 192 ≤ n + 3) :
    olsObservationScalarTailBound eps n ≤
      6 * (n + 3 : ℝ) *
        Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := by
  let N : ℝ := (n + 3 : ℝ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNge1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ n + 3 by omega)
  have hp := olsObservationGoodSetBadMass_le hN
  have hfirst : Real.exp (-((n + 3 : ℝ) / 128)) ≤
      Real.exp (-(olsObservationTailRate eps * N)) := by
    have hrate : olsObservationTailRate eps * N ≤ (1 / 128 : ℝ) * N :=
      mul_le_mul_of_nonneg_right
        (min_le_left _ _) (le_of_lt hNpos)
    apply Real.exp_le_exp.mpr
    calc
      -((n + 3 : ℝ) / 128) = -((1 / 128 : ℝ) * N) := by dsimp [N]; ring
      _ ≤ -(olsObservationTailRate eps * N) := neg_le_neg hrate
  have hsecond : Real.exp (-(((n + 3 : ℝ) * eps ^ 2) /
        (8 * (36007 : ℝ) ^ 2))) ≤
      Real.exp (-(olsObservationTailRate eps * N)) := by
    have hrate : olsObservationTailRate eps * N ≤
        (eps ^ 2 / (8 * (36007 : ℝ) ^ 2)) * N :=
      mul_le_mul_of_nonneg_right
        (min_le_right _ _) (le_of_lt hNpos)
    apply Real.exp_le_exp.mpr
    calc
      -(((n + 3 : ℝ) * eps ^ 2) / (8 * (36007 : ℝ) ^ 2)) =
          -((eps ^ 2 / (8 * (36007 : ℝ) ^ 2)) * N) := by dsimp [N]; ring
      _ ≤ -(olsObservationTailRate eps * N) := neg_le_neg hrate
  have hgauss := olsObservationGaussianTail_exponent eps n
  have hexpNonneg : 0 ≤ Real.exp (-(olsObservationTailRate eps * N)) :=
    (Real.exp_pos _).le
  have hpExp : olsObservationGoodSetBadMass n ≤
      4 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) := by
    calc
      _ ≤ 4 * (n + 3 : ℝ) * Real.exp (-((n + 3 : ℝ) / 128)) := hp
      _ ≤ 4 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
  unfold olsObservationScalarTailBound
  rw [hgauss]
  calc
    _ ≤ 4 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) +
        2 * Real.exp (-(olsObservationTailRate eps * N)) := by
      exact add_le_add hpExp (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ ≤ 4 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) +
        2 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) := by
      have hcoef : (2 : ℝ) ≤ 2 * N := by
        calc
          2 = 2 * 1 := by norm_num
          _ ≤ 2 * N := mul_le_mul_of_nonneg_left hNge1 (by norm_num)
      have hscaled : 2 * Real.exp (-(olsObservationTailRate eps * N)) ≤
          2 * N * Real.exp (-(olsObservationTailRate eps * N)) :=
        mul_le_mul_of_nonneg_right hcoef hexpNonneg
      calc
        _ = 2 * Real.exp (-(olsObservationTailRate eps * N)) +
            4 * (n + 3 : ℝ) * Real.exp (-(olsObservationTailRate eps * N)) := by ring
        _ = 2 * Real.exp (-(olsObservationTailRate eps * N)) +
            4 * N * Real.exp (-(olsObservationTailRate eps * N)) := by rfl
        _ ≤ 2 * N * Real.exp (-(olsObservationTailRate eps * N)) +
            4 * N * Real.exp (-(olsObservationTailRate eps * N)) :=
          add_le_add_left hscaled
            (4 * N * Real.exp (-(olsObservationTailRate eps * N)))
        _ = _ := by dsimp [N]; ring
    _ = 6 * (n + 3 : ℝ) *
        Real.exp (-(olsObservationTailRate eps * (n + 3 : ℝ))) := by
      dsimp [N]
      ring

#print axioms olsObservationGoodSetBadMass_le
#print axioms olsObservationGoodSetPenalty_le
#print axioms olsObservationGoodSetPenalty_nonneg
#print axioms tendsto_olsObservationGoodSetPenalty_atTop
#print axioms olsObservationGoodSetPenalty_eventually_lt
#print axioms olsObservationTailRate_pos
#print axioms olsObservationScalarTailBound_le

end LOOConcentration
