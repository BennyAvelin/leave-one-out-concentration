import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import LOOConcentration.Examples.OlsObservationGoodSet
import LOOConcentration.Examples.OlsRiskMoments

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open Topology
open scoped ENNReal NNReal

private theorem olsObservationSampleLaw_eq_olsPair_map (N : ℕ) :
    gaussianObservationSampleLaw N =
      Measure.map (gaussianObservationSampleMap N) (olsPairGaussianLaw N) := by
  rw [← gaussianObservationSampleLaw_eq_map N]
  congr 1

private theorem olsObservationTestError_pairMap {n : ℕ}
    (G : Fin (n + 3) → ℝ × ℝ) :
    olsObservationTestError (gaussianObservationSampleMap (n + 3) G) =
      olsTestError (n := n + 1) G := by
  change olsTestError
      (olsObservationToPairSample (olsPairToObservationSample G)) = olsTestError G
  rw [olsObservationToPairSample_pairToObservationSample]

private theorem integrable_olsPairTestError {n : ℕ} (hn : 3 ≤ n) :
    Integrable (olsTestError (n := n + 1) :
      (Fin (n + 3) → ℝ × ℝ) → ℝ) (olsPairGaussianLaw (n + 3)) := by
  have hRisk := integrable_olsTestRisk_gaussian (r := n + 3) (by omega : 3 < n + 3)
  have hValidation := integrable_olsValidationError_gaussian
    (n := n + 1) (by omega : 3 < (n + 1) + 1)
  have hsub := hRisk.sub hValidation
  change Integrable
    (fun G : Fin (n + 3) → ℝ × ℝ => olsTestRisk G - olsValidationError G)
    (olsPairGaussianLaw (n + 3))
  exact hsub

private theorem integrable_olsPairTestError_sq {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun G : Fin (n + 3) → ℝ × ℝ =>
      (olsTestError (n := n + 1) G) ^ 2) (olsPairGaussianLaw (n + 3)) := by
  exact integrable_olsTestError_sq_gaussian
    (n := n + 1) (by omega : 4 ≤ n + 1)

theorem integrable_olsObservationTestError_gaussian {n : ℕ} (hn : 3 ≤ n) :
    Integrable (olsObservationTestError :
      Dataset (Observation 1 1) (n + 3) → ℝ)
      (gaussianObservationSampleLaw (n + 3)) := by
  have hpair := integrable_olsPairTestError hn
  have hcomp : Integrable
      (fun G : Fin (n + 3) → ℝ × ℝ =>
        olsObservationTestError (gaussianObservationSampleMap (n + 3) G))
      (olsPairGaussianLaw (n + 3)) := by
    have heq : (fun G : Fin (n + 3) → ℝ × ℝ =>
        olsObservationTestError (gaussianObservationSampleMap (n + 3) G)) =
        fun G => olsTestError (n := n + 1) G := by
      funext G
      exact olsObservationTestError_pairMap G
    rw [heq]
    exact hpair
  have hmap := (integrable_map_measure
      (f := gaussianObservationSampleMap (n + 3))
      (g := olsObservationTestError)
      (measurable_olsObservationTestError (n := n)).aestronglyMeasurable
      (gaussianObservationSampleMap_measurable (n + 3)).aemeasurable).2 hcomp
  rw [olsObservationSampleLaw_eq_olsPair_map]
  exact hmap

theorem integrable_olsObservationTestError_sq_gaussian {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun D : Dataset (Observation 1 1) (n + 3) =>
      (olsObservationTestError D) ^ 2) (gaussianObservationSampleLaw (n + 3)) := by
  have hpair := integrable_olsPairTestError_sq hn
  have hcomp : Integrable
      (fun G : Fin (n + 3) → ℝ × ℝ =>
        (olsObservationTestError (gaussianObservationSampleMap (n + 3) G)) ^ 2)
      (olsPairGaussianLaw (n + 3)) := by
    have heq : (fun G : Fin (n + 3) → ℝ × ℝ =>
        (olsObservationTestError (gaussianObservationSampleMap (n + 3) G)) ^ 2) =
        fun G => (olsTestError (n := n + 1) G) ^ 2 := by
      funext G
      rw [olsObservationTestError_pairMap]
    rw [heq]
    exact hpair
  have hmap := (integrable_map_measure
      (f := gaussianObservationSampleMap (n + 3))
      (g := fun D : Dataset (Observation 1 1) (n + 3) =>
        (olsObservationTestError D) ^ 2)
      ((measurable_olsObservationTestError (n := n)).pow_const 2).aestronglyMeasurable
      (gaussianObservationSampleMap_measurable (n + 3)).aemeasurable).2 hcomp
  rw [olsObservationSampleLaw_eq_olsPair_map]
  exact hmap

theorem integral_olsObservationTestError_gaussian_eq_pair {n : ℕ} (hn : 3 ≤ n) :
    (∫ D : Dataset (Observation 1 1) (n + 3),
      olsObservationTestError D ∂gaussianObservationSampleLaw (n + 3)) =
      ∫ G : Fin (n + 3) → ℝ × ℝ,
        olsTestError (n := n + 1) G ∂olsPairGaussianLaw (n + 3) := by
  have hInt := integrable_olsObservationTestError_gaussian hn
  have hfm : AEStronglyMeasurable
      (olsObservationTestError : Dataset (Observation 1 1) (n + 3) → ℝ)
      (Measure.map (gaussianObservationSampleMap (n + 3))
        (olsPairGaussianLaw (n + 3))) := by
    rw [← olsObservationSampleLaw_eq_olsPair_map]
    exact hInt.aestronglyMeasurable
  calc
    _ = ∫ D : Dataset (Observation 1 1) (n + 3),
        olsObservationTestError D ∂Measure.map (gaussianObservationSampleMap (n + 3))
          (olsPairGaussianLaw (n + 3)) := by
      rw [olsObservationSampleLaw_eq_olsPair_map]
    _ = ∫ G : Fin (n + 3) → ℝ × ℝ,
        olsObservationTestError (gaussianObservationSampleMap (n + 3) G)
          ∂olsPairGaussianLaw (n + 3) :=
      integral_map (gaussianObservationSampleMap_measurable (n + 3)).aemeasurable hfm
    _ = ∫ G : Fin (n + 3) → ℝ × ℝ,
        olsTestError (n := n + 1) G ∂olsPairGaussianLaw (n + 3) := by
      apply integral_congr_ae
      exact ae_of_all _ olsObservationTestError_pairMap

theorem integral_olsObservationTestError_sq_eq_pair {n : ℕ} (hn : 3 ≤ n) :
    (∫ D : Dataset (Observation 1 1) (n + 3),
      (olsObservationTestError D) ^ 2 ∂gaussianObservationSampleLaw (n + 3)) =
      ∫ G : Fin (n + 3) → ℝ × ℝ,
        (olsTestError (n := n + 1) G) ^ 2 ∂olsPairGaussianLaw (n + 3) := by
  have hInt := integrable_olsObservationTestError_sq_gaussian hn
  have hfm : AEStronglyMeasurable
      (fun D : Dataset (Observation 1 1) (n + 3) =>
        (olsObservationTestError D) ^ 2)
      (Measure.map (gaussianObservationSampleMap (n + 3))
        (olsPairGaussianLaw (n + 3))) := by
    rw [← olsObservationSampleLaw_eq_olsPair_map]
    exact hInt.aestronglyMeasurable
  calc
    _ = ∫ D : Dataset (Observation 1 1) (n + 3),
        (olsObservationTestError D) ^ 2
        ∂Measure.map (gaussianObservationSampleMap (n + 3))
          (olsPairGaussianLaw (n + 3)) := by
      rw [olsObservationSampleLaw_eq_olsPair_map]
    _ = ∫ G : Fin (n + 3) → ℝ × ℝ,
        (olsObservationTestError (gaussianObservationSampleMap (n + 3) G)) ^ 2
          ∂olsPairGaussianLaw (n + 3) :=
      integral_map (gaussianObservationSampleMap_measurable (n + 3)).aemeasurable hfm
    _ = ∫ G : Fin (n + 3) → ℝ × ℝ,
        (olsTestError (n := n + 1) G) ^ 2 ∂olsPairGaussianLaw (n + 3) := by
      apply integral_congr_ae
      exact ae_of_all _ fun G => congrArg (fun x : ℝ => x ^ 2)
        (olsObservationTestError_pairMap G)

theorem integral_olsObservationTestError_sq_gaussian_le_twelve {n : ℕ}
    (hn : 3 ≤ n) :
    (∫ D : Dataset (Observation 1 1) (n + 3),
      (olsObservationTestError D) ^ 2 ∂gaussianObservationSampleLaw (n + 3)) ≤ 12 := by
  rw [integral_olsObservationTestError_sq_eq_pair hn]
  exact integral_olsTestError_sq_gaussian_le_twelve
    (n := n + 1) (by omega : 4 ≤ n + 1)

theorem olsObservationTestError_eLpNorm_two_le_sqrt_twelve {n : ℕ}
    (hn : 3 ≤ n) :
    eLpNorm (olsObservationTestError : Dataset (Observation 1 1) (n + 3) → ℝ)
      2 (gaussianObservationSampleLaw (n + 3)) ≤ ENNReal.ofReal (Real.sqrt 12) := by
  have hsq := integrable_olsObservationTestError_sq_gaussian hn
  have hmeas := measurable_olsObservationTestError (n := n)
  have hmem : MemLp (olsObservationTestError :
      Dataset (Observation 1 1) (n + 3) → ℝ) 2
      (gaussianObservationSampleLaw (n + 3)) :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hnorm : (∫ D : Dataset (Observation 1 1) (n + 3),
      ‖olsObservationTestError D‖ ^ 2 ∂gaussianObservationSampleLaw (n + 3)) =
      ∫ D : Dataset (Observation 1 1) (n + 3),
        (olsObservationTestError D) ^ 2 ∂gaussianObservationSampleLaw (n + 3) := by
    apply integral_congr_ae
    exact ae_of_all _ fun D => by
      simp only [Real.norm_eq_abs, sq_abs]
  have hnormR : (∫ D : Dataset (Observation 1 1) (n + 3),
      ‖olsObservationTestError D‖ ^ (2 : ℝ)
        ∂gaussianObservationSampleLaw (n + 3)) =
      ∫ D : Dataset (Observation 1 1) (n + 3),
        (olsObservationTestError D) ^ 2 ∂gaussianObservationSampleLaw (n + 3) := by
    calc
      _ = ∫ D : Dataset (Observation 1 1) (n + 3),
          ‖olsObservationTestError D‖ ^ 2
          ∂gaussianObservationSampleLaw (n + 3) := by
        apply integral_congr_ae
        exact ae_of_all _ fun D => Real.rpow_natCast _ _
      _ = _ := hnorm
  simp only [ENNReal.toReal_ofNat]
  rw [hnormR]
  have hbound := integral_olsObservationTestError_sq_gaussian_le_twelve hn
  have hboundRoot : Real.sqrt
      (∫ D : Dataset (Observation 1 1) (n + 3),
        (olsObservationTestError D) ^ 2 ∂gaussianObservationSampleLaw (n + 3)) ≤
      Real.sqrt 12 := Real.sqrt_le_sqrt hbound
  simpa [Real.sqrt_eq_rpow] using hboundRoot

theorem abs_integral_olsObservationTestError_gaussian_le_bias {n : ℕ}
    (hn : 3 ≤ n) :
    |∫ D : Dataset (Observation 1 1) (n + 3),
      olsObservationTestError D ∂gaussianObservationSampleLaw (n + 3)| ≤
      Real.sqrt (1 / ((n + 3 : ℕ) : ℝ) +
        (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) +
      Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3)) := by
  rw [integral_olsObservationTestError_gaussian_eq_pair hn]
  have h := abs_integral_olsTestError_gaussian_le_bias
    (n := n + 1) (by omega : 3 < (n + 1) + 1)
  simpa [Nat.add_assoc] using h

theorem tendsto_olsObservationBiasEnvelope_zero :
    Tendsto (fun n : ℕ =>
      Real.sqrt (1 / ((n + 3 : ℕ) : ℝ) +
        (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) +
      Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3)))
      atTop (𝓝 0) := by
  let envelope : ℕ → ℝ := fun n =>
    Real.sqrt (1 / ((n + 3 : ℕ) : ℝ) +
      (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) +
    Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
      (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3))
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun n : ℕ => (4 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).mul hinv
  have hroot : Tendsto (fun n : ℕ => Real.sqrt ((4 : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    rw [show (fun n : ℕ => Real.sqrt ((4 : ℝ) / (n : ℝ))) =
        (fun x : ℝ => Real.sqrt x) ∘ (fun n : ℕ => (4 : ℝ) / (n : ℝ)) by
      funext n
      rfl]
    rw [← Real.sqrt_zero]
    exact Real.continuous_sqrt.continuousAt.tendsto.comp harg
  have hmajor : Tendsto (fun n : ℕ => 2 * Real.sqrt ((4 : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (𝓝 2)).mul hroot
  have hle : ∀ᶠ n : ℕ in atTop,
      envelope n ≤ 2 * Real.sqrt ((4 : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    let x : ℝ := n
    have hx : 3 ≤ x := by
      dsimp [x]
      exact_mod_cast hn
    have hxpos : 0 < x := by linarith
    have hxsubpos : 0 < x - 1 := by linarith
    have hfullIndex : ((n + 3 : ℕ) : ℝ) = x + 3 := by
      dsimp [x]
      push_cast
      ring
    have hprevIndex : ((n + 2 : ℕ) : ℝ) = x + 2 := by
      dsimp [x]
      push_cast
      ring
    have hfull :
        1 / ((n + 3 : ℕ) : ℝ) +
          (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3) ≤ 4 / x := by
      rw [hfullIndex]
      have hrecip : 1 / (x + 3) ≤ 1 / x :=
        one_div_le_one_div_of_le hxpos (by linarith)
      have hnum : 1 + 1 / (x + 3) ≤ 2 := by
        have hleOne : 1 / (x + 3) ≤ 1 := by
          rw [div_le_iff₀ (by linarith : 0 < x + 3)]
          linarith
        linarith
      have hquot : (1 + 1 / (x + 3)) / x ≤ 2 / x :=
        div_le_div_of_nonneg_right hnum (le_of_lt hxpos)
      calc
        _ = 1 / (x + 3) + (1 + 1 / (x + 3)) / x := by ring_nf
        _ ≤ 1 / x + 2 / x := add_le_add hrecip hquot
        _ ≤ 4 / x := by
          calc
            1 / x + 2 / x = 3 / x := by ring
            _ ≤ 4 / x := div_le_div_of_nonneg_right (by norm_num) hxpos.le
    have hprev :
        1 / ((n + 2 : ℕ) : ℝ) +
          (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3) ≤ 4 / x := by
      rw [hprevIndex]
      have hrecip : 1 / (x + 2) ≤ 1 / x :=
        one_div_le_one_div_of_le hxpos (by linarith)
      have hnum : 1 + 1 / (x + 2) ≤ 2 := by
        have hleOne : 1 / (x + 2) ≤ 1 := by
          rw [div_le_iff₀ (by linarith : 0 < x + 2)]
          linarith
        linarith
      have hquot : (1 + 1 / (x + 2)) / (x - 1) ≤ 3 / x := by
        rw [div_le_div_iff₀ hxsubpos hxpos]
        calc
          (1 + 1 / (x + 2)) * x ≤ 2 * x := by
            exact mul_le_mul_of_nonneg_right hnum (le_of_lt hxpos)
          _ ≤ 3 * (x - 1) := by nlinarith
      calc
        _ = 1 / (x + 2) + (1 + 1 / (x + 2)) / (x - 1) := by ring_nf
        _ ≤ 1 / x + 3 / x := add_le_add hrecip hquot
        _ = 4 / x := by ring
    have hfullRoot : Real.sqrt
        (1 / ((n + 3 : ℕ) : ℝ) +
          (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) ≤
        Real.sqrt (4 / x) := Real.sqrt_le_sqrt hfull
    have hprevRoot : Real.sqrt
        (1 / ((n + 2 : ℕ) : ℝ) +
          (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3)) ≤
        Real.sqrt (4 / x) := Real.sqrt_le_sqrt hprev
    change _ ≤ _
    dsimp [envelope]
    nlinarith [hfullRoot, hprevRoot]
  have hnonneg : ∀ n : ℕ, 0 ≤ envelope n := by
    intro n
    dsimp [envelope]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change Tendsto envelope atTop (𝓝 0)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hle hmajor

theorem tendsto_abs_integral_olsObservationTestError_gaussian_zero :
    Tendsto (fun n : ℕ =>
      |∫ D : Dataset (Observation 1 1) (n + 3),
        olsObservationTestError D ∂gaussianObservationSampleLaw (n + 3)|)
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |∫ D : Dataset (Observation 1 1) (n + 3),
        olsObservationTestError D ∂gaussianObservationSampleLaw (n + 3)| ≤
      Real.sqrt (1 / ((n + 3 : ℕ) : ℝ) +
        (1 + 1 / ((n + 3 : ℕ) : ℝ)) / (((n + 3 : ℕ) : ℝ) - 3)) +
      Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) - 3)) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact abs_integral_olsObservationTestError_gaussian_le_bias hn
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    hbound tendsto_olsObservationBiasEnvelope_zero

#print axioms integrable_olsObservationTestError_gaussian
#print axioms integrable_olsObservationTestError_sq_gaussian
#print axioms integral_olsObservationTestError_gaussian_eq_pair
#print axioms integral_olsObservationTestError_sq_eq_pair
#print axioms integral_olsObservationTestError_sq_gaussian_le_twelve
#print axioms olsObservationTestError_eLpNorm_two_le_sqrt_twelve
#print axioms abs_integral_olsObservationTestError_gaussian_le_bias
#print axioms tendsto_olsObservationBiasEnvelope_zero
#print axioms tendsto_abs_integral_olsObservationTestError_gaussian_zero

end LOOConcentration
