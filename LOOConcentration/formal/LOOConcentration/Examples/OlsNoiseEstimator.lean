import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Examples.OlsGoodSetErrorLipschitz

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

private def olsNoiseFinOne : Fin 1 := ⟨0, by omega⟩

/-- Encode a real covariate/noise pair in the frozen one-coordinate carrier. -/
def olsNoiseObservation (z : ℝ × ℝ) : Observation 1 1 :=
  (fun _ : Fin 1 => z.1, fun _ : Fin 1 => z.2)

/-- The coordinatewise encoding of a finite noise-pair sample. -/
def olsNoiseObservations {N : ℕ} (G : Fin N → ℝ × ℝ) :
    Dataset (Observation 1 1) N :=
  fun i => olsNoiseObservation (G i)

/-- Read the two scalar coordinates from the frozen one-coordinate carrier. -/
def olsNoiseObservationCoordinates (z : Observation 1 1) : ℝ × ℝ :=
  (z.1 olsNoiseFinOne, z.2 olsNoiseFinOne)

@[simp]
theorem olsNoiseObservationCoordinates_encode (z : ℝ × ℝ) :
    olsNoiseObservationCoordinates (olsNoiseObservation z) = z := by
  ext <;> rfl

@[simp]
theorem olsNoiseObservations_deleteAt {N : ℕ} (G : Fin (N + 1) → ℝ × ℝ)
    (i : Fin (N + 1)) :
    deleteAt (olsNoiseObservations G) i = olsNoiseObservations (deleteAt G i) := by
  rfl

/-- For fixed training data, the literal noise predictor is continuous in the
one-coordinate test feature. -/
theorem continuous_olsNoisePredictor_feature {r : ℕ} (G : Fin r → ℝ × ℝ) :
    Continuous (fun x : Features 1 => fun i : Fin 1 =>
      olsNoisePredictor G (x i)) := by
  apply continuous_pi_iff.2
  intro i
  change Continuous (fun x : Features 1 =>
    olsEBar G + olsNoiseSlope G * (x i - olsXBar G))
  exact continuous_const.add (continuous_const.mul
    ((continuous_apply i).sub continuous_const))

/-- The actual source-case OLS noise estimator. The `r=0` branch is the
unused one-observation typing case; every successor branch uses the totalized
OLS noise predictor on the literal `s+2` training observations. -/
noncomputable def olsNoiseEstimator : (r : ℕ) → Estimator 1 1 (r + 1)
  | 0 => fun _ =>
      ⟨fun _ : Features 1 => fun _ : Fin 1 => (0 : ℝ), continuous_const⟩
  | s + 1 => fun D =>
      ⟨fun x i => olsNoisePredictor (fun j =>
        olsNoiseObservationCoordinates (D j)) (x i), by
        apply continuous_pi_iff.2
        intro i
        change Continuous (fun x : Features 1 =>
          olsEBar (fun j => olsNoiseObservationCoordinates (D j)) +
          olsNoiseSlope (fun j => olsNoiseObservationCoordinates (D j)) *
              (x i - olsXBar (fun j => olsNoiseObservationCoordinates (D j))))
        exact continuous_const.add (continuous_const.mul
          ((continuous_apply i).sub continuous_const))⟩

@[simp]
theorem olsNoiseEstimator_zero_apply (D : Dataset (Observation 1 1) 1)
    (x : Features 1) (i : Fin 1) :
    olsNoiseEstimator 0 D x i = 0 := rfl

@[simp]
theorem olsNoiseEstimator_succ_apply {s : ℕ}
    (D : Dataset (Observation 1 1) (s + 2)) (x : Features 1) (i : Fin 1) :
    olsNoiseEstimator (s + 1) D x i =
    olsNoisePredictor (fun j => olsNoiseObservationCoordinates (D j)) (x i) := rfl

theorem olsNoiseEstimator_encodedTraining_apply {r : ℕ}
    (G : Fin (r + 2) → ℝ × ℝ) (x : Features 1) (i : Fin 1) :
    olsNoiseEstimator (r + 1) (olsNoiseObservations G) x i =
      olsNoisePredictor G (x i) := by
  rw [olsNoiseEstimator_succ_apply]
  have hdecode :
      (fun j : Fin (r + 2) =>
        olsNoiseObservationCoordinates (olsNoiseObservations G j)) = G := by
    funext j
    simp [olsNoiseObservations]
  rw [hdecode]

/-- Both branches of the source estimator have continuous test predictors. -/
theorem continuous_olsNoiseEstimator {r : ℕ}
    (D : Dataset (Observation 1 1) (r + 1)) :
    Continuous (olsNoiseEstimator r D) := by
  cases r with
  | zero =>
      change Continuous (fun _ : Features 1 => fun _ : Fin 1 => (0 : ℝ))
      exact continuous_const
  | succ s =>
      change Continuous (fun x : Features 1 => fun i : Fin 1 =>
        olsNoisePredictor (fun j => olsNoiseObservationCoordinates (D j)) (x i))
      exact continuous_olsNoisePredictor_feature
        (fun j => olsNoiseObservationCoordinates (D j))

/-- The absolute scalar loss, represented on the frozen one-coordinate response
carrier. -/
def olsNoiseAbsoluteLoss (u v : Responses 1) : ℝ :=
  |v olsNoiseFinOne - u olsNoiseFinOne|

/-- The actual fitted loss of the noise estimator at one frozen-carrier test
observation. -/
noncomputable def olsNoiseEstimatorTestLoss {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (z : Observation 1 1) : ℝ :=
  fittedLoss (olsNoiseEstimator (n + 1)) olsNoiseAbsoluteLoss
    (olsNoiseObservations G) z

/-- Pointwise, the frozen `fittedLoss` is exactly the literal scalar OLS risk
loss after encoding a pair as a one-coordinate observation. -/
theorem olsNoiseEstimatorTestLoss_formula {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (z : Observation 1 1) :
    olsNoiseEstimatorTestLoss G z =
      |z.2 olsNoiseFinOne - olsNoisePredictor G (z.1 olsNoiseFinOne)| := by
  change |z.2 olsNoiseFinOne -
      olsNoiseEstimator (n + 1) (olsNoiseObservations G) z.1 olsNoiseFinOne| = _
  rw [olsNoiseEstimator_encodedTraining_apply]

theorem olsNoiseEstimatorTestLoss_encoded {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (z : ℝ × ℝ) :
    olsNoiseEstimatorTestLoss G (olsNoiseObservation z) = olsRiskLoss G z := by
  rw [olsNoiseEstimatorTestLoss_formula]
  simp [olsRiskLoss, olsNoiseObservation, olsNoiseFinOne]

/-- The finite empirical bridge uses the same ordered `deleteAt` coordinates
as the frozen leave-one-out estimate. -/
theorem looEstimate_olsNoiseEstimator_eq_olsValidationError {n : ℕ}
    (G : Fin (n + 3) → ℝ × ℝ) :
    looEstimate (n := n + 1) (olsNoiseEstimator (n + 1))
        olsNoiseAbsoluteLoss (olsNoiseObservations G) =
      olsValidationError (n := n + 1) G := by
  unfold looEstimate olsValidationError
  rfl

/-- The genuine pair-law pushforward to the frozen one-coordinate carrier.
This definition does not identify it with the pending Bunny3 Gaussian
observation-law transport. -/
noncomputable abbrev olsNoiseObservationTestLaw : Measure (Observation 1 1) :=
  olsTestLaw.map olsNoiseObservation

theorem measurable_olsNoiseObservation : Measurable olsNoiseObservation := by
  unfold olsNoiseObservation
  fun_prop

theorem measurable_olsNoiseEstimatorTestLoss {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) : Measurable (olsNoiseEstimatorTestLoss G) := by
  have hpred : Continuous (fun x : Features 1 =>
      olsNoisePredictor G (x olsNoiseFinOne)) := by
    exact (continuous_apply olsNoiseFinOne).comp
      (continuous_olsNoisePredictor_feature G)
  have hx : Measurable (fun z : Observation 1 1 =>
      olsNoisePredictor G (z.1 olsNoiseFinOne)) :=
    (hpred.comp continuous_fst).measurable
  have hy : Measurable (fun z : Observation 1 1 => z.2 olsNoiseFinOne) :=
    ((continuous_apply olsNoiseFinOne).comp continuous_snd).measurable
  rw [show olsNoiseEstimatorTestLoss G =
      (fun z : Observation 1 1 =>
        |z.2 olsNoiseFinOne - olsNoisePredictor G (z.1 olsNoiseFinOne)|) by
        funext z
        exact olsNoiseEstimatorTestLoss_formula G z]
  exact measurable_abs.comp (hy.sub hx)

theorem integrable_olsNoiseEstimatorTestLoss {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) :
    Integrable (olsNoiseEstimatorTestLoss G) (olsNoiseObservationTestLaw) := by
  have hcomp : Integrable
      (fun z : ℝ × ℝ => olsNoiseEstimatorTestLoss G (olsNoiseObservation z))
      olsTestLaw := by
    convert olsTestRiskLoss_integrable G using 1
    funext z
    exact olsNoiseEstimatorTestLoss_encoded G z
  exact (integrable_map_measure
    (measurable_olsNoiseEstimatorTestLoss G).aestronglyMeasurable
    measurable_olsNoiseObservation.aemeasurable).mpr hcomp

/-- The pointwise fitted-loss and integral-map bridges identify the actual
noise-estimator test risk under its explicitly pushed-forward pair law with
the reviewed Gaussian `olsTestRisk`. -/
theorem integral_olsNoiseEstimatorTestLoss_eq_olsTestRisk {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) :
    (∫ z : Observation 1 1, olsNoiseEstimatorTestLoss G z
      ∂olsNoiseObservationTestLaw) = olsTestRisk G := by
  unfold olsNoiseObservationTestLaw olsTestRisk
  rw [integral_map measurable_olsNoiseObservation.aemeasurable
    (integrable_olsNoiseEstimatorTestLoss G).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with z
  exact olsNoiseEstimatorTestLoss_encoded G z

#print axioms olsNoiseEstimator
#print axioms continuous_olsNoisePredictor_feature
#print axioms continuous_olsNoiseEstimator
#print axioms olsNoiseEstimatorTestLoss_formula
#print axioms looEstimate_olsNoiseEstimator_eq_olsValidationError
#print axioms olsNoiseEstimatorTestLoss_encoded
#print axioms integrable_olsNoiseEstimatorTestLoss
#print axioms integral_olsNoiseEstimatorTestLoss_eq_olsTestRisk

end LOOConcentration
