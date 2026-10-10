import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.OlsAffineTransport

set_option autoImplicit false

open MeasureTheory
open ProbabilityTheory
open scoped NNReal

namespace LOOConcentration

/-!
# Exact response-law transport for the OLS error event

The response risk and validation error use the frozen predictor on its entire
carrier, including its literal singular-design extension. Their error-tail
probability is transported to the independent noise-pair coordinates through
the actual affine sample map. The response/noise error identity is used only
almost everywhere, on the positive full and deleted design locus.
-/

/-- The frozen OLS risk under the actual affine response test-pair law. -/
noncomputable def olsResponseLawRisk {r : ℕ} (α β : ℝ)
    (D : Fin (r + 2) → ℝ × ℝ) : ℝ :=
  ∫ z, |olsPrediction D z.1 - z.2| ∂olsAffineResponseTestLaw α β

/-- The frozen OLS leave-one-out error on the exact `n+3` response sample. -/
noncomputable def olsResponseValidationError {n : ℕ}
    (D : Fin (n + 3) → ℝ × ℝ) : ℝ :=
  (∑ i : Fin (n + 3),
    |olsPrediction (deleteAt D i) (D i).1 - (D i).2|) / (n + 3 : ℝ)

/-- The literal response-coordinate frozen generalization error. -/
noncomputable def olsResponseError {n : ℕ} (α β : ℝ)
    (D : Fin (n + 3) → ℝ × ℝ) : ℝ :=
  olsResponseLawRisk α β D - olsResponseValidationError D

/-- The accepted response law is exactly the response law in the frozen root:
an iid product of the pushforward of two standard Gaussian coordinates. -/
theorem olsAffineResponseLaw_eq_frozenResponseLaw (N : ℕ) (α β : ℝ) :
    Measure.pi (fun _ : Fin N =>
      ((ProbabilityTheory.gaussianReal (0 : ℝ) (1 : ℝ≥0)).prod
        (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : ℝ≥0))).map
          (fun p : ℝ × ℝ => (p.1, α + β * p.1 + p.2))) =
      olsAffineResponseLaw N α β := by
  change Measure.pi (fun _ : Fin N =>
      (standardGaussian.prod standardGaussian).map (olsAffineResponsePair α β)) =
    Measure.pi (fun _ : Fin N => olsAffineResponsePairLaw α β)
  rfl

/-- The independent test law in the source risk is the accepted pushforward
response test law. -/
theorem olsAffineResponseTestLaw_eq_frozenResponseTestLaw (α β : ℝ) :
    ((ProbabilityTheory.gaussianReal (0 : ℝ) (1 : ℝ≥0)).prod
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : ℝ≥0))).map
        (fun p : ℝ × ℝ => (p.1, α + β * p.1 + p.2)) =
      olsAffineResponseTestLaw α β := by
  change (standardGaussian.prod standardGaussian).map
      (olsAffineResponsePair α β) = olsAffineResponseTestLaw α β
  rfl

private theorem measurable_olsPrediction_joint {r : ℕ} :
    Measurable (fun p : (Fin (r + 2) → ℝ × ℝ) × ℝ =>
      olsPrediction p.1 p.2) := by
  unfold olsPrediction
  fun_prop

private theorem measurable_olsResponseLoss_joint {r : ℕ} :
    Measurable (fun p : (Fin (r + 2) → ℝ × ℝ) × (ℝ × ℝ) =>
      |olsPrediction p.1 p.2.1 - p.2.2|) := by
  have hp : Measurable
      (fun p : (Fin (r + 2) → ℝ × ℝ) × (ℝ × ℝ) =>
        olsPrediction p.1 p.2.1) := by
    exact measurable_olsPrediction_joint.comp
      (measurable_fst.prodMk (measurable_snd.fst))
  exact measurable_abs.comp (hp.sub measurable_snd.snd)

/-- Whole-carrier measurability of the response risk. It follows from joint
measurability and the measurable-integral theorem; no pointwise integrability
assumption is needed for this measurability result. -/
theorem measurable_olsResponseLawRisk {r : ℕ} (α β : ℝ) :
    Measurable (olsResponseLawRisk α β :
      (Fin (r + 2) → ℝ × ℝ) → ℝ) := by
  have hjoint : StronglyMeasurable
      (fun p : (Fin (r + 2) → ℝ × ℝ) × (ℝ × ℝ) =>
        |olsPrediction p.1 p.2.1 - p.2.2|) :=
    (measurable_olsResponseLoss_joint (r := r)).stronglyMeasurable
  have hsm : StronglyMeasurable
      (fun D : Fin (r + 2) → ℝ × ℝ =>
        ∫ z, |olsPrediction D z.1 - z.2| ∂olsAffineResponseTestLaw α β) :=
    hjoint.integral_prod_right'
  exact hsm.measurable

private theorem measurable_olsResponseValidationSummand {n : ℕ}
    (i : Fin (n + 3)) :
    Measurable (fun D : Fin (n + 3) → ℝ × ℝ =>
      |olsPrediction (deleteAt D i) (D i).1 - (D i).2|) := by
  have hdel : Measurable
      (fun D : Fin (n + 3) → ℝ × ℝ => deleteAt D i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (continuous_apply (i.succAbove j)).measurable
  have hx : Measurable (fun D : Fin (n + 3) → ℝ × ℝ => (D i).1) :=
    measurable_fst.comp (continuous_apply i).measurable
  have hy : Measurable (fun D : Fin (n + 3) → ℝ × ℝ => (D i).2) :=
    measurable_snd.comp (continuous_apply i).measurable
  have hp : Measurable
      (fun D : Fin (n + 3) → ℝ × ℝ =>
        olsPrediction (deleteAt D i) (D i).1) :=
    (measurable_olsPrediction_joint (r := n)).comp (hdel.prodMk hx)
  exact measurable_abs.comp (hp.sub hy)

/-- Whole-carrier measurability of the finite response validation error. -/
theorem measurable_olsResponseValidationError {n : ℕ} :
    Measurable (olsResponseValidationError :
      (Fin (n + 3) → ℝ × ℝ) → ℝ) := by
  unfold olsResponseValidationError
  have hsum : Measurable (fun D : Fin (n + 3) → ℝ × ℝ =>
      ∑ i : Fin (n + 3),
        |olsPrediction (deleteAt D i) (D i).1 - (D i).2|) := by
    apply Finset.measurable_sum Finset.univ
    intro i hi
    exact measurable_olsResponseValidationSummand i
  exact hsum.div_const (n + 3 : ℝ)

/-- Whole-carrier measurability of the literal response error. -/
theorem measurable_olsResponseError {n : ℕ} (α β : ℝ) :
    Measurable (olsResponseError α β :
      (Fin (n + 3) → ℝ × ℝ) → ℝ) := by
  exact (measurable_olsResponseLawRisk (r := n + 1) α β).sub
    measurable_olsResponseValidationError

private theorem measurableSet_olsResponseErrorTail {n : ℕ}
    (α β ε : ℝ) :
    MeasurableSet
      {D : Fin (n + 3) → ℝ × ℝ | |olsResponseError α β D| > ε} := by
  exact measurableSet_lt measurable_const
    (measurable_abs.comp (measurable_olsResponseError α β))

private theorem olsResponseLawRisk_sample_eq_affine {n : ℕ}
    (α β : ℝ) (G : Fin (n + 3) → ℝ × ℝ) :
    olsResponseLawRisk α β (olsAffineResponseSample α β G) =
      olsAffineResponseTestRisk α β G := by
  unfold olsResponseLawRisk olsAffineResponseTestRisk olsAffineResponseTestLoss
  apply integral_congr_ae
  filter_upwards with z
  exact abs_sub_comm _ _

private theorem olsResponseValidationError_sample_eq_affine {n : ℕ}
    (α β : ℝ) (G : Fin (n + 3) → ℝ × ℝ) :
    olsResponseValidationError (olsAffineResponseSample α β G) =
      olsAffineResponseValidationError (olsAffineResponseSample α β G) := by
  unfold olsResponseValidationError olsAffineResponseValidationError
  apply congrArg (fun x : ℝ => x / (n + 3 : ℝ))
  apply Finset.sum_congr rfl
  intro i hi
  rw [olsAffineResponse_deleteAt]
  simp only [olsAffineResponseSample, olsAffineResponsePair]
  rw [abs_sub_comm]

/-- The response-law error tail probability equals the actual iid
noise-coordinate OLS error tail probability for every `n ≥ 3`, `α`, `β`, and
threshold. The sample map is the accepted pushforward; event agreement is
proved almost everywhere on the positive full/deleted design locus. -/
theorem olsResponseErrorTailProbability_eq_noise {n : ℕ} (hn : 3 ≤ n)
    (α β ε : ℝ) :
    (olsAffineResponseLaw (n + 3) α β).real
        {D : Fin (n + 3) → ℝ × ℝ | |olsResponseError α β D| > ε} =
      (olsPairGaussianLaw (n + 3)).real
        {G : Fin (n + 3) → ℝ × ℝ |
          |olsTestError (n := n + 1) G| > ε} := by
  let f : (Fin (n + 3) → ℝ × ℝ) → Fin (n + 3) → ℝ × ℝ :=
    olsAffineResponseSample α β
  let μ := olsPairGaussianLaw (n + 3)
  let E : Set (Fin (n + 3) → ℝ × ℝ) :=
    {D | |olsResponseError α β D| > ε}
  let F : Set (Fin (n + 3) → ℝ × ℝ) :=
    {G | |olsTestError (n := n + 1) G| > ε}
  have hE : MeasurableSet E := by
    exact measurableSet_olsResponseErrorTail α β ε
  have hpre : f ⁻¹' E =ᵐ[μ] F := by
    have hRisk := ae_olsAffineResponseTestRisk_eq_olsTestRisk hn α β
    have hVal := ae_olsAffineResponseValidationError_eq_olsValidationError
      hn α β
    filter_upwards [hRisk, hVal] with G hRisk hVal
    have hError : olsResponseError α β (olsAffineResponseSample α β G) =
        olsTestError (n := n + 1) G := by
      unfold olsResponseError olsTestError
      rw [olsResponseLawRisk_sample_eq_affine, hRisk,
        olsResponseValidationError_sample_eq_affine, hVal]
    apply propext
    change G ∈ f ⁻¹' E ↔ G ∈ F
    change |olsResponseError α β (olsAffineResponseSample α β G)| > ε ↔
      |olsTestError (n := n + 1) G| > ε
    rw [hError]
  calc
    (olsAffineResponseLaw (n + 3) α β).real E =
        (μ.map f).real E := by
      rw [← olsPairGaussianLaw_map_olsAffineResponseSample (n + 3) α β]
    _ = μ.real (f ⁻¹' E) := by
      exact map_measureReal_apply (measurable_olsAffineResponseSample α β) hE
    _ = μ.real F := measureReal_congr hpre

#print axioms measurable_olsResponseLawRisk
#print axioms measurable_olsResponseValidationError
#print axioms measurable_olsResponseError
#print axioms olsResponseErrorTailProbability_eq_noise

end LOOConcentration
