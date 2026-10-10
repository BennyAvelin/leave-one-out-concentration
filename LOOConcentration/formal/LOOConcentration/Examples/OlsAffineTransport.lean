import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LOOConcentration.Frozen.Examples.OlsPrediction
import LOOConcentration.Examples.GaussianDesignIndependence
import LOOConcentration.Examples.OlsGoodSetErrorLipschitz

set_option autoImplicit false

open MeasureTheory
open ProbabilityTheory

namespace LOOConcentration

/-!
# Affine response transport for the actual OLS sample

The response coordinates are obtained from the actual iid noise-pair sample by
the measurable pointwise map `(x,e) ↦ (x, α + β*x + e)`. OLS identities below
are stated only on samples with positive centered design, matching the frozen
zero-slope convention on singular designs.
-/

/-- The literal one-observation affine response map. -/
def olsAffineResponsePair (α β : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, α + β * z.1 + z.2)

/-- The coordinatewise affine response sample on a finite noise sample. -/
def olsAffineResponseSample {N : ℕ} (α β : ℝ)
    (G : Fin N → ℝ × ℝ) : Fin N → ℝ × ℝ :=
  fun i => olsAffineResponsePair α β (G i)

/-- The actual one-observation response law, defined as a pushforward. -/
noncomputable abbrev olsAffineResponsePairLaw (α β : ℝ) : Measure (ℝ × ℝ) :=
  (standardGaussian.prod standardGaussian).map (olsAffineResponsePair α β)

/-- The actual iid response law at sample size `N`. -/
noncomputable abbrev olsAffineResponseLaw (N : ℕ) (α β : ℝ) :
    Measure (Fin N → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin N => olsAffineResponsePairLaw α β)

/-- The independent response test-pair law. -/
noncomputable abbrev olsAffineResponseTestLaw (α β : ℝ) : Measure (ℝ × ℝ) :=
  olsTestLaw.map (olsAffineResponsePair α β)

/-- The response-coordinate absolute test loss for the frozen predictor. -/
noncomputable def olsAffineResponseTestLoss {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  |z.2 - olsPrediction (olsAffineResponseSample α β G) z.1|

/-- The response-coordinate test risk under the actual transformed test law. -/
noncomputable def olsAffineResponseTestRisk {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) : ℝ :=
  ∫ z, olsAffineResponseTestLoss α β G z ∂olsAffineResponseTestLaw α β

/-- The response-coordinate finite validation error for a sample of size `N`. -/
noncomputable def olsAffineResponseValidationError {n : ℕ}
    (G : Fin (n + 3) → ℝ × ℝ) : ℝ :=
  (∑ i : Fin (n + 3),
    |(G i).2 - olsPrediction (deleteAt G i) (G i).1|) / (n + 3 : ℝ)

theorem measurable_olsAffineResponsePair (α β : ℝ) :
    Measurable (olsAffineResponsePair α β) := by
  unfold olsAffineResponsePair
  fun_prop

theorem measurable_olsAffineResponseSample {N : ℕ} (α β : ℝ) :
    Measurable (olsAffineResponseSample α β :
      (Fin N → ℝ × ℝ) → Fin N → ℝ × ℝ) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_olsAffineResponsePair α β).comp (measurable_pi_apply i)

/-- Mapping every coordinate by the affine response transform sends the actual
iid noise-pair law to the finite iid response law. -/
theorem olsPairGaussianLaw_map_olsAffineResponseSample (N : ℕ) (α β : ℝ) :
    (olsPairGaussianLaw N).map (olsAffineResponseSample α β) =
      olsAffineResponseLaw N α β := by
  let μ : Fin N → Measure (ℝ × ℝ) := fun _ => standardGaussian.prod standardGaussian
  let f : Fin N → (ℝ × ℝ) → ℝ × ℝ := fun _ => olsAffineResponsePair α β
  change (Measure.pi μ).map (fun G i => f i (G i)) =
    Measure.pi (fun i => (μ i).map (f i))
  exact Measure.pi_map_pi (fun _ => (measurable_olsAffineResponsePair α β).aemeasurable)

private theorem olsPrediction_eq_olsNoisePredictor {r : ℕ}
    (D : Fin (r + 2) → ℝ × ℝ) (u : ℝ) :
    olsPrediction D u = olsNoisePredictor D u := by
  simp [olsPrediction, olsNoisePredictor, olsNoiseSlope, olsCenteredCross,
    olsCenteredDesign, olsXBar, olsEBar]

/-- The covariate sample mean is unchanged by the response transformation. -/
theorem olsAffineResponse_olsXBar {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) :
    olsXBar (olsAffineResponseSample α β G) = olsXBar G := by
  rfl

/-- The response sample mean is the affine transform of the covariate and
noise sample means. -/
theorem olsAffineResponse_olsEBar {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) :
    olsEBar (olsAffineResponseSample α β G) =
      α + β * olsXBar G + olsEBar G := by
  change
    (∑ i : Fin (r + 2), (α + β * (G i).1 + (G i).2)) /
        ((r + 2 : ℕ) : ℝ) =
      α + β * ((∑ i : Fin (r + 2), (G i).1) / ((r + 2 : ℕ) : ℝ)) +
        (∑ i : Fin (r + 2), (G i).2) / ((r + 2 : ℕ) : ℝ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hN : ((r + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hN]

/-- The centered design is unchanged by an affine response transformation. -/
theorem olsAffineResponse_olsCenteredDesign {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) :
    olsCenteredDesign (olsAffineResponseSample α β G) = olsCenteredDesign G := by
  simp only [olsCenteredDesign, olsAffineResponseSample,
    olsAffineResponsePair, olsAffineResponse_olsXBar]

/-- The centered cross term transforms by `β * design + noise cross`. -/
theorem olsAffineResponse_olsCenteredCross {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) :
    olsCenteredCross (olsAffineResponseSample α β G) =
      β * olsCenteredDesign G + olsCenteredCross G := by
  rw [show olsCenteredCross (olsAffineResponseSample α β G) =
      ∑ i : Fin (r + 2),
        ((olsAffineResponseSample α β G i).1 -
          olsXBar (olsAffineResponseSample α β G)) *
        ((olsAffineResponseSample α β G i).2 -
          olsEBar (olsAffineResponseSample α β G)) by rfl]
  rw [olsAffineResponse_olsXBar, olsAffineResponse_olsEBar]
  simp only [olsAffineResponseSample, olsAffineResponsePair]
  calc
    _ = ∑ i : Fin (r + 2),
        (β * ((G i).1 - olsXBar G) ^ 2 +
          ((G i).1 - olsXBar G) * ((G i).2 - olsEBar G)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = β * olsCenteredDesign G + olsCenteredCross G := by
      simp only [olsCenteredDesign, olsCenteredCross, Finset.sum_add_distrib,
        ← Finset.mul_sum]

/-- On a positive design, the transformed fitted slope is `β` plus the noise
slope. The positive-design condition discharges the real denominator. -/
theorem olsAffineResponse_olsNoiseSlope {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ)
    (hdesign : 0 < olsCenteredDesign G) :
    olsNoiseSlope (olsAffineResponseSample α β G) =
      β + olsNoiseSlope G := by
  unfold olsNoiseSlope
  rw [olsAffineResponse_olsCenteredCross, olsAffineResponse_olsCenteredDesign]
  have hs : olsCenteredDesign G ≠ 0 := ne_of_gt hdesign
  field_simp [hs]

/-- The frozen predictor has the source-faithful affine response identity on
every positive-design sample. No claim is made on singular designs. -/
theorem olsAffineResponse_olsPrediction {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) (hdesign : 0 < olsCenteredDesign G) (u : ℝ) :
    olsPrediction (olsAffineResponseSample α β G) u =
      α + β * u + olsNoisePredictor G u := by
  rw [olsPrediction_eq_olsNoisePredictor]
  unfold olsNoisePredictor
  rw [olsAffineResponse_olsEBar α β G,
    olsAffineResponse_olsNoiseSlope α β G hdesign,
    olsAffineResponse_olsXBar α β G]
  ring

private theorem measurable_olsAffineResponseTestLoss {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ) :
    Measurable (olsAffineResponseTestLoss α β G) := by
  unfold olsAffineResponseTestLoss olsPrediction olsAffineResponseSample
    olsAffineResponsePair
  fun_prop

/-- The fixed-design response loss is integrable under the actual transformed
independent test law whenever the design is positive. -/
theorem integrable_olsAffineResponseTestLoss {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ)
    (hdesign : 0 < olsCenteredDesign G) :
    Integrable (olsAffineResponseTestLoss α β G)
      (olsAffineResponseTestLaw α β) := by
  have hcomp : Integrable
      (fun z : ℝ × ℝ =>
        olsAffineResponseTestLoss α β G (olsAffineResponsePair α β z))
      olsTestLaw := by
    have hEq :
        (fun z : ℝ × ℝ =>
          olsAffineResponseTestLoss α β G (olsAffineResponsePair α β z)) =
            olsRiskLoss G := by
      funext z
      rw [olsAffineResponseTestLoss, olsAffineResponsePair,
        olsAffineResponse_olsPrediction α β G hdesign z.1,
        olsRiskLoss]
      ring_nf
    rw [hEq]
    exact olsTestRiskLoss_integrable G
  exact (integrable_map_measure
    (measurable_olsAffineResponseTestLoss α β G).aestronglyMeasurable
    (measurable_olsAffineResponsePair α β).aemeasurable).mpr hcomp

/-- Genuine integral-map transport identifies the response-space independent
test risk with the actual noise-coordinate risk on every positive design. -/
theorem olsAffineResponseTestRisk_eq_olsTestRisk {r : ℕ} (α β : ℝ)
    (G : Fin (r + 2) → ℝ × ℝ)
    (hdesign : 0 < olsCenteredDesign G) :
    olsAffineResponseTestRisk α β G = olsTestRisk G := by
  unfold olsAffineResponseTestRisk olsTestRisk
  rw [integral_map (measurable_olsAffineResponsePair α β).aemeasurable
    (integrable_olsAffineResponseTestLoss α β G hdesign).aestronglyMeasurable]
  have hEq :
      (fun z : ℝ × ℝ =>
        olsAffineResponseTestLoss α β G (olsAffineResponsePair α β z)) =
          olsRiskLoss G := by
    funext z
    rw [olsAffineResponseTestLoss, olsAffineResponsePair,
      olsAffineResponse_olsPrediction α β G hdesign z.1,
      olsRiskLoss]
    ring_nf
  rw [hEq]

/-- A coordinate deletion commutes definitionally with the pointwise response
transformation. -/
theorem olsAffineResponse_deleteAt {N : ℕ} (α β : ℝ)
    (G : Fin (N + 1) → ℝ × ℝ) (i : Fin (N + 1)) :
    deleteAt (olsAffineResponseSample α β G) i =
      olsAffineResponseSample α β (deleteAt G i) := by
  rfl

/-- The response validation error at the exact `n+3` full-sample size equals
the noise-coordinate validation error when every deleted design is positive. -/
theorem olsAffineResponseValidationError_eq_olsValidationError {n : ℕ}
    (α β : ℝ) (G : Fin (n + 3) → ℝ × ℝ)
    (hdeleted : ∀ i : Fin (n + 3),
      0 < olsCenteredDesign (deleteAt G i)) :
    olsAffineResponseValidationError (olsAffineResponseSample α β G) =
      olsValidationError (n := n + 1) G := by
  unfold olsAffineResponseValidationError olsValidationError
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [olsAffineResponse_deleteAt]
    rw [olsAffineResponse_olsPrediction α β (deleteAt G i) (hdeleted i)]
    simp only [olsAffineResponseSample, olsAffineResponsePair]
    ring_nf
  · push_cast
    ring

private theorem measurable_olsDeleteAt {N : ℕ} (i : Fin (N + 1)) :
    Measurable (fun G : Fin (N + 1) → ℝ × ℝ => deleteAt G i) := by
  rw [measurable_pi_iff]
  intro j
  exact measurable_pi_apply (i.succAbove j)

/-- For a positive residual dimension, the actual centered Gaussian design is
strictly positive almost everywhere. This follows from the reviewed actual
pushforward law and atomlessness of one Gaussian coordinate. -/
theorem ae_olsCenteredDesign_pos_succ {r : ℕ} (hr : 0 < r) :
    ∀ᵐ G : Fin (r + 1) → ℝ × ℝ ∂olsPairGaussianLaw (r + 1),
      0 < olsCenteredDesign G := by
  let μ := olsPairGaussianLaw (r + 1)
  let ν := Measure.pi (fun _ : Fin r => standardGaussian)
  let q : (Fin r → ℝ) → ℝ := fun x => ∑ i : Fin r, (x i) ^ 2
  have hdesign : Measure.map olsCenteredDesign μ = ν.map q := by
    simpa [μ, ν, q, standardGaussian] using
      (olsCenteredDesign_gaussian_pushforward r)
  have hq : ∀ᵐ x : Fin r → ℝ ∂ν, 0 < q x := by
    let i : Fin r := ⟨0, hr⟩
    have hi := Measure.ae_eval_ne
      (μ := fun _ : Fin r => standardGaussian)
      i (0 : ℝ)
    filter_upwards [hi] with x hxi
    have hle : (x i) ^ 2 ≤ q x := by
      dsimp [q]
      exact Finset.single_le_sum (fun j hj => sq_nonneg (x j))
        (Finset.mem_univ i)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hxi) hle
  have hqmeas : Measurable q := by
    dsimp [q]
    fun_prop
  have hqset : MeasurableSet {y : ℝ | 0 < y} := measurableSet_lt
    measurable_const measurable_id
  have hmapPos : ∀ᵐ y : ℝ ∂Measure.map q ν, 0 < y :=
    (ae_map_iff hqmeas.aemeasurable hqset).2 hq
  rw [← hdesign] at hmapPos
  exact (ae_map_iff measurable_olsCenteredDesign.aemeasurable hqset).mp hmapPos

/-- Deleting one coordinate from an iid Gaussian pair sample has exactly the
smaller iid law, for every deleted index. -/
theorem olsPairGaussianLaw_map_deleteAt {N : ℕ} (i : Fin (N + 1)) :
    (olsPairGaussianLaw (N + 1)).map (fun G => deleteAt G i) =
      olsPairGaussianLaw N := by
  let μ : Fin (N + 1) → Measure (ℝ × ℝ) := fun _ =>
    standardGaussian.prod standardGaussian
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ × ℝ) i
  have he :
      (Measure.pi μ).map e =
        (μ i).prod (Measure.pi fun j : Fin N => μ (i.succAbove j)) :=
    measurePreserving_piFinSuccAbove μ i |>.map_eq
  have hdelFun : (fun G : Fin (N + 1) → ℝ × ℝ => deleteAt G i) =
      fun G => (e G).2 := by
    funext G
    funext j
    rfl
  calc
    _ = (Measure.pi μ).map (fun G => (e G).2) := by rw [hdelFun]
    _ = ((Measure.pi μ).map e).map Prod.snd := by
      rw [Measure.map_map measurable_snd e.measurable]
      rfl
    _ = ((μ i).prod (Measure.pi fun j : Fin N => μ (i.succAbove j))).map Prod.snd := by
      rw [he]
    _ = Measure.pi (fun j : Fin N => μ (i.succAbove j)) := by
      rw [Measure.map_snd_prod]
      simp [μ]
    _ = Measure.pi (fun _ : Fin N => standardGaussian.prod standardGaussian) := by
      simp [μ]
    _ = olsPairGaussianLaw N := by
      rfl

/-- Under the actual iid pair law of a sample of size `n+3`, the full design
and every one-observation-deleted design are positive almost everywhere for
`n ≥ 3` (hence `N ≥ 6`). The finite union of deleted exceptional sets is
handled by `ae_all_iff`. -/
theorem ae_olsFullAndDeletedDesign_pos {n : ℕ} (hn : 3 ≤ n) :
    ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂olsPairGaussianLaw (n + 3),
      0 < olsCenteredDesign G ∧
        ∀ i : Fin (n + 3),
          0 < olsCenteredDesign (deleteAt G i) := by
  let μ := olsPairGaussianLaw (n + 3)
  have hfull : ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂μ,
      0 < olsCenteredDesign G := by
    simpa [μ, Nat.add_assoc] using
      (ae_olsCenteredDesign_pos_succ (r := n + 2) (by omega))
  have hdel : ∀ i : Fin (n + 3),
      ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂μ,
        0 < olsCenteredDesign (deleteAt G i) := by
    intro i
    have hdelLaw :
        (μ.map (fun G : Fin (n + 3) → ℝ × ℝ => deleteAt G i)) =
          olsPairGaussianLaw (n + 2) := by
      dsimp [μ]
      simpa [Nat.add_assoc] using
        (olsPairGaussianLaw_map_deleteAt (N := n + 2) i)
    have hpos : ∀ᵐ D : Fin (n + 2) → ℝ × ℝ ∂
        (μ.map (fun G : Fin (n + 3) → ℝ × ℝ => deleteAt G i)),
          0 < olsCenteredDesign D := by
      rw [hdelLaw]
      simpa [Nat.add_assoc] using
        (ae_olsCenteredDesign_pos_succ (r := n + 1) (by omega))
    have hdelmeas : Measurable
        (fun G : Fin (n + 3) → ℝ × ℝ => deleteAt G i) := by
      exact measurable_olsDeleteAt i
    have hset : MeasurableSet
        {D : Fin (n + 2) → ℝ × ℝ | 0 < olsCenteredDesign D} :=
      measurableSet_lt measurable_const measurable_olsCenteredDesign
    exact (ae_map_iff hdelmeas.aemeasurable hset).mp hpos
  have hall : ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂μ,
      ∀ i : Fin (n + 3),
        0 < olsCenteredDesign (deleteAt G i) := by
    rw [ae_all_iff]
    exact hdel
  filter_upwards [hfull, hall] with G hG hGdel
  exact ⟨hG, hGdel⟩

/-- The response and noise test risks agree almost everywhere for the actual
`n+3` iid Gaussian training sample. -/
theorem ae_olsAffineResponseTestRisk_eq_olsTestRisk {n : ℕ} (hn : 3 ≤ n)
    (α β : ℝ) :
    ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂olsPairGaussianLaw (n + 3),
      olsAffineResponseTestRisk α β G = olsTestRisk G := by
  filter_upwards [ae_olsFullAndDeletedDesign_pos hn] with G hG
  exact olsAffineResponseTestRisk_eq_olsTestRisk α β G hG.1

/-- The response and noise validation errors agree almost everywhere for the
actual `n+3` iid Gaussian sample, with exact `n+2` deleted-fit indexing. -/
theorem ae_olsAffineResponseValidationError_eq_olsValidationError {n : ℕ}
    (hn : 3 ≤ n) (α β : ℝ) :
    ∀ᵐ G : Fin (n + 3) → ℝ × ℝ ∂olsPairGaussianLaw (n + 3),
      olsAffineResponseValidationError (olsAffineResponseSample α β G) =
        olsValidationError (n := n + 1) G := by
  filter_upwards [ae_olsFullAndDeletedDesign_pos hn] with G hG
  exact olsAffineResponseValidationError_eq_olsValidationError α β G hG.2

#print axioms measurable_olsAffineResponsePair
#print axioms measurable_olsAffineResponseSample
#print axioms olsPairGaussianLaw_map_olsAffineResponseSample
#print axioms olsAffineResponse_olsXBar
#print axioms olsAffineResponse_olsEBar
#print axioms olsAffineResponse_olsCenteredDesign
#print axioms olsAffineResponse_olsCenteredCross
#print axioms olsAffineResponse_olsNoiseSlope
#print axioms olsAffineResponse_olsPrediction
#print axioms integrable_olsAffineResponseTestLoss
#print axioms olsAffineResponseTestRisk_eq_olsTestRisk
#print axioms olsAffineResponse_deleteAt
#print axioms olsAffineResponseValidationError_eq_olsValidationError
#print axioms ae_olsCenteredDesign_pos_succ
#print axioms olsPairGaussianLaw_map_deleteAt
#print axioms ae_olsFullAndDeletedDesign_pos
#print axioms ae_olsAffineResponseTestRisk_eq_olsTestRisk
#print axioms ae_olsAffineResponseValidationError_eq_olsValidationError

end LOOConcentration
