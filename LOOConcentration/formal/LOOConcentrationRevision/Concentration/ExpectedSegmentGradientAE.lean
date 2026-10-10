import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory Filter
open scoped Gradient

/-- Integrating the sealed almost-everywhere gradient segment estimate gives
the source expected-loss bound. The zero-section and rate integrability are
the only integrability inputs. -/
theorem expected_segment_gradient_ae
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → EuclideanSpace ℝ ι → ℝ)
    (hjoint : Measurable (fun p : α × EuclideanSpace ℝ ι => F p.1 p.2))
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (F z))
    (A B : α → NNReal)
    (hAInt : Integrable (fun z => (A z : ℝ)) μ)
    (hBInt : Integrable (fun z => (B z : ℝ)) μ)
    (h0Int : Integrable (fun z => F z 0) μ)
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ (A z : ℝ) + (B z : ℝ) * ‖x‖) :
    (∀ x, Integrable (fun z => F z x) μ) ∧
      (∀ x y,
        |(∫ z, F z x ∂μ) - (∫ z, F z y ∂μ)| ≤
          ‖x - y‖ *
            ((∫ z, (A z : ℝ) ∂μ) + (∫ z, (B z : ℝ) ∂μ) / 2 *
              (‖x‖ + ‖y‖))) ∧
      LocallyLipschitz (fun x => ∫ z, F z x ∂μ) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
        DifferentiableAt ℝ (fun x => ∫ z, F z x ∂μ) x ∧
          ‖gradient (fun x => ∫ z, F z x ∂μ) x‖ ≤
            (∫ z, (A z : ℝ) ∂μ) + (∫ z, (B z : ℝ) ∂μ) * ‖x‖ := by
  let φ : EuclideanSpace ℝ ι → ℝ := fun x => ∫ z, F z x ∂μ
  let EA : ℝ := ∫ z, (A z : ℝ) ∂μ
  let EB : ℝ := ∫ z, (B z : ℝ) ∂μ
  have hEA : 0 ≤ EA := by
    dsimp [EA]
    exact integral_nonneg fun z => (A z).2
  have hEB : 0 ≤ EB := by
    dsimp [EB]
    exact integral_nonneg fun z => (B z).2
  have hsegment : ∀ᵐ z ∂μ, ∀ x y : EuclideanSpace ℝ ι,
      |F z x - F z y| ≤ ‖x - y‖ *
        ((A z : ℝ) + (B z : ℝ) / 2 * (‖x‖ + ‖y‖)) := by
    filter_upwards [hloc, hgrad] with z hzloc hzgrad
    intro x y
    exact ae_gradient_segment_estimate (F z) hzloc (A z) (B z) hzgrad x y
  have hsectionMeas (x : EuclideanSpace ℝ ι) : Measurable (fun z => F z x) :=
    hjoint.comp (measurable_id.prodMk measurable_const)
  have hsections : ∀ x, Integrable (fun z => F z x) μ := by
    intro x
    let major : α → ℝ := fun z =>
      |F z 0| + ‖x‖ * ((A z : ℝ) + (B z : ℝ) * (‖x‖ / 2))
    have hmajor : Integrable major μ := by
      have hrate : Integrable
          (fun z => (A z : ℝ) + (B z : ℝ) * (‖x‖ / 2)) μ := by
        exact hAInt.add (hBInt.mul_const (‖x‖ / 2))
      exact h0Int.norm.add (hrate.const_mul ‖x‖)
    have hbound : ∀ᵐ z ∂μ, ‖F z x‖ ≤ major z := by
      filter_upwards [hsegment] with z hz
      have hseg := hz x 0
      have hseg' : |F z x - F z 0| ≤
          ‖x‖ * ((A z : ℝ) + (B z : ℝ) * (‖x‖ / 2)) := by
        convert (by simpa [norm_zero] using hseg) using 1; ring
      change |F z x| ≤ _
      calc
        |F z x| = |(F z x - F z 0) + F z 0| := by congr 1; ring
        _ ≤ |F z x - F z 0| + |F z 0| := abs_add_le _ _
        _ ≤ |F z 0| + ‖x‖ * ((A z : ℝ) + (B z : ℝ) * (‖x‖ / 2)) := by
          linarith [add_le_add_left hseg' |F z 0|]
        _ = major z := rfl
    apply Integrable.mono' hmajor (hsectionMeas x).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    exact hz
  have hmean : ∀ x y,
      |(∫ z, F z x ∂μ) - (∫ z, F z y ∂μ)| ≤
        ‖x - y‖ * (EA + EB / 2 * (‖x‖ + ‖y‖)) := by
    intro x y
    let q : ℝ := ‖x - y‖
    let c : ℝ := (‖x‖ + ‖y‖) / 2
    have hmajor : Integrable
        (fun z => q * ((A z : ℝ) + (B z : ℝ) * c)) μ := by
      exact (hAInt.add (hBInt.mul_const c)).const_mul q
    have hdiff : Integrable (fun z => F z x - F z y) μ :=
      (hsections x).sub (hsections y)
    have habs : Integrable (fun z => |F z x - F z y|) μ := hdiff.norm
    have hmono : (∫ z, |F z x - F z y| ∂μ) ≤
        ∫ z, q * ((A z : ℝ) + (B z : ℝ) * c) ∂μ := by
      apply integral_mono_ae habs hmajor
      filter_upwards [hsegment] with z hz
      have hz := hz x y
      dsimp [q, c]
      have hc : (B z : ℝ) / 2 * (‖x‖ + ‖y‖) =
          (B z : ℝ) * ((‖x‖ + ‖y‖) / 2) := by ring
      rw [hc] at hz
      exact hz
    have hsum :
        (∫ z, (A z : ℝ) + (B z : ℝ) * c ∂μ) = EA + EB * c := by
      dsimp [EA, EB]
      rw [integral_add hAInt (hBInt.mul_const c), integral_mul_const]
    calc
      |(∫ z, F z x ∂μ) - (∫ z, F z y ∂μ)| =
          |∫ z, (F z x - F z y) ∂μ| := by rw [integral_sub (hsections x) (hsections y)]
      _ ≤ ∫ z, |F z x - F z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, q * ((A z : ℝ) + (B z : ℝ) * c) ∂μ := hmono
      _ = q * (EA + EB * c) := by rw [integral_const_mul, hsum]
      _ = ‖x - y‖ * (EA + EB / 2 * (‖x‖ + ‖y‖)) := by
        dsimp [q, c]
        ring
  have hlocal : LocallyLipschitz φ := by
    intro x
    let K : ℝ := EA + EB * (‖x‖ + 1)
    refine ⟨Real.toNNReal K, Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
    apply LipschitzOnWith.of_dist_le'
    intro u hu v hv
    have huNorm : ‖u‖ ≤ ‖x‖ + 1 := by
      have hdist : dist u x < 1 := Metric.mem_ball.mp hu
      calc
        ‖u‖ = ‖(u - x) + x‖ := by congr 1; abel
        _ ≤ ‖u - x‖ + ‖x‖ := norm_add_le _ _
        _ = dist u x + ‖x‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖x‖ := by linarith
        _ = ‖x‖ + 1 := by ring
    have hvNorm : ‖v‖ ≤ ‖x‖ + 1 := by
      have hdist : dist v x < 1 := Metric.mem_ball.mp hv
      calc
        ‖v‖ = ‖(v - x) + x‖ := by congr 1; abel
        _ ≤ ‖v - x‖ + ‖x‖ := norm_add_le _ _
        _ = dist v x + ‖x‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖x‖ := by linarith
        _ = ‖x‖ + 1 := by ring
    have hcoef : EA + EB / 2 * (‖u‖ + ‖v‖) ≤ K := by
      dsimp [K]
      calc
        EA + EB / 2 * (‖u‖ + ‖v‖) ≤
            EA + EB / 2 * (2 * (‖x‖ + 1)) := by gcongr; linarith
        _ = EA + EB * (‖x‖ + 1) := by ring
    have hbound := hmean u v
    have hdist : dist (φ u) (φ v) ≤ K * dist u v := by
      rw [Real.dist_eq, dist_eq_norm]
      calc
        |φ u - φ v| ≤ ‖u - v‖ * (EA + EB / 2 * (‖u‖ + ‖v‖)) := by
          simpa only [φ, Real.norm_eq_abs] using hbound
        _ ≤ ‖u - v‖ * K := mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)
        _ = K * dist u v := by rw [dist_eq_norm]; ring
    exact hdist
  have hgradPoint (x : EuclideanSpace ℝ ι) :
      ‖gradient φ x‖ ≤ EA + EB * ‖x‖ := by
    have hderivε : ∀ ε : ℝ, 0 < ε →
        ‖fderiv ℝ φ x‖ ≤ EA + EB * ‖x‖ + ε := by
      intro ε hε
      let δ : ℝ := ε / (EB + 1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      have hEBδ : EB * δ ≤ ε := by
        calc
          EB * δ = (EB * ε) / (EB + 1) := by dsimp [δ]; ring
          _ ≤ ε := (div_le_iff₀ (by positivity : 0 < EB + 1)).2 (by nlinarith)
      have hhalf : EB / 2 * δ ≤ ε := by
        have hnonneg : 0 ≤ EB * δ := mul_nonneg hEB (le_of_lt hδ)
        nlinarith
      apply norm_fderiv_le_of_lip' ℝ (by positivity)
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      have hyNorm : ‖y‖ ≤ ‖x‖ + δ := by
        have hd : dist y x < δ := Metric.mem_ball.mp hy
        calc
          ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ = dist y x + ‖x‖ := by rw [dist_eq_norm]
          _ ≤ δ + ‖x‖ := by linarith
          _ = ‖x‖ + δ := by ring
      have hcoef : EA + EB / 2 * (‖x‖ + ‖y‖) ≤
          EA + EB * ‖x‖ + ε := by
        calc
          EA + EB / 2 * (‖x‖ + ‖y‖) ≤
              EA + EB / 2 * (‖x‖ + (‖x‖ + δ)) := by gcongr
          _ = EA + EB * ‖x‖ + EB / 2 * δ := by ring
          _ ≤ EA + EB * ‖x‖ + ε := by linarith
      have hbound := hmean y x
      calc
        ‖φ y - φ x‖ = |φ y - φ x| := Real.norm_eq_abs _
        _ ≤ ‖y - x‖ * (EA + EB / 2 * (‖y‖ + ‖x‖)) := by
          simpa only [φ, add_comm (‖y‖) (‖x‖), Real.norm_eq_abs] using hbound
        _ ≤ (EA + EB * ‖x‖ + ε) * ‖y - x‖ := by
          calc
            ‖y - x‖ * (EA + EB / 2 * (‖y‖ + ‖x‖)) ≤
                ‖y - x‖ * (EA + EB * ‖x‖ + ε) :=
              mul_le_mul_of_nonneg_left (by simpa [add_comm] using hcoef) (norm_nonneg _)
            _ = (EA + EB * ‖x‖ + ε) * ‖y - x‖ := by ring
    have hfd : ‖fderiv ℝ φ x‖ ≤ EA + EB * ‖x‖ :=
      le_of_forall_pos_le_add hderivε
    calc
      ‖gradient φ x‖ = ‖fderiv ℝ φ x‖ := by
        rw [gradient, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
      _ ≤ EA + EB * ‖x‖ := hfd
  have haeDiff := locallyLipschitz_ae_differentiableAt φ hlocal
  refine ⟨hsections, ?_, ?_, ?_⟩
  · intro x y
    simpa only [EA, EB] using hmean x y
  · exact hlocal
  · filter_upwards [haeDiff] with x hx
    exact ⟨hx, hgradPoint x⟩

end LOOConcentration.Revision
