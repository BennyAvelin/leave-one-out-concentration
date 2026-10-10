import LOOConcentrationRevision.FunctionalInequalities.LogSobolevConstant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Moments.Variance

/-!
# Bounded smooth scalar separators

An arctangent of a coordinate separates any two distinct points. For a
non-Dirac probability law, at least one such coordinate is not almost surely
constant, so its real variance is positive.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Gradient

namespace LOOConcentration.Revision

private noncomputable def arctanCoordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : EuclideanSpace ℝ ι → ℝ := fun x => Real.arctan (x i)

private theorem arctanCoordinate_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x y : EuclideanSpace ℝ ι) :
    fderiv ℝ (arctanCoordinate i) x y =
      (1 / (1 + (x i) ^ 2)) * y i := by
  let p : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i
  change fderiv ℝ (Real.arctan ∘ p) x y = _
  have hp : HasFDerivAt p p x := p.hasFDerivAt
  have ha : HasFDerivAt Real.arctan
      (ContinuousLinearMap.toSpanSingleton ℝ (1 / (1 + (x i) ^ 2))) (x i) :=
    (Real.hasDerivAt_arctan (x i)).hasFDerivAt
  have h := (ha.comp x hp).fderiv
  rw [h]
  simp [p]
  ring

private theorem arctanCoordinate_gradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : EuclideanSpace ℝ ι) :
    gradient (arctanCoordinate i) x =
      (1 / (1 + (x i) ^ 2)) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  have h := inner_gradient_right (𝕜 := ℝ) (f := arctanCoordinate i)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := x)
  rw [EuclideanSpace.inner_single_left] at h
  have hd := arctanCoordinate_fderiv i x (EuclideanSpace.single j (1 : ℝ))
  rw [hd] at h
  simpa [PiLp.single_apply, eq_comm, mul_comm] using h

private theorem arctanCoordinate_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (arctanCoordinate i) := by
  let p : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.arctan ∘ p)
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := p.contDiff
  exact Real.contDiff_arctan.comp hp

private theorem arctanCoordinate_abs_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : EuclideanSpace ℝ ι) :
    |arctanCoordinate i x| ≤ Real.pi / 2 := by
  change |Real.arctan (x i)| ≤ Real.pi / 2
  exact abs_le.mpr ⟨(Real.arctan_mem_Ioo (x i)).1.le,
    (Real.arctan_mem_Ioo (x i)).2.le⟩

private theorem arctanCoordinate_gradient_bound {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (x : EuclideanSpace ℝ ι) :
    ‖gradient (arctanCoordinate i) x‖ ≤ 1 := by
  rw [arctanCoordinate_gradient]
  have hcoef_nonneg : 0 ≤ 1 / (1 + (x i) ^ 2) := by positivity
  have hcoef_le : 1 / (1 + (x i) ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + (x i) ^ 2)]
    nlinarith [sq_nonneg (x i)]
  simpa only [norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs,
    abs_of_nonneg hcoef_nonneg, mul_one] using hcoef_le

private theorem arctanCoordinate_memLp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (arctanCoordinate i) 2 μ := by
  have hcontinuous : Continuous (arctanCoordinate i) :=
    (arctanCoordinate_contDiff i).continuous
  have hbound : ∀ x, ‖arctanCoordinate i x‖ ≤ Real.pi + 1 := by
    intro x
    rw [Real.norm_eq_abs]
    exact (arctanCoordinate_abs_bound i x).trans (by linarith [Real.pi_pos])
  exact MemLp.of_bound hcontinuous.aestronglyMeasurable (Real.pi + 1)
    (Filter.Eventually.of_forall hbound)

/-- Distinct points in a finite Euclidean space are separated by a bounded,
globally smooth scalar function whose gradient is bounded everywhere. -/
theorem exists_bounded_smooth_separator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : EuclideanSpace ℝ ι) (hxy : x ≠ y) :
    ∃ f : EuclideanSpace ℝ ι → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, |f z| ≤ B ∧ ‖gradient f z‖ ≤ B) ∧
      f x ≠ f y := by
  classical
  have hcoord : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    apply hxy
    ext i
    exact h i
  obtain ⟨i, hne⟩ := hcoord
  refine ⟨arctanCoordinate i, arctanCoordinate_contDiff i, ?_, ?_⟩
  · refine ⟨Real.pi + 1, by linarith [Real.pi_pos], ?_⟩
    intro z
    refine ⟨?_, ?_⟩
    · exact (arctanCoordinate_abs_bound i z).trans (by linarith [Real.pi_pos])
    · exact (arctanCoordinate_gradient_bound i z).trans (by linarith [Real.pi_pos])
  · change Real.arctan (x i) ≠ Real.arctan (y i)
    exact fun heq => hne (Real.arctan_injective heq)

/-- A non-Dirac probability law has a coordinate arctangent that is not
almost surely constant. The proof intersects the finitely many coordinate
events and uses that the probability almost-everywhere filter is nontrivial. -/
theorem exists_nonconstant_arctan_coordinate {ι : Type*} [Fintype ι]
    [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ ≠ Measure.dirac a) :
    ∃ i, ∀ c : ℝ,
      ¬ ((fun x : EuclideanSpace ℝ ι => Real.arctan (x i)) =ᵐ[μ] fun _ => c) := by
  classical
  by_contra h
  push Not at h
  choose c hc using h
  have hall : ∀ᵐ x ∂μ, ∀ i, Real.arctan (x i) = c i :=
    ae_all_iff.mpr hc
  obtain ⟨a, ha⟩ := hall.exists
  have hpoint : ∀ᵐ x ∂μ, x = a := by
    filter_upwards [hall] with x hx
    ext i
    apply Real.arctan_injective
    exact (hx i).trans (ha i).symm
  have hmap : Measure.map id μ = Measure.map (fun _ => a) μ := by
    apply Measure.map_congr
    exact hpoint
  have hdirac : μ = Measure.dirac a := by
    calc
      μ = Measure.map id μ := by rw [Measure.map_id]
      _ = Measure.map (fun _ => a) μ := hmap
      _ = Measure.dirac a := by rw [Measure.map_const, measure_univ, one_smul]
  exact hμ a hdirac

/-- A non-Dirac probability law has positive real variance in some bounded
coordinate arctangent. Boundedness supplies `MemLp`; thus the variance-zero
criterion is applied in its finite-moment regime. -/
theorem exists_arctan_coordinate_positive_variance {ι : Type*} [Fintype ι]
    [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ ≠ Measure.dirac a) :
    ∃ i, 0 < ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ ι => Real.arctan (x i)) μ := by
  obtain ⟨i, hnonconstant⟩ := exists_nonconstant_arctan_coordinate μ hμ
  let f : EuclideanSpace ℝ ι → ℝ := fun x => Real.arctan (x i)
  have hfMemLp : MemLp f 2 μ := by
    change MemLp (arctanCoordinate i) 2 μ
    exact arctanCoordinate_memLp i μ
  have hvariance_ne : ProbabilityTheory.variance f μ ≠ 0 := by
    intro hzero
    have hconstant :
        (fun x : EuclideanSpace ℝ ι => Real.arctan (x i)) =ᵐ[μ]
          fun _ => ∫ x, Real.arctan (x i) ∂μ := by
      filter_upwards
        [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hfMemLp hzero]
        with x hx
      exact hx
    exact hnonconstant (∫ x, Real.arctan (x i) ∂μ) hconstant
  refine ⟨i, lt_of_le_of_ne (ProbabilityTheory.variance_nonneg f μ)
    (Ne.symm hvariance_ne)⟩

/-- Every non-Dirac probability law admits a bounded globally smooth generator
with bounded gradient, finite second moment, and positive scalar variance. -/
theorem exists_bounded_smooth_generator_positive_variance {ι : Type*}
    [Fintype ι] [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (hμ : ∀ a, μ ≠ Measure.dirac a) :
    ∃ f : EuclideanSpace ℝ ι → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B ∧ ‖gradient f x‖ ≤ B) ∧
      MemLp f 2 μ ∧ 0 < ProbabilityTheory.variance f μ := by
  obtain ⟨i, hvariance⟩ := exists_arctan_coordinate_positive_variance μ hμ
  refine ⟨(fun x : EuclideanSpace ℝ ι => Real.arctan (x i)), ?_, ?_, ?_, hvariance⟩
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (arctanCoordinate i)
    exact arctanCoordinate_contDiff i
  · refine ⟨Real.pi + 1, by linarith [Real.pi_pos], ?_⟩
    change ∀ x, |arctanCoordinate i x| ≤ Real.pi + 1 ∧
      ‖gradient (arctanCoordinate i) x‖ ≤ Real.pi + 1
    intro x
    refine ⟨?_, ?_⟩
    · exact (arctanCoordinate_abs_bound i x).trans (by linarith [Real.pi_pos])
    · exact (arctanCoordinate_gradient_bound i x).trans (by linarith [Real.pi_pos])
  · change MemLp (arctanCoordinate i) 2 μ
    exact arctanCoordinate_memLp i μ

end LOOConcentration.Revision
