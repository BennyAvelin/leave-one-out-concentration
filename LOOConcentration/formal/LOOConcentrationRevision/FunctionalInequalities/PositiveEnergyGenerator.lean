import LOOConcentrationRevision.FunctionalInequalities.LogSobolevConstant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# A smooth generator with positive Sobolev energy

For a nonempty finite coordinate type, an arctangent of one coordinate is a
bounded smooth function with bounded, everywhere nonzero gradient. Its
Sobolev pair therefore belongs to the approved closure and has positive energy
under every probability law.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Gradient

namespace LOOConcentration.Revision

private noncomputable def arctanGenerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : EuclideanSpace ℝ ι → ℝ := fun x => Real.arctan (x i)

private theorem arctanGenerator_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x y : EuclideanSpace ℝ ι) :
    fderiv ℝ (arctanGenerator i) x y =
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

private theorem arctanGenerator_gradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : EuclideanSpace ℝ ι) :
    gradient (arctanGenerator i) x =
      (1 / (1 + (x i) ^ 2)) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  have h := inner_gradient_right (𝕜 := ℝ) (f := arctanGenerator i)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := x)
  rw [EuclideanSpace.inner_single_left] at h
  have hd := arctanGenerator_fderiv i x (EuclideanSpace.single j (1 : ℝ))
  rw [hd] at h
  simpa [PiLp.single_apply, eq_comm, mul_comm] using h

/-- A probability law on a nonempty finite Euclidean coordinate space has an
actual Sobolev pair of positive energy. -/
theorem positiveEnergyGenerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∃ u : SobolevPair μ, 0 < sobolevEnergy μ u := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  let f := arctanGenerator i
  let p : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i
  let B : ℝ := Real.pi + 1
  have hfContDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.arctan ∘ p)
    exact Real.contDiff_arctan.comp p.contDiff
  have hfContinuous : Continuous f := hfContDiff.continuous
  have hgradientFormula : gradient f =
      fun x => (1 / (1 + (x i) ^ 2)) • EuclideanSpace.single i (1 : ℝ) := by
    funext x
    exact arctanGenerator_gradient i x
  have hgradientContinuous : Continuous (gradient f) := by
    rw [hgradientFormula]
    have hdenContinuous : Continuous (fun x : EuclideanSpace ℝ ι => 1 + (x i) ^ 2) := by
      fun_prop
    have hdenNeZero : ∀ x : EuclideanSpace ℝ ι, 1 + (x i) ^ 2 ≠ 0 := by
      intro x
      positivity
    simp only [one_div]
    change Continuous
      ((fun x : EuclideanSpace ℝ ι => 1 + (x i) ^ 2)⁻¹ •
        (fun _ : EuclideanSpace ℝ ι => EuclideanSpace.single i (1 : ℝ)))
    exact (hdenContinuous.inv₀ hdenNeZero).smul continuous_const
  have hscalarBound : ∀ x, |f x| ≤ Real.pi / 2 := by
    intro x
    exact abs_le.mpr ⟨(Real.arctan_mem_Ioo (x i)).1.le,
      (Real.arctan_mem_Ioo (x i)).2.le⟩
  have hcoefficientNonneg (x : EuclideanSpace ℝ ι) :
      0 ≤ 1 / (1 + (x i) ^ 2) := by
    positivity
  have hcoefficientLeOne (x : EuclideanSpace ℝ ι) :
      1 / (1 + (x i) ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + (x i) ^ 2)]
    nlinarith [sq_nonneg (x i)]
  have hgradientBound : ∀ x, ‖gradient f x‖ ≤ 1 := by
    intro x
    rw [hgradientFormula]
    simp only [norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs,
      abs_of_nonneg (hcoefficientNonneg x), mul_one]
    exact hcoefficientLeOne x
  have hgradientPositive : ∀ x, 0 < ‖gradient f x‖ := by
    intro x
    rw [hgradientFormula]
    simp only [norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (1 + (x i) ^ 2)), mul_one]
    positivity
  have hfunctionBound : ∀ x, |f x| ≤ B := by
    intro x
    dsimp [B]
    exact (hscalarBound x).trans (by linarith [Real.pi_pos])
  have hgradientBoundB : ∀ x, ‖gradient f x‖ ≤ B := by
    intro x
    dsimp [B]
    exact (hgradientBound x).trans (by linarith [Real.pi_pos])
  have hfMemLp : MemLp f 2 μ :=
    MemLp.of_bound hfContinuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hfunctionBound x)
  have hgradientMemLp : MemLp (gradient f) 2 μ :=
    MemLp.of_bound hgradientContinuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall hgradientBoundB)
  let v : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ) :=
    WithLp.toLp 2 (hfMemLp.toLp f, hgradientMemLp.toLp (gradient f))
  have hv : v ∈ smoothSobolevPairs μ := by
    refine ⟨f, hfContDiff, ⟨B, ?_, ?_⟩, ⟨hfMemLp, hgradientMemLp, rfl⟩⟩
    · dsimp [B]
      linarith [Real.pi_pos]
    · intro x
      exact ⟨hfunctionBound x, hgradientBoundB x⟩
  let u : SobolevPair μ := ⟨v, subset_closure hv⟩
  refine ⟨u, ?_⟩
  apply pos_iff_ne_zero.mpr
  intro henergyZero
  have hgradientLpZero : (WithLp.ofLp u.val).2 = 0 :=
    (sobolevEnergy_eq_zero_iff u).mp henergyZero
  have hLpZero : hgradientMemLp.toLp (gradient f) = 0 := by
    simpa [u, v] using hgradientLpZero
  have hzeroAe : hgradientMemLp.toLp (gradient f) =ᵐ[μ] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp hLpZero
  have hgradientZeroAe : gradient f =ᵐ[μ] 0 := by
    filter_upwards [hgradientMemLp.coeFn_toLp, hzeroAe] with x hrep hz
    rw [← hrep]
    exact hz
  have hgradientPointNe : ∀ x, gradient f x ≠ 0 := by
    intro x hz
    simpa [hz] using hgradientPositive x
  have hbad : μ {x | ¬ gradient f x = (0 : EuclideanSpace ℝ ι)} = 0 :=
    (ae_iff).mp hgradientZeroAe
  have hbadSet : {x | ¬ gradient f x = (0 : EuclideanSpace ℝ ι)} = Set.univ := by
    ext x
    simp [hgradientPointNe x]
  rw [hbadSet, measure_univ] at hbad
  norm_num at hbad

/-- The generator witnesses the positive-energy hypothesis needed to invoke the
existing log-Sobolev estimate. -/
theorem positiveEnergyGenerator_lsi_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∃ u : SobolevPair μ,
      0 < sobolevEnergy μ u ∧
        squareEntropy μ (WithLp.ofLp u.val).1 ≤
          2 * logSobolevConstant μ * sobolevEnergy μ u := by
  obtain ⟨u, hu⟩ := positiveEnergyGenerator μ
  exact ⟨u, hu, squareEntropy_le_of_energy_pos u hu⟩

end LOOConcentration.Revision
