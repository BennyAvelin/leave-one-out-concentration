import LOOConcentrationRevision.FunctionalInequalities.MollifiedJointBound
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A positive mollification radius bounded by one and tending to zero. -/
noncomputable def mollificationRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- For a continuous input with the internally supplied segment estimate, the actual
clip-then-mollify smooth pairs converge strongly in the scalar `L²` coordinate to the clipped
input. The segment estimate and second moment are producer inputs; this is the scalar clause of
`step:revision:mollification-approximation`, not a closure of that full graph node. -/
theorem exists_scalar_strongL2_clipThenMollify {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (a b R : NNReal)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖))) :
    ∃ hclip : MemLp (clipFunction (R : ℝ) F) 2 μ,
      ∃ f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ),
        (∀ n, f n ∈ smoothSobolevPairs μ) ∧
        (∀ n, (WithLp.ofLp (f n)).1 =ᵐ[μ]
          clipThenMollify F R (mollificationRadius n)) ∧
        (∀ n, (WithLp.ofLp (f n)).2 =ᵐ[μ]
          gradient (clipThenMollify F R (mollificationRadius n))) ∧
        Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop
          (𝓝 (hclip.toLp (clipFunction (R : ℝ) F))) := by
  let η : ℕ → ℝ := mollificationRadius
  have hη : ∀ n, 0 < η n ∧ η n ≤ 1 := by
    intro n
    constructor
    · dsimp [η, mollificationRadius]
      positivity
    · dsimp [η, mollificationRadius]
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      nlinarith
  have hη_tendsto : Tendsto η atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hden
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) at hinv
    have hηeq : η = fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
      funext n
      simp [η, mollificationRadius]
    rw [hηeq]
    exact hinv

  have hclip : MemLp (clipFunction (R : ℝ) F) 2 μ :=
    MemLp.of_bound (continuous_clipFunction hF).aestronglyMeasurable (R : ℝ)
      (Eventually.of_forall fun x => by
        change |clipValue (R : ℝ) (F x)| ≤ (R : ℝ)
        exact abs_le.mpr (clipValue_bounds R.property))

  let f : ℕ → WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ) := fun n =>
    Classical.choose (exists_smooth_pair_clipThenMollify μ F hF R (η n) (hη n).1)
  have hf_spec (n : ℕ) :
      f n ∈ smoothSobolevPairs μ ∧
        (WithLp.ofLp (f n)).1 =ᵐ[μ] clipThenMollify F R (η n) ∧
        (WithLp.ofLp (f n)).2 =ᵐ[μ] gradient (clipThenMollify F R (η n)) := by
    exact Classical.choose_spec
      (exists_smooth_pair_clipThenMollify μ F hF R (η n) (hη n).1)

  let q : EuclideanSpace ℝ ι → ℝ := fun x =>
    (a : ℝ) + (b : ℝ) + (b : ℝ) * ‖x‖
  have hq : MemLp q 2 μ := memLp_affine_norm_of_second_moment μ hmoment a b
  let Q : Lp ℝ 2 μ := hq.toLp q
  have hq_nonneg (x : EuclideanSpace ℝ ι) : 0 ≤ q x := by
    dsimp [q]
    positivity

  have hsegF : HasLinearGrowthSegmentBound F (a : ℝ) (b : ℝ) := by
    intro x y
    simpa only [dist_eq_norm] using hseg x y
  have hsegClip : HasLinearGrowthSegmentBound (clipFunction (R : ℝ) F)
      (a : ℝ) (b : ℝ) := clipFunction_segmentBound hsegF

  have hErrorBound (n : ℕ) (x : EuclideanSpace ℝ ι) :
      |clipThenMollify F R (η n) x - clipFunction (R : ℝ) F x| ≤ η n * q x := by
    have hclose := clipThenMollify_close (f := F) (N := (R : ℝ))
      hF (hη n).1 hsegClip a.property b.property x
    have hfactor :
        (a : ℝ) + (b : ℝ) * ‖x‖ + (b : ℝ) * η n / 2 ≤ q x := by
      have hb0 : 0 ≤ (b : ℝ) := b.property
      have hbeta : (b : ℝ) * η n ≤ (b : ℝ) := by
        calc
          (b : ℝ) * η n ≤ (b : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hη n).2 hb0
          _ = (b : ℝ) := by ring
      dsimp [q]
      nlinarith [hbeta, hb0]
    exact hclose.trans (mul_le_mul_of_nonneg_left hfactor (hη n).1.le)

  have hnorm_bound (n : ℕ) :
      ‖(WithLp.ofLp (f n)).1 - hclip.toLp (clipFunction (R : ℝ) F)‖ ≤
        η n * ‖Q‖ := by
    calc
      ‖(WithLp.ofLp (f n)).1 - hclip.toLp (clipFunction (R : ℝ) F)‖ ≤
          ‖(η n) • Q‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [Lp.coeFn_sub (WithLp.ofLp (f n)).1
          (hclip.toLp (clipFunction (R : ℝ) F)),
          (hf_spec n).2.1, hclip.coeFn_toLp, hq.coeFn_toLp,
          Lp.coeFn_smul (η n) Q]
          with x hsub happrox htarget hmajorant hsmul
        rw [hsub]
        simp only [Pi.sub_apply]
        rw [happrox, htarget, hsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hmajorant]
        have hqbound := hErrorBound n x
        simpa [smul_eq_mul, Real.norm_eq_abs,
          abs_of_pos (hη n).1, abs_of_nonneg (hq_nonneg x)] using hqbound
      _ = η n * ‖Q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hη n).1]

  have hηQ : Tendsto (fun n => η n * ‖Q‖) atTop (𝓝 0) := by
    simpa using hη_tendsto.mul_const ‖Q‖
  have hstrong :
      Tendsto (fun n => (WithLp.ofLp (f n)).1) atTop
        (𝓝 (hclip.toLp (clipFunction (R : ℝ) F))) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ n in atTop, η n * ‖Q‖ < ε :=
      hηQ.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with n hn
    have hdist := hnorm_bound n
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hdist hn

  exact ⟨hclip, f, (fun n => (hf_spec n).1),
    (fun n => by simpa [η] using (hf_spec n).2.1),
    (fun n => by simpa [η] using (hf_spec n).2.2), hstrong⟩

end LOOConcentration.Revision
