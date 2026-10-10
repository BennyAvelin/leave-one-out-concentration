import LOOConcentration.Concentration.NormTruncation
import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Limits and slope estimates for the bounded squared-norm truncation

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version).
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

/-- The scale sequence `A_j = j + 1` applied to the bounded truncation. -/
noncomputable def normTruncationSequence {k m n : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) : ℕ → ℝ :=
  fun j => normTruncation ((j + 1 : ℕ) : ℝ) (by positivity) D

/-- The key scalar inequality behind the squared local-slope estimate. -/
theorem normTruncation_scalar_slope_ineq {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-2 * t) ≤ 1 - Real.exp (-t) := by
  have he : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have he0 : 1 ≤ Real.exp t := by
    exact le_trans (by linarith) he
  have hdiff : t ≤ Real.exp t - 1 := by linarith
  have hprod : t ≤ Real.exp t * (Real.exp t - 1) := by
    calc
      t ≤ Real.exp t - 1 := hdiff
      _ ≤ Real.exp t * (Real.exp t - 1) := by
        exact le_mul_of_one_le_left (by linarith) he0
  have hmul := mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg (-2 * t))
  have hcancel : Real.exp t * Real.exp (-2 * t) = Real.exp (-t) := by
    calc
      Real.exp t * Real.exp (-2 * t) = Real.exp (t + -2 * t) := by
        rw [← Real.exp_add]
      _ = Real.exp (-t) := by congr 1; ring
  have hfactor : (Real.exp t - 1) * Real.exp (-t) =
      1 - Real.exp (-t) := by
    have hprod' : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (Real.exp t - 1) * Real.exp (-t) =
          Real.exp t * Real.exp (-t) - Real.exp (-t) := by ring
      _ = 1 - Real.exp (-t) := by rw [hprod']
  calc
    t * Real.exp (-2 * t) ≤
        Real.exp t * (Real.exp t - 1) * Real.exp (-2 * t) := hmul
    _ = (Real.exp t - 1) * (Real.exp t * Real.exp (-2 * t)) := by ring
    _ = 1 - Real.exp (-t) := by rw [hcancel, hfactor]

/-- The one-exponential lower estimate used to pass to the pointwise limit. -/
theorem normTruncation_scalar_lower_ineq {t : ℝ} :
    t * Real.exp (-t) ≤ 1 - Real.exp (-t) := by
  have he : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have hprod : (1 + t) * Real.exp (-t) ≤ 1 := by
    calc
      (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

private noncomputable def normTruncationScalar (A t : ℝ) : ℝ :=
  A * (1 - Real.exp (-t / A))

private theorem normTruncationScalar_mono {t A B : ℝ}
    (ht : 0 ≤ t) (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    normTruncationScalar A t ≤ normTruncationScalar B t := by
  let x := t / A
  let y := t / B
  let z := x - y
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hxy : x = y + z := by dsimp [z]; ring
  have hzEq : z = t * (B - A) / (A * B) := by
    dsimp [x, y, z]
    field_simp [hA.ne', hB.ne']
  have hz : 0 ≤ z := by
    rw [hzEq]
    positivity
  have hAz : A * z = (B - A) * y := by
    dsimp [y, z, x]
    field_simp [hA.ne', hB.ne']
  have hy : y * Real.exp (-y) ≤ 1 - Real.exp (-y) :=
    normTruncation_scalar_lower_ineq
  have hzle : 1 - Real.exp (-z) ≤ z := by
    have h := Real.add_one_le_exp (-z)
    linarith
  have hcompare : A * Real.exp (-y) * (1 - Real.exp (-z)) ≤
      (B - A) * (1 - Real.exp (-y)) := by
    calc
      A * Real.exp (-y) * (1 - Real.exp (-z)) ≤
          A * Real.exp (-y) * z := by
        exact mul_le_mul_of_nonneg_left hzle
          (mul_nonneg hA.le (Real.exp_nonneg _))
      _ = (B - A) * (y * Real.exp (-y)) := by
        calc
          A * Real.exp (-y) * z = Real.exp (-y) * (A * z) := by ring
          _ = Real.exp (-y) * ((B - A) * y) := by rw [hAz]
          _ = (B - A) * (y * Real.exp (-y)) := by ring
      _ ≤ (B - A) * (1 - Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left hy hBA
  have hdiff :
      normTruncationScalar B t - normTruncationScalar A t =
        (B - A) * (1 - Real.exp (-y)) -
          A * Real.exp (-y) * (1 - Real.exp (-z)) := by
    unfold normTruncationScalar
    simp only [neg_div]
    rw [show t / B = y by rfl, show t / A = x by rfl]
    rw [hxy, neg_add, Real.exp_add]
    ring
  rw [← sub_nonneg, hdiff]
  exact sub_nonneg.mpr hcompare

/-- The prescribed sequence of truncations is pointwise nondecreasing. -/
theorem normTruncationSequence_monotone {k m n : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    Monotone (normTruncationSequence D) := by
  intro i j hij
  have hAi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
  have hAj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hAij : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hij 1
  have hS := datasetNormSq_nonneg D
  simpa [normTruncationSequence, normTruncation, normTruncationScalar] using
    (normTruncationScalar_mono hS hAi hAj hAij)

/-- A lower bound converging to the squared norm. -/
theorem normTruncation_lower_exp {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    datasetNormSq D * Real.exp (-datasetNormSq D / A) ≤ normTruncation A hA D := by
  have hS := datasetNormSq_nonneg D
  let t := datasetNormSq D / A
  have ht : 0 ≤ t := div_nonneg hS hA.le
  have hscalar := normTruncation_scalar_lower_ineq (t := t)
  have hmul := mul_le_mul_of_nonneg_left hscalar hA.le
  have hexp : -datasetNormSq D / A = -t := by dsimp [t]; ring
  unfold normTruncation
  rw [hexp]
  calc
    datasetNormSq D * Real.exp (-t) = A * (t * Real.exp (-t)) := by
      dsimp [t]
      field_simp [hA.ne']
    _ ≤ A * (1 - Real.exp (-t)) := hmul

/-- The truncations at integer scales converge pointwise to the frozen squared norm. -/
theorem normTruncationSequence_tendsto {k m n : ℕ}
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    Tendsto (normTruncationSequence D) atTop (𝓝 (datasetNormSq D)) := by
  let t := datasetNormSq D
  have ht : Tendsto (fun j : ℕ => t / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
  have hexp : Tendsto (fun j : ℕ => Real.exp (-(t / ((j + 1 : ℕ) : ℝ))))
      atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘ fun j : ℕ => -(t / ((j + 1 : ℕ) : ℝ)))
      atTop (𝓝 1)
    simpa only [neg_zero, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp ht.neg)
  have hlow : Tendsto (fun j : ℕ => t * Real.exp (-(t / ((j + 1 : ℕ) : ℝ))))
      atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.mul hexp
  have hhigh : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh
  · intro j
    have hA : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have hl := normTruncation_lower_exp hA D
    have heq : -datasetNormSq D / ((j + 1 : ℕ) : ℝ) =
        -(t / ((j + 1 : ℕ) : ℝ)) := by dsimp [t]; ring
    rw [heq] at hl
    simpa [normTruncationSequence, t] using hl
  · intro j
    have hA : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    exact normTruncation_le_normSq hA D

end LOOConcentration
