import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bounded truncations of the squared dataset norm

This module records the smooth bounded approximation to the frozen dataset
squared norm used in the norm entropy argument.

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version).
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

/-- The bounded smooth truncation of the frozen squared dataset norm. -/
noncomputable def normTruncation {k m n : ℕ} (A : ℝ) (_hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) : ℝ :=
  A * (1 - Real.exp (-datasetNormSq D / A))

theorem normTruncation_nonneg {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    0 ≤ normTruncation A hA D := by
  unfold normTruncation
  have hS := datasetNormSq_nonneg D
  have hexp : Real.exp (-datasetNormSq D / A) ≤ 1 := by
    calc
      Real.exp (-datasetNormSq D / A) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hS) hA.le)
      _ = 1 := by simp
  nlinarith [hA]

theorem normTruncation_le {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    normTruncation A hA D ≤ A := by
  unfold normTruncation
  have hexp : 0 ≤ Real.exp (-datasetNormSq D / A) := (Real.exp_pos _).le
  nlinarith

theorem normTruncation_le_normSq {k m n : ℕ} {A : ℝ} (hA : 0 < A)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    normTruncation A hA D ≤ datasetNormSq D := by
  unfold normTruncation
  have hS := datasetNormSq_nonneg D
  have h := Real.add_one_le_exp (-(datasetNormSq D / A))
  have hmul : A * (1 - Real.exp (-datasetNormSq D / A)) ≤
      A * (datasetNormSq D / A) := by
    have h' : 1 - Real.exp (-datasetNormSq D / A) ≤ datasetNormSq D / A := by
      have heq : -datasetNormSq D / A = -(datasetNormSq D / A) := by ring
      rw [heq]
      linarith
    exact mul_le_mul_of_nonneg_left h' hA.le
  have hcancel : A * (datasetNormSq D / A) = datasetNormSq D := by
    field_simp
  rw [hcancel] at hmul
  exact hmul

theorem normTruncation_zero {k m n : ℕ} {A : ℝ} (hA : 0 < A) :
    normTruncation A hA (0 : Dataset (Observation (k + 1) (m + 1)) (n + 1)) = 0 := by
  simp [normTruncation, datasetNormSq, observationNormSq]

theorem normTruncation_contDiff {k m n : ℕ} (A : ℝ) (hA : 0 < A) :
    ContDiff ℝ ⊤ (normTruncation A hA :
      Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ) := by
  unfold normTruncation
  apply (contDiff_const.mul ?_)
  have hS : ContDiff ℝ ⊤
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) => datasetNormSq D) := by
    unfold datasetNormSq observationNormSq
    fun_prop
  exact contDiff_const.sub (Real.contDiff_exp.comp (hS.neg.div_const A))

end LOOConcentration
