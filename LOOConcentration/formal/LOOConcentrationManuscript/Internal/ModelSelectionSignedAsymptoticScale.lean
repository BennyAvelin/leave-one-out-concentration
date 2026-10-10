import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open Filter
open scoped Topology

/-- The common numeric Gaussian constant for the simplified asymptotic scale.
It depends only on the three rate bounds. -/
noncomputable def modelSelectionSignedGaussianConstant (C A B : NNReal) : ℝ :=
  1 / (8 * ((C : ℝ) * (3 * (A : ℝ) + (B : ℝ)) ^ 2 + 1))

theorem modelSelectionSignedGaussianConstant_pos (C A B : NNReal) :
    0 < modelSelectionSignedGaussianConstant C A B := by
  dsimp [modelSelectionSignedGaussianConstant]
  positivity

private theorem sq_le_sq_of_nonneg_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx)
  nlinarith only [hprod]

/-- A numeric Gaussian proxy estimate for the common simplified rate. The
zero-variance branch is literal, so it also covers `C = 0` and `s = 0`. -/
theorem modelSelection_signed_gaussian_proxy_bound
    (C A B : NNReal) (n : ℕ) (s ε δ : ℝ)
    (hs_nonneg : 0 ≤ s)
    (hs_bound : s ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) +
      (B : ℝ) / Real.sqrt (n + 2 : ℝ) +
      (A : ℝ) / Real.sqrt (n + 2 : ℝ))
    (hε : 0 < ε) (hδ : δ < ε / 2) :
    (if (C : ℝ) * s ^ 2 = 0 then 0 else
      Real.exp (-((ε - δ) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant C A B * ε ^ 2 *
          (n + 2 : ℝ))) := by
  let q : ℝ := (n + 2 : ℝ)
  let S : ℝ := 3 * (A : ℝ) + (B : ℝ)
  let K : ℝ := (C : ℝ) * S ^ 2
  let V : ℝ := (C : ℝ) * s ^ 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hroot : Real.sqrt (n + 2 : ℝ) ≤ 2 * Real.sqrt (n + 1 : ℝ) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hsq : (n + 2 : ℝ) ≤ (2 * Real.sqrt (n + 1 : ℝ)) ^ 2 := by
      nlinarith only [hsquare, hn]
    have hroot' := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hroot'
    exact hroot'
  have hratio : 1 / Real.sqrt (n + 1 : ℝ) ≤
      2 / Real.sqrt (n + 2 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa using hroot
  have hA_bound : (A : ℝ) / Real.sqrt (n + 1 : ℝ) ≤
      2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
    calc
      (A : ℝ) / Real.sqrt (n + 1 : ℝ) =
          (A : ℝ) * (1 / Real.sqrt (n + 1 : ℝ)) := by ring
      _ ≤ (A : ℝ) * (2 / Real.sqrt (n + 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by ring
  have hs_upper : s ≤ S / Real.sqrt q := by
    dsimp [S, q]
    calc
      s ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) +
          (B : ℝ) / Real.sqrt (n + 2 : ℝ) +
          (A : ℝ) / Real.sqrt (n + 2 : ℝ) := hs_bound
      _ ≤ 2 * (A : ℝ) / Real.sqrt (n + 2 : ℝ) +
          (B : ℝ) / Real.sqrt (n + 2 : ℝ) +
          (A : ℝ) / Real.sqrt (n + 2 : ℝ) := by
        linarith only [hA_bound]
      _ = (3 * (A : ℝ) + (B : ℝ)) / Real.sqrt (n + 2 : ℝ) := by ring
  have hscale : s ^ 2 ≤ S ^ 2 / q := by
    calc
      s ^ 2 ≤ (S / Real.sqrt q) ^ 2 :=
        sq_le_sq_of_nonneg_le hs_nonneg hs_upper
      _ = S ^ 2 / q := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hq)]
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hV_scale : V ≤ K / q := by
    dsimp [V, K]
    calc
      (C : ℝ) * s ^ 2 ≤ (C : ℝ) * (S ^ 2 / q) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = ((C : ℝ) * S ^ 2) / q := by ring
  have hVq : V * q ≤ K := (le_div_iff₀ hq).mp hV_scale
  have hKplus : 0 < K + 1 := by
    dsimp [K]
    positivity
  have hεδ : 0 < ε - δ := by
    linarith
  have hεsquare : (ε / 2) ^ 2 ≤ (ε - δ) ^ 2 :=
    sq_le_sq_of_nonneg_le (by positivity) (by linarith)
  by_cases hVzero : V = 0
  · have hVeq : (C : ℝ) * s ^ 2 = V := rfl
    rw [hVeq, if_pos hVzero]
    exact Real.exp_nonneg _
  · have hVpos : 0 < V := lt_of_le_of_ne hV_nonneg (Ne.symm hVzero)
    have hfactor : q / (K + 1) ≤ 1 / V := by
      apply (div_le_div_iff₀ hKplus hVpos).2
      calc
        q * V = V * q := by ring
        _ ≤ K := hVq
        _ ≤ K + 1 := le_add_of_nonneg_right (by norm_num)
        _ = 1 * (K + 1) := by ring
    have hεcoeff : ε ^ 2 / 8 ≤ (ε - δ) ^ 2 / 2 := by
      nlinarith only [hεsquare]
    have harg : modelSelectionSignedGaussianConstant C A B * ε ^ 2 * q ≤
        (ε - δ) ^ 2 / (2 * V) := by
      calc
        modelSelectionSignedGaussianConstant C A B * ε ^ 2 * q =
            (ε ^ 2 / 8) * (q / (K + 1)) := by
          dsimp [modelSelectionSignedGaussianConstant, K, S]
          field_simp [hKplus.ne']
        _ ≤ (ε ^ 2 / 8) * (1 / V) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = (ε ^ 2 / 8) / V := by ring
        _ ≤ ((ε - δ) ^ 2 / 2) / V :=
          div_le_div_of_nonneg_right hεcoeff (le_of_lt hVpos)
        _ = (ε - δ) ^ 2 / (2 * V) := by ring
    have hDen : 2 * (C : ℝ) * s ^ 2 = 2 * V := by
      dsimp [V]
      ring
    have hExp : Real.exp (-((ε - δ) ^ 2 / (2 * V))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant C A B * ε ^ 2 * q)) :=
      Real.exp_le_exp.mpr (neg_le_neg harg)
    have hExp' : Real.exp (-((ε - δ) ^ 2 / (2 * (C : ℝ) * s ^ 2))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant C A B * ε ^ 2 * q)) := by
      simpa only [hDen] using hExp
    have hVeq : (C : ℝ) * s ^ 2 = V := rfl
    simpa only [hVeq, if_neg hVzero, q] using hExp'

/-- A single constant works for every rate sequence, bias sequence, and
positive deviation. Only the bias convergence determines the eventual index. -/
theorem modelSelection_signed_gaussian_proxy_eventually :
    ∀ (C A B : NNReal), ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (s δ₃ : ℕ → ℝ),
        (∀ n, 0 ≤ s n ∧ s n ≤
          (A : ℝ) / Real.sqrt (n + 1 : ℝ) +
            (B : ℝ) / Real.sqrt (n + 2 : ℝ) +
            (A : ℝ) / Real.sqrt (n + 2 : ℝ)) →
        Tendsto (fun n => δ₃ (n + 2)) atTop (nhds 0) →
        ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
          (if (C : ℝ) * (s n) ^ 2 = 0 then 0 else
            Real.exp (-((ε - δ₃ (n + 2)) ^ 2 /
              (2 * (C : ℝ) * (s n) ^ 2)))) ≤
                Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
  intro C A B
  let c₀ := modelSelectionSignedGaussianConstant C A B
  refine ⟨c₀, modelSelectionSignedGaussianConstant_pos C A B, ?_⟩
  intro s δ₃ hs hδ₃ ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  have hsmall : ∀ᶠ n : ℕ in atTop, δ₃ (n + 2) < ε / 2 :=
    hδ₃.eventually (Iio_mem_nhds hεhalf)
  obtain ⟨nε, hnε⟩ := eventually_atTop.1 hsmall
  refine ⟨nε, ?_⟩
  intro n hn
  exact modelSelection_signed_gaussian_proxy_bound C A B n (s n) ε
    (δ₃ (n + 2)) (hs n).1 (hs n).2 hε (hnε n hn)

/-- Endpoint smoke declaration: a zero variance proxy is interpreted literally
as zero even when the other rate bounds are nonzero. -/
theorem modelSelection_signed_gaussian_proxy_C_zero
    (A B : NNReal) (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : δ < ε / 2) :
    (if (0 : ℝ) * (0 : ℝ) ^ 2 = 0 then 0 else
      Real.exp (-((ε - δ) ^ 2 / (2 * (0 : ℝ) * (0 : ℝ) ^ 2)))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant 0 A B * ε ^ 2 *
          (n + 2 : ℝ))) := by
  exact modelSelection_signed_gaussian_proxy_bound 0 A B n 0 ε δ
    (by norm_num) (by positivity) hε hδ

/-- Endpoint smoke declaration: zero scale uses the same zero-proxy branch. -/
theorem modelSelection_signed_gaussian_proxy_s_zero
    (C A B : NNReal) (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : δ < ε / 2) :
    (if (C : ℝ) * (0 : ℝ) ^ 2 = 0 then 0 else
      Real.exp (-((ε - δ) ^ 2 / (2 * (C : ℝ) * (0 : ℝ) ^ 2)))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant C A B * ε ^ 2 *
          (n + 2 : ℝ))) := by
  exact modelSelection_signed_gaussian_proxy_bound C A B n 0 ε δ
    (by norm_num) (by positivity) hε hδ

/-- Endpoint smoke declaration: when both asymptotic rate bounds vanish, every
admissible nonnegative scale is zero. -/
theorem modelSelection_signed_gaussian_proxy_all_rate_bounds_zero
    (C : NNReal) (n : ℕ) (s ε δ : ℝ)
    (hs : 0 ≤ s)
    (hs_bound : s ≤ (0 : ℝ) / Real.sqrt (n + 1 : ℝ) +
      (0 : ℝ) / Real.sqrt (n + 2 : ℝ) +
      (0 : ℝ) / Real.sqrt (n + 2 : ℝ))
    (hε : 0 < ε) (hδ : δ < ε / 2) :
    (if (C : ℝ) * s ^ 2 = 0 then 0 else
      Real.exp (-((ε - δ) ^ 2 / (2 * (C : ℝ) * s ^ 2)))) ≤
        Real.exp (-(modelSelectionSignedGaussianConstant C 0 0 * ε ^ 2 *
          (n + 2 : ℝ))) := by
  exact modelSelection_signed_gaussian_proxy_bound C 0 0 n s ε δ hs hs_bound hε hδ

end LOOConcentration.Manuscript.Internal
