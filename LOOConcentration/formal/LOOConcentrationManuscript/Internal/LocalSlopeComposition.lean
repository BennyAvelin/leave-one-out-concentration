import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.EMetricSpace.Lipschitz
import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean

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

private noncomputable def localSlopeQuotient {r : ℕ} {β : Type*} [NormedAddCommGroup β]
    (g : EuclideanSpace ℝ (Fin (r + 1)) → β)
    (D : EuclideanSpace ℝ (Fin (r + 1))) (A : EuclideanSpace ℝ (Fin (r + 1))) : ℝ :=
  ‖g A - g D‖ / ‖A - D‖

private theorem localSlopeQuotient_bounded {r : ℕ}
    {β : Type*} [NormedAddCommGroup β]
    (g : EuclideanSpace ℝ (Fin (r + 1)) → β)
    (hg : LocallyLipschitz g) (D : EuclideanSpace ℝ (Fin (r + 1))) :
    ∃ K : NNReal, ∀ᶠ A in 𝓝[≠] D, localSlopeQuotient g D A ≤ (K : ℝ) := by
  obtain ⟨K, t, ht, hK⟩ := hg D
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hD : D ∈ t := hball (Metric.mem_ball_self hε)
  refine ⟨K, ?_⟩
  have ht' : ∀ᶠ A in 𝓝 D, A ∈ t := ht
  have htF : ∀ᶠ A in 𝓝[≠] D, A ∈ t := ht'.filter_mono nhdsWithin_le_nhds
  filter_upwards [htF] with A hA
  by_cases hAD : A = D
  · simp [localSlopeQuotient, hAD]
  · have hdist : ‖g A - g D‖ ≤ (K : ℝ) * ‖A - D‖ := by
      have h := hK.dist_le_mul A hA D hD
      simpa only [dist_eq_norm] using h
    have hden : 0 < ‖A - D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAD)
    dsimp [localSlopeQuotient]
    exact (div_le_iff₀ hden).2 hdist

private theorem localSlopeQuotient_nonneg {r : ℕ}
    {β : Type*} [NormedAddCommGroup β]
    (g : EuclideanSpace ℝ (Fin (r + 1)) → β)
    (D A : EuclideanSpace ℝ (Fin (r + 1))) :
    0 ≤ localSlopeQuotient g D A :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- A local Lipschitz bound on the outer map controls the punctured local slope
of a composition by the corresponding local slope of its inner map. -/
theorem local_slope_comp_le
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (r : ℕ)
    (g : EuclideanSpace ℝ (Fin (r + 1)) → β)
    (hg : LocallyLipschitz g)
    (f : β → ℝ)
    (D : EuclideanSpace ℝ (Fin (r + 1)))
    (L : NNReal) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : LipschitzOnWith L f (Metric.ball (g D) ρ)) :
    limsup (fun A : EuclideanSpace ℝ (Fin (r + 1)) =>
      |f (g A) - f (g D)| / ‖A - D‖) (𝓝[≠] D) ≤
      (L : ℝ) * limsup (localSlopeQuotient g D) (𝓝[≠] D) := by
  let q : EuclideanSpace ℝ (Fin (r + 1)) → ℝ := localSlopeQuotient g D
  let qf : EuclideanSpace ℝ (Fin (r + 1)) → ℝ := fun A =>
    |f (g A) - f (g D)| / ‖A - D‖
  let F := 𝓝[≠] D
  have hqBoundExists := localSlopeQuotient_bounded g hg D
  obtain ⟨K, hqBound⟩ := hqBoundExists
  have hqFilterBound : F.IsBoundedUnder (· ≤ ·) q := ⟨(K : ℝ), hqBound⟩
  have hqNonneg : ∀ A, 0 ≤ q A := by
    intro A
    exact localSlopeQuotient_nonneg g D A
  have hnear : ∀ᶠ A in (𝓝 D), g A ∈ Metric.ball (g D) ρ := by
    exact (hg.continuous.continuousAt).eventually (Metric.ball_mem_nhds _ hρ)
  have hnearF : ∀ᶠ A in F, g A ∈ Metric.ball (g D) ρ :=
    hnear.filter_mono nhdsWithin_le_nhds
  have hpoint : ∀ᶠ A in F, qf A ≤ (L : ℝ) * q A := by
    filter_upwards [hnearF] with A hA
    by_cases hAD : A = D
    · simp [qf, q, localSlopeQuotient, hAD]
    · have hout : |f (g A) - f (g D)| ≤ (L : ℝ) * ‖g A - g D‖ := by
        have h := hf.dist_le_mul (g A) hA (g D) (Metric.mem_ball_self hρ)
        simpa only [dist_eq_norm, Real.norm_eq_abs] using h
      have hden : 0 < ‖A - D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAD)
      dsimp [qf, q, localSlopeQuotient]
      calc
        |f (g A) - f (g D)| / ‖A - D‖ ≤
            ((L : ℝ) * ‖g A - g D‖) / ‖A - D‖ := div_le_div_of_nonneg_right hout (norm_nonneg _)
        _ = (L : ℝ) * (‖g A - g D‖ / ‖A - D‖) := by ring
  have hqfBound : F.IsBoundedUnder (· ≤ ·) qf := by
    refine ⟨(L : ℝ) * (K : ℝ), ?_⟩
    change ∀ᶠ A in F, qf A ≤ (L : ℝ) * (K : ℝ)
    filter_upwards [hpoint, hqBound] with A hA hq
    exact hA.trans (mul_le_mul_of_nonneg_left hq (NNReal.coe_nonneg L))
  have hqfNonneg : ∀ A, 0 ≤ qf A := by
    intro A
    exact div_nonneg (abs_nonneg _) (norm_nonneg _)
  have hqfCobound : F.IsCoboundedUnder (· ≤ ·) qf := by
    change (Filter.map qf F).IsCobounded (· ≤ ·)
    refine ⟨0, ?_⟩
    intro a ha
    have hqa : ∀ᶠ A in F, qf A ≤ a := by
      simpa only [Filter.eventually_map] using ha
    have hzero : ∀ᶠ A in F, 0 ≤ qf A := Filter.Eventually.of_forall hqfNonneg
    have hconst : ∀ᶠ A in F, 0 ≤ a :=
      (hzero.and hqa).mono fun _ ⟨hzeroA, hqaA⟩ => hzeroA.trans hqaA
    obtain ⟨A, hA⟩ := @Filter.Eventually.exists _ _ _ (by infer_instance : NeBot F) hconst
    exact hA
  have hconstantBound : F.IsBoundedUnder (· ≤ ·)
      (fun _ : EuclideanSpace ℝ (Fin (r + 1)) => (L : ℝ)) :=
    ⟨(L : ℝ), by
      change ∀ᶠ A in F, (L : ℝ) ≤ (L : ℝ)
      exact Filter.Eventually.of_forall fun _ => le_rfl⟩
  have hqNonnegEvent : 0 ≤ᶠ[F] q := Filter.Eventually.of_forall hqNonneg
  have hmulLimsup : limsup (fun A => (L : ℝ) * q A) F ≤ (L : ℝ) * limsup q F := by
    have hmul := limsup_mul_le
      (Filter.Frequently.of_forall fun _ => NNReal.coe_nonneg L)
      hconstantBound hqNonnegEvent hqFilterBound
    have hfun : (fun A => (L : ℝ) * q A) = (fun _ => (L : ℝ)) * q := by
      funext A
      rfl
    rw [hfun]
    simpa only [Filter.limsup_const] using hmul
  have hproductBound : F.IsBoundedUnder (· ≤ ·) (fun A => (L : ℝ) * q A) := by
    refine ⟨(L : ℝ) * (K : ℝ), ?_⟩
    change ∀ᶠ A in F, (L : ℝ) * q A ≤ (L : ℝ) * (K : ℝ)
    filter_upwards [hqBound] with A hq
    exact mul_le_mul_of_nonneg_left hq (NNReal.coe_nonneg L)
  have hlimsup : limsup qf F ≤ (L : ℝ) * limsup q F := by
    apply (Filter.limsup_le_iff hqfCobound hqfBound).2
    intro a ha
    have hprod : ∀ᶠ A in F, (L : ℝ) * q A < a :=
      eventually_lt_of_limsup_lt (hmulLimsup.trans_lt ha) hproductBound
    filter_upwards [hpoint, hprod] with A hA hprodA
    exact hA.trans_lt hprodA
  simpa only [qf, q, F, localSlopeQuotient] using hlimsup

/-- The square loss has the exact local-slope chain bound, including at points
where its outer derivative vanishes. -/
theorem local_slope_square_loss_le
    (r : ℕ) (g : EuclideanSpace ℝ (Fin (r + 1)) → ℝ)
    (hg : LocallyLipschitz g) (y : ℝ) (D : EuclideanSpace ℝ (Fin (r + 1))) :
    limsup (fun A : EuclideanSpace ℝ (Fin (r + 1)) =>
      |(g A - y) ^ 2 - (g D - y) ^ 2| / ‖A - D‖) (𝓝[≠] D) ≤
      2 * |g D - y| * limsup (fun A : EuclideanSpace ℝ (Fin (r + 1)) =>
        |g A - g D| / ‖A - D‖) (𝓝[≠] D) := by
  let q : EuclideanSpace ℝ (Fin (r + 1)) → ℝ := fun A => |g A - g D| / ‖A - D‖
  let qsq : EuclideanSpace ℝ (Fin (r + 1)) → ℝ := fun A =>
    |(g A - y) ^ 2 - (g D - y) ^ 2| / ‖A - D‖
  let F := 𝓝[≠] D
  obtain ⟨K, hqBound⟩ := localSlopeQuotient_bounded g hg D
  have hqNonneg : ∀ A, 0 ≤ q A := by
    intro A
    exact div_nonneg (abs_nonneg _) (norm_nonneg _)
  have hqCobound : F.IsCoboundedUnder (· ≤ ·) q := by
    change (Filter.map q F).IsCobounded (· ≤ ·)
    refine ⟨0, ?_⟩
    intro a ha
    have hqa : ∀ᶠ A in F, q A ≤ a := by
      simpa only [Filter.eventually_map] using ha
    have hzero : ∀ᶠ A in F, 0 ≤ q A := Filter.Eventually.of_forall hqNonneg
    have hconst : ∀ᶠ A in F, 0 ≤ a :=
      (hzero.and hqa).mono fun _ ⟨hzeroA, hqaA⟩ => hzeroA.trans hqaA
    obtain ⟨A, hA⟩ := @Filter.Eventually.exists _ _ _ (by infer_instance : NeBot F) hconst
    exact hA
  have hqFilterBound : F.IsBoundedUnder (· ≤ ·) q := ⟨(K : ℝ), hqBound⟩
  have hqLimsup : limsup q F ≤ (K : ℝ) := by
    apply (Filter.limsup_le_iff hqCobound hqFilterBound).2
    intro a ha
    exact hqBound.mono fun _ hA => hA.trans_lt ha
  have hmain : limsup qsq F ≤ 2 * |g D - y| * limsup q F := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    -- The fixed-radius estimate above gives an error at most one; rescale its radius to δ.
    have hsmall : ∀ ρ : ℝ, 0 < ρ →
        limsup qsq F ≤ 2 * (|g D - y| + ρ) * limsup q F := by
      intro ρ hρ
      let L : NNReal := Real.toNNReal (2 * (|g D - y| + ρ))
      have hconst : (L : ℝ) = 2 * (|g D - y| + ρ) := by
        dsimp [L]
        exact Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * (|g D - y| + ρ))
      have houter : LipschitzOnWith L (fun x : ℝ => (x - y) ^ 2)
          (Metric.ball (g D) ρ) := by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx z hz
        have hxball : |x - g D| < ρ := by
          have hdist := Metric.mem_ball.mp hx
          simpa only [Real.dist_eq] using hdist
        have hzball : |z - g D| < ρ := by
          have hdist := Metric.mem_ball.mp hz
          simpa only [Real.dist_eq] using hdist
        have hxbound : |x - y| ≤ |g D - y| + ρ := by
          calc
            |x - y| ≤ |x - g D| + |g D - y| := abs_sub_le x (g D) y
          _ = |g D - y| + |x - g D| := by ring
          _ ≤ |g D - y| + ρ := add_le_add_right hxball.le _
        have hzbound : |z - y| ≤ |g D - y| + ρ := by
          calc
            |z - y| ≤ |z - g D| + |g D - y| := abs_sub_le z (g D) y
          _ = |g D - y| + |z - g D| := by ring
          _ ≤ |g D - y| + ρ := add_le_add_right hzball.le _
        have hfactor : |x + z - 2 * y| ≤ 2 * (|g D - y| + ρ) := by
          calc
            |x + z - 2 * y| = |(x - y) + (z - y)| := by congr 1; ring
            _ ≤ |x - y| + |z - y| := abs_add_le _ _
            _ ≤ (|g D - y| + ρ) + (|g D - y| + ρ) := add_le_add hxbound hzbound
            _ = 2 * (|g D - y| + ρ) := by ring
        have hfact : |(x - y) ^ 2 - (z - y) ^ 2| =
            |x - z| * |x + z - 2 * y| := by
          rw [← abs_mul]
          congr 1; ring
        have hineq : |(x - y) ^ 2 - (z - y) ^ 2| ≤
            (2 * (|g D - y| + ρ)) * |x - z| := by
          rw [hfact]
          calc
            |x - z| * |x + z - 2 * y| ≤
                |x - z| * (2 * (|g D - y| + ρ)) :=
                  mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
            _ = (2 * (|g D - y| + ρ)) * |x - z| := by ring
        simpa only [Real.dist_eq, hconst] using hineq
      have hcomp := local_slope_comp_le r g hg (fun x : ℝ => (x - y) ^ 2) D L ρ hρ houter
      have hqEq : localSlopeQuotient g D = q := by
        funext A
        simp [q, localSlopeQuotient, Real.norm_eq_abs]
      rw [hqEq] at hcomp
      simpa only [qsq, F, hconst] using hcomp
    let ρ : ℝ := δ / (2 * ((K : ℝ) + 1))
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρid : 2 * ρ * ((K : ℝ) + 1) = δ := by
      dsimp [ρ]
      field_simp
    have hρbound : 2 * ρ * limsup q F ≤ δ := by
      calc
        2 * ρ * limsup q F ≤ 2 * ρ * (K : ℝ) :=
          mul_le_mul_of_nonneg_left hqLimsup (by positivity)
        _ ≤ 2 * ρ * ((K : ℝ) + 1) := by gcongr; linarith
        _ = δ := hρid
    calc
      limsup qsq F ≤ 2 * (|g D - y| + ρ) * limsup q F := hsmall ρ hρ
      _ = 2 * |g D - y| * limsup q F + 2 * ρ * limsup q F := by ring
      _ ≤ 2 * |g D - y| * limsup q F + δ := add_le_add_right hρbound _
  simpa only [qsq, q, F] using hmain

/-- At a differentiability point, the actual gradient of square loss is given
by the chain rule. The local-slope estimate above does not assume this premise. -/
theorem gradient_square_loss_chain_rule
    (r : ℕ) (g : EuclideanSpace ℝ (Fin (r + 1)) → ℝ)
    (y : ℝ) (D : EuclideanSpace ℝ (Fin (r + 1)))
    (hg : DifferentiableAt ℝ g D) :
    gradient (fun A : EuclideanSpace ℝ (Fin (r + 1)) => (g A - y) ^ 2) D =
      (2 * (g D - y)) • gradient g D := by
  have hsub : HasFDerivAt (fun A : EuclideanSpace ℝ (Fin (r + 1)) => g A - y)
      (fderiv ℝ g D) D := hg.hasFDerivAt.sub_const y
  have hpow := hsub.pow 2
  have hderiv := hpow.fderiv
  have hderiv' : fderiv ℝ (fun A : EuclideanSpace ℝ (Fin (r + 1)) =>
      (g A - y) ^ 2) D = (2 * (g D - y)) • fderiv ℝ g D := by
    rw [hderiv]
    norm_num [smul_smul]
  let R := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))
  calc
    gradient (fun A : EuclideanSpace ℝ (Fin (r + 1)) => (g A - y) ^ 2) D =
        R.symm (fderiv ℝ (fun A : EuclideanSpace ℝ (Fin (r + 1)) =>
          (g A - y) ^ 2) D) := rfl
    _ = R.symm ((2 * (g D - y)) • fderiv ℝ g D) := by rw [hderiv']
    _ = (2 * (g D - y)) • R.symm (fderiv ℝ g D) := map_smul R.symm _ _
    _ = (2 * (g D - y)) • gradient g D := rfl

end LOOConcentration.Manuscript.Internal
