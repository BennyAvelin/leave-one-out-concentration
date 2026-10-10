import LOOConcentrationRevision.FunctionalInequalities.GradientSegment
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory Set Filter

open scoped Gradient

/-- A volume-a.e. linear growth bound on the actual gradient gives the sharp
all-pairs segment estimate for a locally Lipschitz function. -/
theorem ae_gradient_segment_estimate_of_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F w ∧ ‖gradient F w‖ ≤ (a : ℝ) + (b : ℝ) * ‖w‖)
    (x y : EuclideanSpace ℝ ι) :
    |F x - F y| ≤ ‖x - y‖ * ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)) := by
  let A : ℝ := (a : ℝ)
  let B : ℝ := (b : ℝ)
  let v : EuclideanSpace ℝ ι := y - x
  let path (z : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
    (1 - t) • x + t • y + z
  let affine (z : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
    x + z + t • v
  let g (z : EuclideanSpace ℝ ι) : ℝ → ℝ := fun t => F (path z t)

  have hB : 0 ≤ B := b.2
  have hpath (z : EuclideanSpace ℝ ι) (t : ℝ) : path z t = affine z t := by
    dsimp [path, affine, v]
    simp only [sub_smul, one_smul, smul_sub]
    abel

  have hshift := ae_shifted_segment_of_ae
    (fun w : EuclideanSpace ℝ ι => DifferentiableAt ℝ F w ∧
      ‖gradient F w‖ ≤ A + B * ‖w‖)
    (by simpa only [A, B] using hgrad) x y

  have hgood : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        DifferentiableAt ℝ F (path z t) ∧
          ‖gradient F (path z t)‖ ≤ A + B * ‖path z t‖ := by
    simpa only [A, B, path] using hshift

  have hbound : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)),
      |F (y + z) - F (x + z)| ≤
        ‖y - x‖ * (A + B / 2 * (‖x‖ + ‖y‖) + B * ‖z‖) := by
    filter_upwards [hgood] with z hz
    have hgamma_lip : LipschitzWith ‖v‖₊ (affine z) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro s t
      have hdiff : affine z s - affine z t = (s - t) • v := by
        dsimp [affine]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
      rw [dist_eq_norm, dist_eq_norm, hdiff, norm_smul, coe_nnnorm]
      ring_nf
      exact le_rfl
    have hgamma_loc : LocallyLipschitz (affine z) := hgamma_lip.locallyLipschitz
    have hg_loc : LocallyLipschitz (g z) := by
      have hc := hF.comp hgamma_loc
      simpa [g, Function.comp_def, path, hpath] using hc
    have hg_loc_on : LocallyLipschitzOn (Icc (0 : ℝ) 1) (g z) :=
      hg_loc.locallyLipschitzOn
    obtain ⟨K, hK⟩ :=
      LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hg_loc_on
    have hac : AbsolutelyContinuousOnInterval (g z) 0 1 := by
      have hK' : LipschitzOnWith K (g z) (uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hK
      exact hK'.absolutelyContinuousOnInterval

    have hgamma_deriv' (t : ℝ) :
        HasDerivAt (path z) ((-1 : ℝ) • x + (1 : ℝ) • y) t := by
      have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
        (hasDerivAt_id t).const_sub (1 : ℝ)
      have hsum := (h1.smul_const x).add ((hasDerivAt_id t).smul_const y)
      have hsum' := hsum.add_const z
      simpa [path] using hsum'
    have hv : (-1 : ℝ) • x + (1 : ℝ) • y = v := by
      simp [v, sub_eq_add_neg, add_comm]
    have hgamma_deriv (t : ℝ) : HasDerivAt (path z) v t := by
      rw [← hv]
      exact hgamma_deriv' t

    have hderiv : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        |deriv (g z) t| ≤
          ‖y - x‖ * (A + B * ‖path z t‖) := by
      filter_upwards [hz] with t ht
      rcases ht with ⟨hDiff, hGrad⟩
      have hchain : HasDerivAt (fun s => F (path z s))
          (fderiv ℝ F (path z t) v) t := by
        exact hDiff.hasFDerivAt.comp_hasDerivAt t (hgamma_deriv t)
      have hderiv_eq : deriv (g z) t = fderiv ℝ F (path z t) v := by
        change deriv (fun s => F (path z s)) t = _
        exact hchain.deriv
      have hGradNorm : ‖gradient F (path z t)‖ =
          ‖fderiv ℝ F (path z t)‖ := by
        rw [gradient,
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
      calc
        |deriv (g z) t| = ‖fderiv ℝ F (path z t) v‖ := by
          rw [Real.norm_eq_abs, hderiv_eq]
        _ ≤ ‖fderiv ℝ F (path z t)‖ * ‖v‖ :=
          (fderiv ℝ F (path z t)).le_opNorm v
        _ = ‖gradient F (path z t)‖ * ‖y - x‖ := by
          rw [hGradNorm]
        _ ≤ (A + B * ‖path z t‖) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hGrad (norm_nonneg _)
        _ = ‖y - x‖ * (A + B * ‖path z t‖) := by
          ring

    have hsegment := interval_abs_sub_le_shifted_segment_growth
      (g z) x y z A B hac hB hderiv
    simpa [g, path] using hsegment

  let Q : EuclideanSpace ℝ ι → Prop := fun z =>
    |F (y + z) - F (x + z)| ≤
      ‖y - x‖ * (A + B / 2 * (‖x‖ + ‖y‖) + B * ‖z‖)
  have hQae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)), Q z := by
    simpa only [Q] using hbound
  have hFcont : Continuous F := hF.continuous
  have hleft : Continuous (fun z : EuclideanSpace ℝ ι =>
      |F (y + z) - F (x + z)|) := by
    exact continuous_abs.comp
      ((hFcont.comp (continuous_const.add continuous_id)).sub
        (hFcont.comp (continuous_const.add continuous_id)))
  have hright : Continuous (fun z : EuclideanSpace ℝ ι =>
      ‖y - x‖ * (A + B / 2 * (‖x‖ + ‖y‖) + B * ‖z‖)) := by
    fun_prop
  have hclosed : IsClosed {z : EuclideanSpace ℝ ι | Q z} := by
    change IsClosed {z : EuclideanSpace ℝ ι |
      |F (y + z) - F (x + z)| ≤
        ‖y - x‖ * (A + B / 2 * (‖x‖ + ‖y‖) + B * ‖z‖)}
    exact isClosed_le hleft hright
  have hdense : Dense {z : EuclideanSpace ℝ ι | Q z} := by
    rw [dense_iff_inter_open]
    intro U hU hUne
    by_contra hDisjoint
    have hbad : (volume : Measure (EuclideanSpace ℝ ι)) {z | ¬ Q z} = 0 :=
      ae_iff.mp hQae
    have hsub : U ⊆ {z : EuclideanSpace ℝ ι | ¬ Q z} := by
      intro z hzU hzQ
      exact hDisjoint ⟨z, hzU, hzQ⟩
    have hzero : (volume : Measure (EuclideanSpace ℝ ι)) U = 0 :=
      measure_mono_null hsub hbad
    exact (hU.measure_ne_zero (volume : Measure (EuclideanSpace ℝ ι)) hUne) hzero
  have hzero : (0 : EuclideanSpace ℝ ι) ∈ {z | Q z} := by
    have hmem : (0 : EuclideanSpace ℝ ι) ∈ closure {z | Q z} := by
      rw [hdense.closure_eq]
      simp
    exact hclosed.closure_subset hmem
  simpa [Q, A, B, abs_sub_comm, norm_sub_rev] using hzero

end LOOConcentration.Revision
