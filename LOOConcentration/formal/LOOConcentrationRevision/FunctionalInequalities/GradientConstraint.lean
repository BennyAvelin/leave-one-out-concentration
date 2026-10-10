import LOOConcentrationRevision.FunctionalInequalities.MazurClosure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter Set
open scoped ENNReal Topology
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (μ : Measure α)

/-- The literal a.e. norm constraint is convex in L2. -/
theorem convex_lp_ae_norm_le (q : α → ℝ) :
    Convex ℝ {g : Lp E 2 μ | ∀ᵐ x ∂μ, ‖g x‖ ≤ q x} := by
  rw [convex_iff_add_mem]
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hfx hgx hadd hsmulF hsmulG
  rw [hadd]
  simp only [Pi.add_apply, hsmulF, hsmulG, Pi.smul_apply]
  calc
    ‖a • f x + b • g x‖ ≤ ‖a • f x‖ + ‖b • g x‖ := norm_add_le _ _
    _ = a * ‖f x‖ + b * ‖g x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * q x + b * q x := add_le_add (mul_le_mul_of_nonneg_left hfx ha)
      (mul_le_mul_of_nonneg_left hgx hb)
    _ = q x := by rw [← add_mul, hab, one_mul]

omit [NormedSpace ℝ E] in
/-- Norm convergence has an a.e. convergent subsequence, retaining the bound. -/
theorem isClosed_lp_ae_norm_le (q : α → ℝ) :
    IsClosed {g : Lp E 2 μ | ∀ᵐ x ∂μ, ‖g x‖ ≤ q x} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, ‖f n x‖ ≤ q x := ae_all_iff.2 hf
  filter_upwards [hae, hall] with x hx hbound
  exact le_of_tendsto (continuous_norm.tendsto (g x) |>.comp hx)
    (Eventually.of_forall fun n => hbound (φ n))

/-- Vanishing approximation errors disappear at the weak limit of the actual
L2 gradients; no a.e. set is transferred to a different measure. -/
theorem weak_limit_lp_ae_norm_le_of_errors (q : α → ℝ)
    (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (nhds 0))
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ q x + err n)
    (hweak : Tendsto (fun n => toWeakSpace ℝ (Lp E 2 μ) (f n)) atTop
      (nhds (toWeakSpace ℝ (Lp E 2 μ) g))) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ q x := by
  have hδ (δ : ℝ) (hδ : 0 < δ) : ∀ᵐ x ∂μ, ‖g x‖ ≤ q x + δ := by
    let s : Set (Lp E 2 μ) := {v | ∀ᵐ x ∂μ, ‖v x‖ ≤ q x + δ}
    have hc : Convex ℝ s := convex_lp_ae_norm_le μ (fun x => q x + δ)
    have hclosed : IsClosed s := isClosed_lp_ae_norm_le μ (fun x => q x + δ)
    have hwclosed : IsClosed (toWeakSpace ℝ (Lp E 2 μ) '' s) := by
      have h := isClosed_closure (s := toWeakSpace ℝ (Lp E 2 μ) '' s)
      rw [← hc.toWeakSpace_closure ℝ, hclosed.closure_eq] at h
      exact h
    have hevent : ∀ᶠ n in atTop, toWeakSpace ℝ (Lp E 2 μ) (f n) ∈
        toWeakSpace ℝ (Lp E 2 μ) '' s := by
      filter_upwards [herr.eventually (Iio_mem_nhds hδ)] with n hn
      refine ⟨f n, ?_, rfl⟩
      filter_upwards [hf n] with x hx
      exact hx.trans (add_le_add le_rfl hn.le)
    obtain ⟨v, hv, hvg⟩ := hwclosed.mem_of_tendsto hweak hevent
    have hvg' : v = g := (toWeakSpace ℝ (Lp E 2 μ)).injective hvg
    change ∀ᵐ x ∂μ, ‖v x‖ ≤ q x + δ at hv
    rw [hvg'] at hv
    exact hv
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖g x‖ ≤ q x + 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun n => hδ (1 / ((n : ℝ) + 1)) (by positivity)
  filter_upwards [hall] with x hx
  have ht : Tendsto (fun n : ℕ => q x + 1 / ((n : ℝ) + 1)) atTop (nhds (q x)) := by
    simpa only [add_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q x) atTop (nhds (q x))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall hx)

/-- A joint weak limit is admitted by Mazur with the SAME retained gradient
bound. The generator and weak-limit producers are separate internal inputs. -/
theorem weak_smooth_pair_gradient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (f : ℕ → WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν))
    (p : WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν))
    (hweak : Tendsto (fun n => toWeakSpace ℝ
      (WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν)) (f n)) atTop
      (nhds (toWeakSpace ℝ
        (WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν)) p)))
    (hf : ∀ n, f n ∈ smoothSobolevPairs ν)
    (q : EuclideanSpace ℝ ι → ℝ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ n, ∀ᵐ x ∂ν, ‖(WithLp.ofLp (f n)).2 x‖ ≤ q x + err n) :
    ∃ u : SobolevPair ν, u.val = p ∧
      (∀ᵐ x ∂ν, ‖(WithLp.ofLp u.val).2 x‖ ≤ q x) := by
  let P : WithLp 2 (Lp ℝ 2 ν × Lp (EuclideanSpace ℝ ι) 2 ν) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 ν :=
    (ContinuousLinearMap.snd ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ ι) 2 ν)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
        (Lp (EuclideanSpace ℝ ι) 2 ν)).toContinuousLinearMap
  have hw : Tendsto (fun n => toWeakSpace ℝ (Lp (EuclideanSpace ℝ ι) 2 ν)
      ((WithLp.ofLp (f n)).2)) atTop
      (nhds (toWeakSpace ℝ (Lp (EuclideanSpace ℝ ι) 2 ν) (WithLp.ofLp p).2)) :=
    (WeakSpace.map P).continuous.tendsto _ |>.comp hweak
  have hb := weak_limit_lp_ae_norm_le_of_errors ν q
    (fun n => (WithLp.ofLp (f n)).2) (WithLp.ofLp p).2 err herr hbound hw
  obtain ⟨u, hu⟩ := weak_limit_smoothSobolevPairs_mem ν f p hweak hf
  refine ⟨u, hu, ?_⟩
  rw [hu]
  exact hb

end LOOConcentration.Revision
