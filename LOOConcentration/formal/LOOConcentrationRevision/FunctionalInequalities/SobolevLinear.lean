import LOOConcentrationRevision.Frozen.Definitions.SobolevPair
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Module.Basic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open InnerProductSpace
open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]

omit [DecidableEq ι] in
private theorem gradient_add_contDiff {f g : EuclideanSpace ℝ ι → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : EuclideanSpace ℝ ι) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  change (toDual ℝ (EuclideanSpace ℝ ι)).symm
      (fderiv ℝ (fun y => f y + g y) x) =
    (toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ f x) +
      (toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ g x)
  rw [fderiv_fun_add (hf.contDiffAt.differentiableAt (by simp))
    (hg.contDiffAt.differentiableAt (by simp))]
  simp

omit [DecidableEq ι] in
private theorem gradient_smul_contDiff {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (c : ℝ)
    (x : EuclideanSpace ℝ ι) :
    gradient (fun y => c • f y) x = c • gradient f x := by
  change (toDual ℝ (EuclideanSpace ℝ ι)).symm
      (fderiv ℝ (fun y => c • f y) x) =
    c • (toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ f x)
  rw [fderiv_fun_const_smul (hf.contDiffAt.differentiableAt (by simp)) c]
  simp

/-- The smooth function-gradient image is closed under addition, with the actual
pointwise sum as its bounded smooth generator. -/
theorem smoothSobolevPairs_add
    {u v : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)}
    (hu : u ∈ smoothSobolevPairs μ) (hv : v ∈ smoothSobolevPairs μ) :
    u + v ∈ smoothSobolevPairs μ := by
  rcases hu with ⟨f, hfSmooth, ⟨B, hB, hBounds⟩, hfLp, hgradLp, huEq⟩
  rcases hv with ⟨g, hgSmooth, ⟨C, hC, hBoundsG⟩, hgLp, hgradLpG, hvEq⟩
  have hgradEq : gradient (fun x => f x + g x) = fun x => gradient f x + gradient g x := by
    funext x
    exact gradient_add_contDiff hfSmooth hgSmooth x
  have hgradSum : MemLp (gradient (fun x => f x + g x)) 2 μ := by
    rw [hgradEq]
    exact hgradLp.add hgradLpG
  have hgradToLp :
      hgradSum.toLp (gradient (fun x => f x + g x)) =
        hgradLp.toLp (gradient f) + hgradLpG.toLp (gradient g) := by
    calc
      hgradSum.toLp (gradient (fun x => f x + g x)) =
          (hgradLp.add hgradLpG).toLp (fun x => gradient f x + gradient g x) :=
        MemLp.toLp_congr hgradSum (hgradLp.add hgradLpG)
          (Filter.Eventually.of_forall fun x => congrFun hgradEq x)
      _ = hgradLp.toLp (gradient f) + hgradLpG.toLp (gradient g) :=
        MemLp.toLp_add hgradLp hgradLpG
  refine ⟨fun x => f x + g x, hfSmooth.add hgSmooth, ?_, hfLp.add hgLp, hgradSum, ?_⟩
  · refine ⟨B + C, add_nonneg hB hC, ?_⟩
    intro x
    constructor
    · calc
        |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
        _ ≤ B + C := add_le_add (hBounds x).1 (hBoundsG x).1
    · calc
        ‖gradient (fun y => f y + g y) x‖ =
            ‖gradient f x + gradient g x‖ := by rw [gradient_add_contDiff hfSmooth hgSmooth]
        _ ≤ ‖gradient f x‖ + ‖gradient g x‖ := norm_add_le _ _
        _ ≤ B + C := add_le_add (hBounds x).2 (hBoundsG x).2
  · rw [huEq, hvEq]
    apply (WithLp.ext_iff 2).2
    simp only [WithLp.ofLp_add]
    apply Prod.ext
    · exact (MemLp.toLp_add hfLp hgLp).symm
    · exact hgradToLp.symm

/-- Scalar multiplication preserves the smooth function-gradient image, using the
scaled generator and its scaled gradient. -/
theorem smoothSobolevPairs_smul
    {u : WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)}
    (c : ℝ) (hu : u ∈ smoothSobolevPairs μ) : c • u ∈ smoothSobolevPairs μ := by
  rcases hu with ⟨f, hfSmooth, ⟨B, hB, hBounds⟩, hfLp, hgradLp, huEq⟩
  have hgradEq : gradient (fun x => c • f x) = fun x => c • gradient f x := by
    funext x
    exact gradient_smul_contDiff hfSmooth c x
  have hgradScaled : MemLp (gradient (fun x => c • f x)) 2 μ := by
    rw [hgradEq]
    exact hgradLp.const_smul c
  have hgradToLp :
      hgradScaled.toLp (gradient (fun x => c • f x)) = c • hgradLp.toLp (gradient f) := by
    calc
      hgradScaled.toLp (gradient (fun x => c • f x)) =
          (hgradLp.const_smul c).toLp (fun x => c • gradient f x) :=
        MemLp.toLp_congr hgradScaled (hgradLp.const_smul c)
          (Filter.Eventually.of_forall fun x => congrFun hgradEq x)
      _ = c • hgradLp.toLp (gradient f) := MemLp.toLp_const_smul c hgradLp
  refine ⟨fun x => c • f x, hfSmooth.const_smul c, ?_, hfLp.const_smul c, hgradScaled, ?_⟩
  · refine ⟨|c| * B, mul_nonneg (abs_nonneg c) hB, ?_⟩
    intro x
    constructor
    · calc
        |c • f x| = |c| * |f x| := by rw [smul_eq_mul, abs_mul]
        _ ≤ |c| * B := mul_le_mul_of_nonneg_left (hBounds x).1 (abs_nonneg c)
    · calc
        ‖gradient (fun y => c • f y) x‖ =
            ‖c‖ * ‖gradient f x‖ := by rw [gradient_smul_contDiff hfSmooth c x, norm_smul]
        _ = |c| * ‖gradient f x‖ := by rw [Real.norm_eq_abs]
        _ ≤ |c| * B := mul_le_mul_of_nonneg_left (hBounds x).2 (abs_nonneg c)
  · rw [huEq]
    apply (WithLp.ext_iff 2).2
    simp only [WithLp.ofLp_smul]
    apply Prod.ext
    · exact (MemLp.toLp_const_smul c hfLp).symm
    · exact hgradToLp.symm

/-- A linear submodule whose carrier is the frozen smooth generator set. -/
def smoothSobolevPairsSubmodule :
    Submodule ℝ (WithLp 2 (Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ)) where
  carrier := smoothSobolevPairs μ
  zero_mem' := by
    let hfun : MemLp (fun _ : EuclideanSpace ℝ ι => (0 : ℝ)) 2 μ := memLp_const 0
    have hgradEq : gradient (fun _ : EuclideanSpace ℝ ι => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp [gradient]
    let hgrad : MemLp (gradient (fun _ : EuclideanSpace ℝ ι => (0 : ℝ))) 2 μ := by
      rw [hgradEq]
      exact memLp_const 0
    have hgradToLp : hgrad.toLp _ = 0 := by
      calc
        hgrad.toLp (gradient (fun _ : EuclideanSpace ℝ ι => (0 : ℝ))) =
            (memLp_const (0 : EuclideanSpace ℝ ι)).toLp (fun _ => 0) :=
          MemLp.toLp_congr hgrad (memLp_const (0 : EuclideanSpace ℝ ι))
            (Filter.Eventually.of_forall fun x => congrFun hgradEq x)
        _ = 0 := MemLp.toLp_zero _
    refine ⟨fun _ => 0, contDiff_const, ⟨0, le_rfl, ?_⟩, hfun, hgrad, ?_⟩
    · intro x
      simp [gradient]
    · rw [← WithLp.toLp_zero]
      apply (WithLp.ext_iff 2).2
      change (0 : Lp ℝ 2 μ × Lp (EuclideanSpace ℝ ι) 2 μ) =
        (hfun.toLp (fun _ => 0), hgrad.toLp _)
      apply Prod.ext
      · exact (MemLp.toLp_zero hfun).symm
      · exact hgradToLp.symm
  add_mem' := by
    intro u v hu hv
    exact smoothSobolevPairs_add μ hu hv
  smul_mem' := by
    intro c u hu
    exact smoothSobolevPairs_smul μ c hu

private theorem smoothSobolePairs_closure_eq :
    closure (smoothSobolevPairs μ) =
      (smoothSobolevPairsSubmodule μ).topologicalClosure := by
  rw [Submodule.topologicalClosure_coe]
  rfl

/-- The topological closure of the smooth generator set is a linear subspace. -/
theorem sobolevPair_add_mem {u v : SobolevPair μ} :
    (u.1 + v.1) ∈ closure (smoothSobolevPairs μ) := by
  have huEq :
      (u.1 ∈ closure (smoothSobolevPairs μ)) =
        (u.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure) :=
    congrArg (fun s : Set _ => u.1 ∈ s) (smoothSobolePairs_closure_eq μ)
  have hvEq :
      (v.1 ∈ closure (smoothSobolevPairs μ)) =
        (v.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure) :=
    congrArg (fun s : Set _ => v.1 ∈ s) (smoothSobolePairs_closure_eq μ)
  have hu : u.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure := by
    exact huEq.mp u.2
  have hv : v.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure := by
    exact hvEq.mp v.2
  have hadd := (smoothSobolevPairsSubmodule μ).topologicalClosure.add_mem hu hv
  have haddEq :
      ((u.1 + v.1) ∈ closure (smoothSobolevPairs μ)) =
        ((u.1 + v.1) ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure) :=
    congrArg (fun s : Set _ => (u.1 + v.1) ∈ s) (smoothSobolePairs_closure_eq μ)
  exact haddEq.mpr hadd

/-- Scalar multiplication preserves the actual Sobolev-pair subtype. -/
theorem sobolevPair_smul_mem (c : ℝ) {u : SobolevPair μ} :
    (c • u.1) ∈ closure (smoothSobolevPairs μ) := by
  have huEq :
      (u.1 ∈ closure (smoothSobolevPairs μ)) =
        (u.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure) :=
    congrArg (fun s : Set _ => u.1 ∈ s) (smoothSobolePairs_closure_eq μ)
  have hu : u.1 ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure := by
    exact huEq.mp u.2
  have hsmul := (smoothSobolevPairsSubmodule μ).topologicalClosure.smul_mem c hu
  have hsmulEq :
      ((c • u.1) ∈ closure (smoothSobolevPairs μ)) =
        ((c • u.1) ∈ (smoothSobolevPairsSubmodule μ).topologicalClosure) :=
    congrArg (fun s : Set _ => (c • u.1) ∈ s) (smoothSobolePairs_closure_eq μ)
  exact hsmulEq.mpr hsmul

/-- The concrete ambient value of `u + t • v`, retained as an actual Sobolev pair. -/
def sobolevPairPerturbation (u v : SobolevPair μ) (t : ℝ) : SobolevPair μ :=
  ⟨u.1 + t • v.1,
    sobolevPair_add_mem μ (u := u) (v := ⟨t • v.1, sobolevPair_smul_mem μ t (u := v)⟩)⟩

/-- Unpack both retained L2 components of the concrete perturbation. -/
theorem sobolevPairPerturbation_components (u v : SobolevPair μ) (t : ℝ) :
    WithLp.ofLp (sobolevPairPerturbation μ u v t).1 =
      WithLp.ofLp u.1 + t • WithLp.ofLp v.1 := by
  simp only [sobolevPairPerturbation, WithLp.ofLp_add, WithLp.ofLp_smul]

theorem sobolevPairPerturbation_function_component (u v : SobolevPair μ) (t : ℝ) :
    (WithLp.ofLp (sobolevPairPerturbation μ u v t).1).1 =
      (WithLp.ofLp u.1).1 + t • (WithLp.ofLp v.1).1 := by
  rw [sobolevPairPerturbation_components]
  rfl

theorem sobolevPairPerturbation_gradient_component (u v : SobolevPair μ) (t : ℝ) :
    (WithLp.ofLp (sobolevPairPerturbation μ u v t).1).2 =
      (WithLp.ofLp u.1).2 + t • (WithLp.ofLp v.1).2 := by
  rw [sobolevPairPerturbation_components]
  rfl

end

end LOOConcentration.Revision
