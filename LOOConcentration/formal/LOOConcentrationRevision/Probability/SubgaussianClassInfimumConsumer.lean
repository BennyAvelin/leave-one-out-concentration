import LOOConcentrationRevision.Probability.RestrictionSubgaussianClass

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped NNReal ENNReal

private theorem exists_uniform_proxy_le_add_of_class_infimum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace ℝ ι)) (C : ℝ≥0)
    (hInf : sInf {d : ℝ≥0∞ | ∃ c : ℝ≥0, d = (c : ℝ≥0∞) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
        (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤ (C : ℝ≥0∞)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ c : ℝ≥0, c ≤ C + ε ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
        (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν := by
  intro ε hε
  by_contra hnone
  have hlower (d : ℝ≥0∞)
      (hd : d ∈ {d : ℝ≥0∞ | ∃ c : ℝ≥0, d = (c : ℝ≥0∞) ∧
        ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
          (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
          ProbabilityTheory.HasSubgaussianMGF
            (fun x => F x - ∫ y, F y ∂ν) c ν}) : (C + ε : ℝ≥0∞) ≤ d := by
    rcases hd with ⟨c, hdc, hClass⟩
    subst d
    have hc : ¬ c ≤ C + ε := by
      intro hc
      exact hnone ⟨c, hc, hClass⟩
    exact ENNReal.coe_le_coe.mpr (le_of_not_ge hc)
  have hle := le_sInf hlower
  have hlt : (C : ℝ≥0∞) < (C + ε : ℝ≥0∞) := by
    exact ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right C hε)
  exact (not_le_of_gt hlt) (hle.trans hInf)

/-- A finite bound on the literal whole local-Lipschitz class infimum transfers
to every integrable function that is 1-Lipschitz on the same event. -/
theorem local_lipschitz_hasSubgaussianMGF_of_class_infimum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace ℝ ι)) (C : ℝ≥0)
    (hInf : sInf {d : ℝ≥0∞ | ∃ c : ℝ≥0, d = (c : ℝ≥0∞) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
        (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤ (C : ℝ≥0∞))
    (H : EuclideanSpace ℝ ι → ℝ) (hH : Integrable H ν)
    (hLip : ∀ x ∈ A, ∀ y ∈ A, |H x - H y| ≤ ‖x-y‖) :
    ProbabilityTheory.HasSubgaussianMGF (fun x => H x - ∫ y, H y ∂ν) C ν := by
  have hProxy := exists_uniform_proxy_le_add_of_class_infimum_le ν A C hInf
  obtain ⟨c0, _hc0, hClass0⟩ := hProxy 1 (by norm_num)
  have hSG0 := hClass0 H hH hLip
  refine ⟨hSG0.integrable_exp_mul, ?_⟩
  intro t
  by_contra hnot
  have hbad : Real.exp ((C : ℝ) * t ^ 2 / 2) <
      ProbabilityTheory.mgf (fun x => H x - ∫ y, H y ∂ν) ν t :=
    lt_of_not_ge hnot
  let f : ℝ → ℝ := fun ε => Real.exp (((C : ℝ) + ε) * t ^ 2 / 2)
  have hfcont : Continuous f := by fun_prop
  have hopen : IsOpen {ε : ℝ | f ε <
      ProbabilityTheory.mgf (fun x => H x - ∫ y, H y ∂ν) ν t} :=
    isOpen_lt hfcont continuous_const
  have hzero : (0 : ℝ) ∈ {ε : ℝ | f ε <
      ProbabilityTheory.mgf (fun x => H x - ∫ y, H y ∂ν) ν t} := by
    simpa [f] using hbad
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  let ε : ℝ := r / 2
  have hεpos : 0 < ε := by dsimp [ε]; linarith
  have hεball : ε ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [sub_zero, abs_of_pos hεpos, ε] using (show r / 2 < r by linarith)
  have hsmall : f ε <
      ProbabilityTheory.mgf (fun x => H x - ∫ y, H y ∂ν) ν t := hball hεball
  let εnn : ℝ≥0 := ⟨ε, hεpos.le⟩
  obtain ⟨c, hc, hClass⟩ := hProxy εnn (by exact_mod_cast hεpos)
  have hcoeff : (c : ℝ) ≤ (C : ℝ) + ε := by
    have := hc
    exact_mod_cast this
  have hbound := (hClass H hH hLip).mgf_le t
  have hle : Real.exp ((c : ℝ) * t ^ 2 / 2) ≤ f ε := by
    apply Real.exp_le_exp.mpr
    have ht : 0 ≤ t ^ 2 / 2 := by positivity
    calc
      (c : ℝ) * t ^ 2 / 2 = (c : ℝ) * (t ^ 2 / 2) := by ring
      _ ≤ ((C : ℝ) + ε) * (t ^ 2 / 2) := mul_le_mul_of_nonneg_right hcoeff ht
      _ = ((C : ℝ) + ε) * t ^ 2 / 2 := by ring
  exact (not_lt_of_ge (hbound.trans hle)) hsmall

/-- Scales the literal-class MGF consumer by a Lipschitz constant on the same
event. At zero scale, the support event makes the function constant almost
everywhere, so the centered MGF has proxy zero. -/
theorem local_lipschitz_hasSubgaussianMGF_scaled_of_class_infimum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace ℝ ι)) (C : ℝ≥0)
    (hInf : sInf {d : ℝ≥0∞ | ∃ c : ℝ≥0, d = (c : ℝ≥0∞) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F ν →
        (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν} ≤ (C : ℝ≥0∞))
    (hSupport : ∀ᵐ x ∂ν, x ∈ A)
    (H : EuclideanSpace ℝ ι → ℝ) (hH : Integrable H ν)
    (L : ℝ≥0)
    (hLip : ∀ x ∈ A, ∀ y ∈ A, |H x - H y| ≤ (L : ℝ) * ‖x-y‖) :
    ProbabilityTheory.HasSubgaussianMGF (fun x => H x - ∫ y, H y ∂ν) (C * L ^ 2) ν := by
  by_cases hL : L = 0
  · obtain ⟨x0, hx0⟩ := hSupport.exists
    have hconst : ∀ᵐ x ∂ν, H x = H x0 := by
      filter_upwards [hSupport] with x hx
      have h := hLip x hx x0 hx0
      rw [hL, NNReal.coe_zero, zero_mul] at h
      have h' := abs_le.mp h
      linarith
    have hmean : (∫ x, H x ∂ν) = H x0 := by
      calc
        (∫ x, H x ∂ν) = ∫ x, (fun _ => H x0) x ∂ν := integral_congr_ae hconst
        _ = H x0 := by simp
    have hcenter : (fun x => H x - ∫ y, H y ∂ν) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
      filter_upwards [hconst] with x hx
      simp [hx, hmean]
    have hzero : ProbabilityTheory.HasSubgaussianMGF (fun _ : EuclideanSpace ℝ ι => (0 : ℝ)) 0 ν :=
      ProbabilityTheory.HasSubgaussianMGF.fun_zero
    simpa [hL] using hzero.congr hcenter.symm
  · have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hL)
    let G : EuclideanSpace ℝ ι → ℝ := fun x => H x / (L : ℝ)
    have hGint : Integrable G ν := by
      dsimp [G]
      exact hH.div_const _
    have hGlip : ∀ x ∈ A, ∀ y ∈ A, |G x - G y| ≤ ‖x-y‖ := by
      intro x hx y hy
      have hxy := hLip x hx y hy
      dsimp [G]
      rw [← sub_div, abs_div, abs_of_pos hLpos]
      calc
        |H x - H y| / (L : ℝ) ≤ ((L : ℝ) * ‖x-y‖) / (L : ℝ) :=
          div_le_div_of_nonneg_right hxy hLpos.le
        _ = ‖x-y‖ := by field_simp [ne_of_gt hLpos]
    have hG := local_lipschitz_hasSubgaussianMGF_of_class_infimum_le
      ν A C hInf G hGint hGlip
    have hscale := hG.const_mul (L : ℝ)
    have hmean : (∫ y, G y ∂ν) = (∫ y, H y ∂ν) / (L : ℝ) := by
      dsimp [G]
      exact integral_div (L : ℝ) H
    have hcenter : (fun x => (L : ℝ) * (G x - ∫ y, G y ∂ν)) =ᵐ[ν]
        (fun x => H x - ∫ y, H y ∂ν) := by
      filter_upwards [Filter.Eventually.of_forall fun _ : EuclideanSpace ℝ ι => True.intro]
        with x _
      dsimp [G]
      rw [hmean]
      field_simp [ne_of_gt hLpos]
    have hsq : (⟨(L : ℝ) ^ 2, sq_nonneg (L : ℝ)⟩ : ℝ≥0) = L ^ 2 := by
      apply NNReal.coe_injective
      rfl
    rw [hsq] at hscale
    rw [mul_comm C (L ^ 2)]
    exact hscale.congr hcenter

end LOOConcentration.Revision

