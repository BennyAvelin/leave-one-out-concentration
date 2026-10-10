import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.Correspondence.SourceGradient

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem subexponential_average_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin (n + 2) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) id P μ)
    (hIndependent : iIndepFun X P)
    (lam : ℝ) (hLambda : 0 < lam)
    (hMGF : ∀ s : ℝ, s ≤ lam⁻¹ →
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (s * (x - ∫ y : ℝ, y ∂μ))) ∂μ) ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * s ^ 2 / 2)))
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤
      ((n + 2 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 2), X i ω -
        ∫ ω' : Ω, ((n + 2 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 2), X i ω' ∂P} ≤
      max (Real.exp (-(ε ^ 2 * (n + 2 : ℕ)) / (2 * lam ^ 2)))
        (Real.exp (-(ε * (n + 2 : ℕ)) / (2 * lam))) := by
  open Real in
    have centered_exp_integrable_of_mgf
        {μ : Measure ℝ} [IsProbabilityMeasure μ]
        (lam : ℝ)
        (hMGF : ∀ s : ℝ, s ≤ lam⁻¹ →
          (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (s * (x - ∫ y : ℝ, y ∂μ))) ∂μ) ≤
            ENNReal.ofReal (Real.exp (lam ^ 2 * s ^ 2 / 2)))
        (s : ℝ) (hs : s ≤ lam⁻¹) :
        Integrable (fun x : ℝ => exp (s * (x - ∫ y : ℝ, y ∂μ))) μ := by
      let m : ℝ := ∫ y : ℝ, y ∂μ
      let Z : ℝ → ℝ := fun x => x - m
      apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
        (Filter.Eventually.of_forall fun x => exp_nonneg (s * Z x))).mp
      have hfinite :
          (∫⁻ x : ℝ, ENNReal.ofReal (exp (s * Z x)) ∂μ) < ⊤ := by
        calc
          (∫⁻ x : ℝ, ENNReal.ofReal (exp (s * Z x)) ∂μ)
              ≤ ENNReal.ofReal (exp (lam ^ 2 * s ^ 2 / 2)) := by
                simpa [Z, m] using hMGF s hs
          _ < ⊤ := ENNReal.ofReal_lt_top
      exact ne_of_lt hfinite

    have integrable_id_of_two_sign_mgf
        {μ : Measure ℝ} [IsProbabilityMeasure μ]
        (lam : ℝ) (hLambda : 0 < lam)
        (hMGF : ∀ s : ℝ, s ≤ lam⁻¹ →
          (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (s * (x - ∫ y : ℝ, y ∂μ))) ∂μ) ≤
            ENNReal.ofReal (Real.exp (lam ^ 2 * s ^ 2 / 2))) :
        Integrable (id : ℝ → ℝ) μ := by
      let m : ℝ := ∫ y : ℝ, y ∂μ
      let Z : ℝ → ℝ := fun x => x - m
      have ha : 0 < lam⁻¹ := inv_pos.mpr hLambda
      have hpos : Integrable (fun x : ℝ => exp (lam⁻¹ * Z x)) μ :=
        centered_exp_integrable_of_mgf lam hMGF lam⁻¹ le_rfl
      have hneg₀ := centered_exp_integrable_of_mgf lam hMGF (-lam⁻¹) (by linarith)
      have hneg : Integrable (fun x : ℝ => exp (lam⁻¹ * (m - x))) μ := by
        convert hneg₀ using 1
        funext x
        congr 1
        simp only [m]
        ring
      have hEnvelope :
          Integrable (fun x : ℝ => lam * (exp (lam⁻¹ * Z x) + exp (lam⁻¹ * (m - x)))) μ := by
        have h := hpos.add hneg
        simpa [Z, Pi.add_apply, mul_add] using h.const_mul lam
      have hZbound (x : ℝ) :
          |Z x| ≤ lam * (exp (lam⁻¹ * Z x) + exp (lam⁻¹ * (m - x))) := by
        have hc : 0 ≤ lam := le_of_lt hLambda
        have hplus : Z x ≤ lam * exp (lam⁻¹ * Z x) := by
          simpa [Z, mul_comm] using le_inv_mul_exp (x - m) ha
        have hminus : -Z x ≤ lam * exp (lam⁻¹ * (m - x)) := by
          simpa [Z, m] using le_inv_mul_exp (m - x) ha
        apply abs_le.mpr
        constructor
        · calc
            -(lam * (exp (lam⁻¹ * Z x) + exp (lam⁻¹ * (m - x))))
                ≤ -(lam * exp (lam⁻¹ * (m - x))) := by
                  apply neg_le_neg
                  nlinarith [mul_nonneg hc (exp_nonneg (lam⁻¹ * Z x))]
            _ ≤ Z x := by linarith
        · calc
            Z x ≤ lam * exp (lam⁻¹ * Z x) := hplus
            _ ≤ lam * (exp (lam⁻¹ * Z x) + exp (lam⁻¹ * (m - x))) := by
              nlinarith [mul_nonneg hc (exp_nonneg (lam⁻¹ * (m - x)))]
      have hZ : Integrable Z μ := by
        refine Integrable.mono hEnvelope (by fun_prop) ?_
        filter_upwards with x
        change |Z x| ≤ |lam * (exp (lam⁻¹ * Z x) + exp (lam⁻¹ * (m - x)))|
        rw [abs_mul, abs_of_nonneg hLambda.le,
          abs_of_nonneg (add_nonneg (exp_nonneg _) (exp_nonneg _))]
        exact hZbound x
      have hId : Integrable (fun x : ℝ => Z x + m) μ := hZ.add (integrable_const m)
      change Integrable (fun x : ℝ => x) μ
      simpa [Z, m] using hId

    have mgf_centered_le_of_mgf
        {μ : Measure ℝ} [IsProbabilityMeasure μ]
        (lam : ℝ)
        (hMGF : ∀ s : ℝ, s ≤ lam⁻¹ →
          (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (s * (x - ∫ y : ℝ, y ∂μ))) ∂μ) ≤
            ENNReal.ofReal (Real.exp (lam ^ 2 * s ^ 2 / 2)))
        (s : ℝ) (hs : s ≤ lam⁻¹) :
        mgf (fun x : ℝ => x - ∫ y : ℝ, y ∂μ) μ s ≤ exp (lam ^ 2 * s ^ 2 / 2) := by
      let m : ℝ := ∫ y : ℝ, y ∂μ
      let Z : ℝ → ℝ := fun x => x - m
      have hInt : Integrable (fun x : ℝ => exp (s * Z x)) μ :=
        centered_exp_integrable_of_mgf lam hMGF s hs
      have hENN :
          ENNReal.ofReal (∫ x : ℝ, exp (s * Z x) ∂μ) ≤
            ENNReal.ofReal (exp (lam ^ 2 * s ^ 2 / 2)) := by
        calc
          ENNReal.ofReal (∫ x : ℝ, exp (s * Z x) ∂μ) =
              ∫⁻ x : ℝ, ENNReal.ofReal (exp (s * Z x)) ∂μ :=
            ofReal_integral_eq_lintegral_ofReal hInt
              (Filter.Eventually.of_forall fun x => exp_nonneg (s * Z x))
          _ ≤ ENNReal.ofReal (exp (lam ^ 2 * s ^ 2 / 2)) := by
            simpa [Z, m] using hMGF s hs
      have hReal : ∫ x : ℝ, exp (s * Z x) ∂μ ≤ exp (lam ^ 2 * s ^ 2 / 2) :=
        (ENNReal.ofReal_le_ofReal_iff (exp_nonneg _)).mp hENN
      simpa [Z, m, mgf] using hReal

    let N : ℝ := ((n + 2 : ℕ) : ℝ)
    let m : ℝ := ∫ y : ℝ, y ∂μ
    have hN : 0 < N := by positivity
    have hmuInt : Integrable (id : ℝ → ℝ) μ :=
      integrable_id_of_two_sign_mgf lam hLambda hMGF
    have hCenteredLaw (i : Fin (n + 2)) :
        IdentDistrib (fun ω : Ω => X i ω - m) (fun x : ℝ => x - m) P μ :=
      (hLaw i).comp (measurable_id.sub_const m)
    have hCenteredIndep : iIndepFun (fun i : Fin (n + 2) => fun ω : Ω => X i ω - m) P := by
      exact hIndependent.comp (fun (_i : Fin (n + 2)) (x : ℝ) => x - m)
        (fun (_i : Fin (n + 2)) => measurable_id.sub_const m)
    have hCenteredMeas (i : Fin (n + 2)) : AEMeasurable (fun ω : Ω => X i ω - m) P :=
      (hCenteredLaw i).aemeasurable_fst
    have hCenteredExpInt (i : Fin (n + 2)) (s : ℝ) (hs : s ≤ lam⁻¹) :
        Integrable (fun ω : Ω => exp (s * (X i ω - m))) P := by
      have hExpLaw := (hCenteredLaw i).comp (measurable_const_mul s).exp
      apply hExpLaw.integrable_iff.mpr
      simpa [Function.comp_def, m] using centered_exp_integrable_of_mgf lam hMGF s hs
    have hCenteredMgf (i : Fin (n + 2)) (s : ℝ) (hs : s ≤ lam⁻¹) :
        mgf (fun ω : Ω => X i ω - m) P s ≤ exp (lam ^ 2 * s ^ 2 / 2) := by
      rw [mgf_congr_of_identDistrib (fun ω : Ω => X i ω - m) (fun x : ℝ => x - m)
        (hCenteredLaw i) s]
      simpa [m] using mgf_centered_le_of_mgf (μ := μ) lam hMGF s hs
    have hXInt (i : Fin (n + 2)) : Integrable (fun ω : Ω => X i ω) P :=
      (hLaw i).integrable_iff.mpr hmuInt
    have hXMean (i : Fin (n + 2)) : ∫ ω : Ω, X i ω ∂P = m := by
      simpa [m] using (hLaw i).integral_eq
    have hAverageInt :
        Integrable (fun ω : Ω => N⁻¹ * ∑ i : Fin (n + 2), X i ω) P := by
      apply (integrable_finsetSum Finset.univ ?_).const_mul N⁻¹
      intro i hi
      exact hXInt i
    have hAverageMean :
        ∫ ω : Ω, N⁻¹ * ∑ i : Fin (n + 2), X i ω ∂P = m := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (by
        intro i hi
        exact hXInt i)]
      calc
        N⁻¹ * ∑ i : Fin (n + 2), (∫ ω : Ω, X i ω ∂P) =
            N⁻¹ * ∑ i : Fin (n + 2), m := by
          simp_rw [hXMean]
        _ = N⁻¹ * (N * m) := by
          simp [N, Finset.sum_const, Fintype.card_fin]
        _ = m := by field_simp [ne_of_gt hN]
    have hCenteredSumMgf (s : ℝ) :
        mgf (fun ω : Ω => ∑ i : Fin (n + 2), (X i ω - m)) P s =
          ∏ i : Fin (n + 2), mgf (fun ω : Ω => X i ω - m) P s := by
      have hfun :
          (fun ω : Ω => ∑ i : Fin (n + 2), (X i ω - m)) =
            ∑ i : Fin (n + 2), (fun ω : Ω => X i ω - m) := by
        funext ω
        simp
      rw [hfun]
      exact hCenteredIndep.mgf_sum₀ hCenteredMeas Finset.univ (t := s)
    have hTailCore (s : ℝ) (hs : 0 ≤ s) (hsCut : s ≤ lam⁻¹) :
        P.real {ω | ε * N ≤ ∑ i : Fin (n + 2), (X i ω - m)} ≤
          exp (N * (-s * ε + lam ^ 2 * s ^ 2 / 2)) := by
      let S : Ω → ℝ := fun ω => ∑ i : Fin (n + 2), (X i ω - m)
      have hSInt : Integrable (fun ω : Ω => exp (s * S ω)) P := by
        apply (mgf_pos_iff (X := S) (μ := P) (t := s)).mp
        rw [hCenteredSumMgf]
        apply Finset.prod_pos
        intro i hi
        exact mgf_pos (hCenteredExpInt i s hsCut)
      have hSumMgfBound : mgf S P s ≤ exp (N * (lam ^ 2 * s ^ 2 / 2)) := by
        rw [hCenteredSumMgf]
        calc
          ∏ i : Fin (n + 2), mgf (fun ω : Ω => X i ω - m) P s ≤
              ∏ i : Fin (n + 2), exp (lam ^ 2 * s ^ 2 / 2) := by
                apply Finset.prod_le_prod
                · intro i hi
                  exact mgf_nonneg
                · intro i hi
                  exact hCenteredMgf i s hsCut
          _ = exp (N * (lam ^ 2 * s ^ 2 / 2)) := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← Real.exp_nat_mul]
      have hChernoff := measure_ge_le_exp_mul_mgf (X := S) (μ := P)
        (ε := ε * N) (t := s) hs hSInt
      calc
        P.real {ω | ε * N ≤ S ω} ≤ exp (-s * (ε * N)) * mgf S P s := hChernoff
        _ ≤ exp (-s * (ε * N)) * exp (N * (lam ^ 2 * s ^ 2 / 2)) := by
          exact mul_le_mul_of_nonneg_left hSumMgfBound (exp_nonneg _)
        _ = exp (N * (-s * ε + lam ^ 2 * s ^ 2 / 2)) := by
          rw [← exp_add]
          congr 1
          ring_nf
    have hScaleEvent :
        {ω : Ω | ε ≤ N⁻¹ * ∑ i : Fin (n + 2), X i ω - m} =
          {ω : Ω | ε * N ≤ ∑ i : Fin (n + 2), (X i ω - m)} := by
      ext ω
      have hscaled :
          N * (N⁻¹ * ∑ i : Fin (n + 2), X i ω - m) =
            ∑ i : Fin (n + 2), (X i ω - m) := by
        calc
          N * (N⁻¹ * ∑ i : Fin (n + 2), X i ω - m) =
              N * N⁻¹ * ∑ i : Fin (n + 2), X i ω - N * m := by ring
          _ = ∑ i : Fin (n + 2), (X i ω - m) := by
            rw [mul_inv_cancel₀ (ne_of_gt hN), one_mul]
            simp [Finset.sum_sub_distrib, N, Finset.sum_const, Fintype.card_fin]
      constructor
      · intro h
        have h' := (mul_le_mul_iff_of_pos_left hN).2 h
        calc
          ε * N = N * ε := by ring
          _ ≤ N * (N⁻¹ * ∑ i : Fin (n + 2), X i ω - m) := h'
          _ = ∑ i : Fin (n + 2), (X i ω - m) := hscaled
      · intro h
        apply (mul_le_mul_iff_of_pos_left hN).1
        calc
          N * ε = ε * N := by ring
          _ ≤ ∑ i : Fin (n + 2), (X i ω - m) := h
          _ = N * (N⁻¹ * ∑ i : Fin (n + 2), X i ω - m) := hscaled.symm
    have hEvent :
        {ω : Ω | ε ≤ N⁻¹ * ∑ i : Fin (n + 2), X i ω -
          ∫ ω' : Ω, N⁻¹ * ∑ i : Fin (n + 2), X i ω' ∂P} =
          {ω : Ω | ε * N ≤ ∑ i : Fin (n + 2), (X i ω - m)} := by
      simpa [hAverageMean] using hScaleEvent
    rw [hEvent]
    by_cases hεlam : ε ≤ lam
    · let s : ℝ := ε / lam ^ 2
      have hs : 0 ≤ s := by
        dsimp [s]
        positivity
      have hsCut : s ≤ lam⁻¹ := by
        dsimp [s]
        rw [div_le_iff₀ (sq_pos_of_pos hLambda)]
        calc
          ε ≤ lam := hεlam
          _ = lam⁻¹ * lam ^ 2 := by field_simp [ne_of_gt hLambda]
      have hExponent :
          N * (-s * ε + lam ^ 2 * s ^ 2 / 2) =
            -(ε ^ 2 * (n + 2 : ℕ)) / (2 * lam ^ 2) := by
        dsimp [s, N]
        field_simp [ne_of_gt hLambda]
        ring
      have h := hTailCore s hs hsCut
      rw [hExponent] at h
      exact h.trans (le_max_left _ _)
    · have hlamε : lam ≤ ε := le_of_not_ge hεlam
      have hs : 0 ≤ lam⁻¹ := (inv_pos.mpr hLambda).le
      have hsCut : lam⁻¹ ≤ lam⁻¹ := le_rfl
      have hExponent :
          N * (-lam⁻¹ * ε + lam ^ 2 * (lam⁻¹) ^ 2 / 2) ≤
            -(ε * (n + 2 : ℕ)) / (2 * lam) := by
        have hscalar : -lam⁻¹ * ε + lam ^ 2 * (lam⁻¹) ^ 2 / 2 ≤ -ε / (2 * lam) := by
          field_simp [ne_of_gt hLambda]
          nlinarith [hlamε]
        calc
          N * (-lam⁻¹ * ε + lam ^ 2 * (lam⁻¹) ^ 2 / 2) ≤
              N * (-ε / (2 * lam)) := mul_le_mul_of_nonneg_left hscalar hN.le
          _ = -(ε * (n + 2 : ℕ)) / (2 * lam) := by
            dsimp [N]
            ring
      have h := hTailCore lam⁻¹ hs hsCut
      exact (h.trans (Real.exp_le_exp.mpr hExponent)).trans (le_max_right _ _)

end LOOConcentration.Manuscript
