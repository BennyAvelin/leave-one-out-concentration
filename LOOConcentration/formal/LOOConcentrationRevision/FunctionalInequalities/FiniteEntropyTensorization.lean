import LOOConcentration.FunctionalInequalities.EntropyCoordinateTransport
import LOOConcentration.FunctionalInequalities.EntropyMixture
import LOOConcentrationRevision.FunctionalInequalities.FiniteEntropySplit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Finite bounded-positive entropy subadditivity

This module iterates the reviewed two-factor inequality over the actual finite
product law. The coordinate terms are transported by the reviewed insertion
identity, with every section-entropy kernel admitted as an integrable function.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration.Revision

open LOOConcentration

private theorem piFinSuccAbove_zero_symm_apply_cons
    {E : Type*} [MeasurableSpace E] {n : ℕ}
    (z : E) (tail : Fin n → E) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
        (z, tail) = Fin.cons z tail := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero']

/-- The induction step for finite entropy subadditivity, with the exact
bounded-positive two-factor subadditivity theorem as its sole predecessor.
The intended producer of this predecessor is
`entropy_two_factor_subadditive_bounded_positive`. -/
theorem entropy_piFin_succ_subadditive_of_two_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hTwoFactor :
      ∀ {s : ℕ} (ν : Measure (Fin s → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν]
        (F : EuclideanSpace ℝ ι ×
          (Fin s → EuclideanSpace ℝ ι) → ℝ) (ε B : ℝ)
        (_hF : Measurable F) (_hε : 0 < ε)
        (_hBounds : ∀ p, ε ≤ F p ∧ F p ≤ B),
        entropy (μ.prod ν) F ≤
          (∫ x, entropy ν (fun y => F (x, y)) ∂μ) +
            (∫ y, entropy μ (fun x => F (x, y)) ∂ν))
    {r : ℕ}
    (f : (Fin (r + 1) → EuclideanSpace ℝ ι) → ℝ)
    (ε B : ℝ) (hf : Measurable f) (hε : 0 < ε)
    (hBounds : ∀ D, ε ≤ f D ∧ f D ≤ B) :
    entropy (Measure.pi fun _ : Fin (r + 1) => μ) f ≤
      ∑ i : Fin (r + 1),
        ∫ tail : Fin r → EuclideanSpace ℝ ι,
          entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm
              (z, tail))) ∂Measure.pi fun _ : Fin r => μ := by
  induction r with
  | zero =>
      let E := EuclideanSpace ℝ ι
      let ν : Measure (Fin 0 → E) := Measure.pi fun _ : Fin 0 => μ
      let F : E × (Fin 0 → E) → ℝ := fun p => f (Fin.cons p.1 p.2)
      have hB0 : 0 ≤ B := by
        have hb := hBounds (default : Fin 1 → E)
        exact (le_trans hε.le hb.1).trans hb.2
      have hFmeas : Measurable F := by
        dsimp [F]
        fun_prop
      have hFbounds (p : E × (Fin 0 → E)) : ε ≤ F p ∧ F p ≤ B :=
        hBounds (Fin.cons p.1 p.2)
      have hFnonneg (p : E × (Fin 0 → E)) : 0 ≤ F p :=
        le_trans hε.le (hFbounds p).1
      have hsplit := entropy_piFin_succ_split μ f B hf
        (fun D => le_trans hε.le (hBounds D).1) (fun D => (hBounds D).2)
        (0 : Fin 1)
      have hchain := entropy_two_factor_chain_rule μ ν F B hFmeas hFnonneg
        (fun p => (hFbounds p).2)
      have htransport : entropy (Measure.pi fun _ : Fin 1 => μ) f =
          entropy (μ.prod ν) F := by
        calc
          _ = _ := by
            simpa [E, ν, F, piFinSuccAbove_zero_symm_apply_cons] using hsplit
          _ = _ := by
            simpa [ν, F] using hchain.symm
      have hpair := hTwoFactor ν F ε B hFmeas hε hFbounds
      have hpairFull : entropy (Measure.pi fun _ : Fin 1 => μ) f ≤
          (∫ z, entropy ν (fun tail => f (Fin.cons z tail)) ∂μ) +
            (∫ tail, entropy μ (fun z => f (Fin.cons z tail)) ∂ν) := by
        calc
          _ = entropy (μ.prod ν) F := htransport
          _ ≤ _ := by simpa [F, ν] using hpair
      have hfirstZero :
          (∫ z, entropy ν (fun tail => f (Fin.cons z tail)) ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with z
        exact entropy_piFin_zero_eq_zero μ _
      have htarget :
          (∑ i : Fin 1,
            ∫ tail : Fin 0 → E,
              entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin 1 => E) i).symm (z, tail))) ∂ν) =
            ∫ tail, entropy μ (fun z => f (Fin.cons z tail)) ∂ν := by
        rw [Fin.sum_univ_succ]
        simp [ν, piFinSuccAbove_zero_symm_apply_cons]
      calc
        entropy (Measure.pi fun _ : Fin 1 => μ) f ≤
            ∫ tail, entropy μ (fun z => f (Fin.cons z tail)) ∂ν := by
          simpa [hfirstZero] using hpairFull
        _ = _ := htarget.symm
  | succ r ih =>
      let E := EuclideanSpace ℝ ι
      let ν : Measure (Fin (r + 1) → E) := Measure.pi fun _ : Fin (r + 1) => μ
      let e₀ : (Fin (r + 2) → E) ≃ᵐ E × (Fin (r + 1) → E) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 2) => E) 0
      have hinsert0 (z₀ : E) (tail : Fin (r + 1) → E) :
          e₀.symm (z₀, tail) = Fin.cons z₀ tail := by
        exact piFinSuccAbove_zero_symm_apply_cons z₀ tail
      let F : E × (Fin (r + 1) → E) → ℝ := fun p => f (Fin.cons p.1 p.2)
      let secFun : E → (Fin (r + 1) → E) → ℝ := fun z₀ tail =>
        f (Fin.cons z₀ tail)
      let A : ℝ := ∫ z₀, entropy ν (secFun z₀) ∂μ
      let B₀ : ℝ := ∫ tail, entropy μ (fun z₀ => F (z₀, tail)) ∂ν
      have hB0 : 0 ≤ B := by
        have hb := hBounds (default : Fin (r + 2) → E)
        exact (le_trans hε.le hb.1).trans hb.2
      have hFmeas : Measurable F := by
        dsimp [F]
        fun_prop
      have hFbounds (p : E × (Fin (r + 1) → E)) : ε ≤ F p ∧ F p ≤ B :=
        hBounds (Fin.cons p.1 p.2)
      have hFnonneg (p : E × (Fin (r + 1) → E)) : 0 ≤ F p :=
        le_trans hε.le (hFbounds p).1
      have hsplit := entropy_piFin_succ_split μ f B hf
        (fun D => le_trans hε.le (hBounds D).1) (fun D => (hBounds D).2)
        (0 : Fin (r + 2))
      have hchain := entropy_two_factor_chain_rule μ ν F B hFmeas hFnonneg
        (fun p => (hFbounds p).2)
      have htransport : entropy (Measure.pi fun _ : Fin (r + 2) => μ) f =
          entropy (μ.prod ν) F := by
        calc
          _ = _ := by
            simpa [E, ν, secFun, A,
              piFinSuccAbove_zero_symm_apply_cons] using hsplit
          _ = _ := by
            simpa [ν, F, secFun, A] using hchain.symm
      have hpair := hTwoFactor ν F ε B hFmeas hε hFbounds
      have hpairFull : entropy (Measure.pi fun _ : Fin (r + 2) => μ) f ≤ A + B₀ := by
        calc
          _ = entropy (μ.prod ν) F := htransport
          _ ≤ _ := by simpa [A, B₀, F, secFun, ν] using hpair
      let FA : ((Fin (r + 1) → E) × E) → ℝ := fun p =>
        f (Fin.cons p.2 p.1)
      have hFAmeas : Measurable FA := by
        fun_prop
      have hFAbounds (p : (Fin (r + 1) → E) × E) :
          0 ≤ FA p ∧ FA p ≤ B := by
        constructor
        · exact le_trans hε.le (hBounds (Fin.cons p.2 p.1)).1
        · exact (hBounds (Fin.cons p.2 p.1)).2
      have hAint : Integrable (fun z₀ => entropy ν (secFun z₀)) μ := by
        change Integrable
          (fun z₀ => entropy ν (fun tail => FA (tail, z₀))) μ
        exact entropy_section_integrable ν μ FA B hB0 hFAmeas
          (fun p => (hFAbounds p).1) (fun p => (hFAbounds p).2)
      let K : Fin (r + 1) → E → ℝ := fun j z₀ =>
        ∫ tail₂ : Fin r → E,
          entropy μ (fun zⱼ => f (e₀.symm
            (z₀, (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => E) j).symm (zⱼ, tail₂))))
          ∂Measure.pi fun _ : Fin r => μ
      have hKint (j : Fin (r + 1)) : Integrable (K j) μ := by
        let eTail : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) j
        let Q : E × (Fin r → E) → ℝ := fun p =>
          entropy μ (fun zⱼ => f (e₀.symm (p.1, eTail.symm (zⱼ, p.2))))
        let HQ : E × (E × (Fin r → E)) → ℝ := fun p =>
          f (e₀.symm (p.2.1, eTail.symm (p.1, p.2.2)))
        have hHQmeas : Measurable HQ := by
          fun_prop
        have hHQbounds (p : E × (E × (Fin r → E))) :
            0 ≤ HQ p ∧ HQ p ≤ B := by
          constructor
          · exact le_trans hε.le
              (hBounds (e₀.symm (p.2.1, eTail.symm (p.1, p.2.2)))).1
          · exact (hBounds (e₀.symm (p.2.1, eTail.symm (p.1, p.2.2)))).2
        have hQint : Integrable Q (μ.prod (Measure.pi fun _ : Fin r => μ)) := by
          change Integrable
            (fun p : E × (Fin r → E) => entropy μ (fun zⱼ => HQ (zⱼ, p))) _
          exact entropy_section_integrable μ (μ.prod (Measure.pi fun _ : Fin r => μ))
            HQ B hB0 hHQmeas (fun p => (hHQbounds p).1)
            (fun p => (hHQbounds p).2)
        change Integrable (fun z₀ => ∫ tail₂, Q (z₀, tail₂)
          ∂Measure.pi fun _ : Fin r => μ) μ
        exact hQint.integral_prod_left
      have hIndPoint (z₀ : E) :
          entropy ν (secFun z₀) ≤ ∑ j : Fin (r + 1), K j z₀ := by
        have hsectionMeas : Measurable (secFun z₀) := by
          dsimp [secFun]
          fun_prop
        have hsectionBounds (tail : Fin (r + 1) → E) :
          ε ≤ secFun z₀ tail ∧ secFun z₀ tail ≤ B :=
          hBounds (Fin.cons z₀ tail)
        have hIH := ih (secFun z₀) hsectionMeas hsectionBounds
        simpa [K, secFun, hinsert0] using hIH
      have hsumInt : Integrable (fun z₀ => ∑ j : Fin (r + 1), K j z₀) μ := by
        exact integrable_finsetSum Finset.univ fun j _ => hKint j
      have hAtoSum : A ≤ ∑ j : Fin (r + 1), ∫ z₀, K j z₀ ∂μ := by
        calc
          A = ∫ z₀, entropy ν (secFun z₀) ∂μ := rfl
          _ ≤ ∫ z₀, ∑ j : Fin (r + 1), K j z₀ ∂μ :=
            integral_mono hAint hsumInt hIndPoint
          _ = ∑ j : Fin (r + 1), ∫ z₀, K j z₀ ∂μ := by
            rw [integral_finsetSum]
            exact fun j _ => hKint j
      have hKtransport (j : Fin (r + 1)) :
          (∫ z₀, K j z₀ ∂μ) =
            ∫ tail, entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 2) => E) j.succ).symm (z, tail)))
              ∂Measure.pi fun _ : Fin (r + 1) => μ := by
        exact entropy_piFin_jSucc_transport μ f B hB0 hf
          (fun D => le_trans hε.le (hBounds D).1)
          (fun D => (hBounds D).2) j
      have htarget :
          (∑ i : Fin (r + 2),
            ∫ tail : Fin (r + 1) → E,
              entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (r + 2) => E) i).symm (z, tail)))
              ∂Measure.pi fun _ : Fin (r + 1) => μ) =
            B₀ + ∑ j : Fin (r + 1), ∫ z₀, K j z₀ ∂μ := by
        rw [Fin.sum_univ_succ]
        have hzero :
            (∫ tail : Fin (r + 1) → E,
              entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (r + 2) => E) 0).symm (z, tail)))
              ∂Measure.pi fun _ : Fin (r + 1) => μ) = B₀ := by
          change (∫ tail : Fin (r + 1) → E,
            entropy μ (fun z₀ => f ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 2) => E) 0).symm (z₀, tail)))
            ∂Measure.pi fun _ : Fin (r + 1) => μ) =
            ∫ tail, entropy μ (fun z₀ => f (Fin.cons z₀ tail))
              ∂Measure.pi fun _ : Fin (r + 1) => μ
          apply integral_congr_ae
          filter_upwards with tail
          apply congrArg (entropy μ)
          funext z₀
          exact congrArg f (piFinSuccAbove_zero_symm_apply_cons z₀ tail)
        rw [hzero]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact (hKtransport j).symm
      calc
        entropy (Measure.pi fun _ : Fin (r + 2) => μ) f ≤ A + B₀ := hpairFull
        _ ≤ (∑ j : Fin (r + 1), ∫ z₀, K j z₀ ∂μ) + B₀ :=
          by nlinarith [hAtoSum]
        _ = ∑ i : Fin (r + 2),
            ∫ tail : Fin (r + 1) → E,
              entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (r + 2) => E) i).symm (z, tail)))
              ∂Measure.pi fun _ : Fin (r + 1) => μ := by
          rw [htarget]
          ring

/-- Coefficient-one finite entropy subadditivity for bounded positive tests
under the actual finite i.i.d. product law. -/
theorem entropy_piFin_succ_subadditive_bounded_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : (Fin (r + 1) → EuclideanSpace ℝ ι) → ℝ)
    (ε B : ℝ) (hf : Measurable f) (hε : 0 < ε)
    (hBounds : ∀ D, ε ≤ f D ∧ f D ≤ B) :
    entropy (Measure.pi fun _ : Fin (r + 1) => μ) f ≤
      ∑ i : Fin (r + 1),
        ∫ tail : Fin r → EuclideanSpace ℝ ι,
          entropy μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm
              (z, tail))) ∂Measure.pi fun _ : Fin r => μ := by
  apply entropy_piFin_succ_subadditive_of_two_factor μ _ f ε B hf hε hBounds
  intro s ν hν F ε B hF hε hBounds
  exact entropy_two_factor_subadditive_bounded_positive
    μ ν F ε B hF hε hBounds

#print axioms LOOConcentration.Revision.entropy_piFin_succ_subadditive_of_two_factor
#print axioms LOOConcentration.Revision.entropy_piFin_succ_subadditive_bounded_positive

end LOOConcentration.Revision
