import LOOConcentration.FunctionalInequalities.FiniteVarianceTensorization

/-!
# Finite-product Efron–Stein inequality

The bounded variance inequality is iterated over a finite i.i.d. product.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

private theorem square_norm_bound {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    ‖x ^ 2‖ ≤ B ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ B ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hB (abs_nonneg x))
      nlinarith [hprod]

private theorem integralVariance_section_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    Integrable (fun y => integralVariance μ (fun x => F (x, y))) ν := by
  let mean : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let second : β → ℝ := fun y => ∫ x, F (x, y) ^ 2 ∂μ
  let variance : β → ℝ := fun y => integralVariance μ (fun x => F (x, y))
  have hF2 : Measurable (fun p : α × β => F p ^ 2) := hF.pow_const 2
  have hmeanStrong : StronglyMeasurable mean := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hsecondStrong : StronglyMeasurable second := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ^ 2 ∂μ)
    exact hF2.stronglyMeasurable.integral_prod_left'
  have hmeanMeas : Measurable mean := hmeanStrong.measurable
  have hsecondMeas : Measurable second := hsecondStrong.measurable
  have hvarMeas : Measurable variance := by
    change Measurable (fun y => second y - mean y ^ 2)
    exact hsecondMeas.sub (hmeanMeas.pow_const 2)
  have hmeanBound (y : β) : |mean y| ≤ B := by
    have hsectionMeas : Measurable (fun x : α => F (x, y)) :=
      hF.comp (measurable_prodMk_right (y := y))
    have hsectionInt : Integrable (fun x : α => F (x, y)) μ :=
      bounded_measurable_integrable hsectionMeas B fun x => by
        simpa only [Real.norm_eq_abs] using hFbound (x, y)
    calc
      |mean y| ≤ ∫ x, |F (x, y)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : α, B ∂μ :=
        integral_mono hsectionInt.abs (integrable_const B) fun x => hFbound (x, y)
      _ = B := by simp
  have hsecondSectionInt (y : β) : Integrable (fun x : α => F (x, y) ^ 2) μ := by
    have hsqMeas : Measurable (fun x : α => F (x, y) ^ 2) :=
      hF2.comp (measurable_prodMk_right (y := y))
    exact bounded_measurable_integrable hsqMeas (B ^ 2) fun x => by
      exact square_norm_bound hB (hFbound (x, y))
  have hsecondNonneg (y : β) : 0 ≤ second y := by
    calc
      0 = ∫ _ : α, (0 : ℝ) ∂μ := by simp
      _ ≤ ∫ x, F (x, y) ^ 2 ∂μ :=
        integral_mono (by simp) (hsecondSectionInt y) fun x => sq_nonneg _
  have hsecondUpper (y : β) : second y ≤ B ^ 2 := by
    calc
      second y ≤ ∫ _ : α, B ^ 2 ∂μ :=
        integral_mono (hsecondSectionInt y) (integrable_const _) fun x => by
          have hprod := mul_nonneg
            (sub_nonneg.mpr (hFbound (x, y)))
            (add_nonneg hB (abs_nonneg (F (x, y))))
          nlinarith [hprod, sq_abs (F (x, y))]
      _ = B ^ 2 := by simp
  have hsecondBound (y : β) : |second y| ≤ B ^ 2 := by
    rw [abs_of_nonneg (hsecondNonneg y)]
    exact hsecondUpper y
  have hvariance_eq (y : β) : variance y = second y - mean y ^ 2 := by
    simp [variance, integralVariance, mean, second]
  have hvarianceBound (y : β) : ‖variance y‖ ≤ 2 * B ^ 2 := by
    rw [Real.norm_eq_abs, hvariance_eq]
    calc
      |second y - mean y ^ 2| ≤ |second y| + |mean y ^ 2| := abs_sub _ _
      _ ≤ B ^ 2 + B ^ 2 := add_le_add (hsecondBound y) (by
        rw [abs_of_nonneg (sq_nonneg (mean y))]
        have hprod := mul_nonneg
          (sub_nonneg.mpr (hmeanBound y))
          (add_nonneg hB (abs_nonneg (mean y)))
        nlinarith [hprod, sq_abs (mean y)])
      _ = 2 * B ^ 2 := by ring
  exact bounded_measurable_integrable hvarMeas (2 * B ^ 2) hvarianceBound

/-- For bounded measurable functions on a finite i.i.d. product with at least
one coordinate, variance is bounded by the sum of its expected conditional
coordinate variances. -/
theorem integralVariance_piFin_succ_efronStein
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, ∀ (f : (Fin (n + 1) → E) → ℝ) (B : ℝ), 0 ≤ B →
      Measurable f → (∀ D, |f D| ≤ B) →
      integralVariance (Measure.pi fun _ : Fin (n + 1) => μ) f ≤
        ∑ i : Fin (n + 1),
          ∫ tail : Fin n → E,
            integralVariance μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => E) i).symm (z, tail)))
              ∂Measure.pi (fun _ : Fin n => μ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro f B hB hf hfbound
      cases n with
      | zero =>
          let e : (Fin 1 → E) ≃ᵐ E × (Fin 0 → E) :=
            MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => E) 0
          let F : E × (Fin 0 → E) → ℝ := fun p => f (e.symm p)
          let energy : Fin 1 → ℝ := fun i =>
            ∫ tail : Fin 0 → E,
              integralVariance μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin 1 => E) i).symm (z, tail))) ∂Measure.pi (fun _ : Fin 0 => μ)
          have hF : Measurable F := hf.comp e.symm.measurable
          have hFbound (p : E × (Fin 0 → E)) : |F p| ≤ B := hfbound (e.symm p)
          have haverage :
              integralVariance μ (fun z => ∫ tail : Fin 0 → E, F (z, tail)
                ∂Measure.pi (fun _ : Fin 0 => μ)) ≤
                ∫ tail : Fin 0 → E, integralVariance μ (fun z => F (z, tail))
                  ∂Measure.pi (fun _ : Fin 0 => μ) :=
            integralVariance_average_le μ (Measure.pi fun _ : Fin 0 => μ) F B hB hF hFbound
          have hsplit := integralVariance_piFin_succ_split μ f B hB hf hfbound
            (0 : Fin 1)
          have hsplit' : integralVariance (Measure.pi fun _ : Fin 1 => μ) f =
              (∫ z, integralVariance (Measure.pi fun _ : Fin 0 => μ)
                (fun tail => f (e.symm (z, tail))) ∂μ) +
              integralVariance μ (fun z => ∫ tail, F (z, tail)
                ∂Measure.pi (fun _ : Fin 0 => μ)) := by
            simpa [F, e] using hsplit
          calc
            integralVariance (Measure.pi fun _ : Fin 1 => μ) f =
                integralVariance μ (fun z => ∫ tail, F (z, tail)
                  ∂Measure.pi (fun _ : Fin 0 => μ)) := by
              rw [hsplit']
              simp [integralVariance_piFin_zero_eq_zero, e]
            _ ≤ ∫ tail, integralVariance μ (fun z => F (z, tail))
                ∂Measure.pi (fun _ : Fin 0 => μ) := haverage
            _ = ∑ i : Fin 1, energy i := by
              rw [Fin.sum_univ_succ]
              simp only [Fin.sum_univ_zero, add_zero]
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun tail => by
                simp [F, e]
      | succ n =>
          let e0 : (Fin (n + 2) → E) ≃ᵐ E × (Fin (n + 1) → E) :=
            MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => E) 0
          let etail (j : Fin (n + 1)) :
              (Fin (n + 1) → E) ≃ᵐ E × (Fin n → E) :=
            MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) j
          let ν : Measure (Fin (n + 1) → E) := Measure.pi fun _ : Fin (n + 1) => μ
          let ν₀ : Measure (Fin n → E) := Measure.pi fun _ : Fin n => μ
          let F : E × (Fin (n + 1) → E) → ℝ := fun p => f (e0.symm p)
          let energy : Fin (n + 2) → ℝ := fun i =>
            ∫ tail : Fin (n + 1) → E,
              integralVariance μ (fun z => f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (n + 2) => E) i).symm (z, tail))) ∂ν
          let coordinateEnergy : Fin (n + 1) → E → ℝ := fun j z₀ =>
            ∫ tail₂ : Fin n → E,
              integralVariance μ (fun z => f (e0.symm (z₀, (etail j).symm (z, tail₂)))) ∂ν₀
          have hF : Measurable F := hf.comp e0.symm.measurable
          have hFbound (p : E × (Fin (n + 1) → E)) : |F p| ≤ B := hfbound (e0.symm p)
          have hsectionInt :
              Integrable (fun z₀ => integralVariance ν (fun tail => F (z₀, tail))) μ := by
            let G : (Fin (n + 1) → E) × E → ℝ := fun p => F (p.2, p.1)
            have hG : Measurable G := hF.comp measurable_swap
            have hGbound (p : (Fin (n + 1) → E) × E) : |G p| ≤ B := hFbound (p.2, p.1)
            change Integrable (fun z₀ => integralVariance ν (fun tail => G (tail, z₀))) μ
            exact integralVariance_section_integrable ν μ G B hB hG hGbound
          have hcoordinateKernelInt (j : Fin (n + 1)) :
              Integrable
                (fun p : E × (Fin n → E) =>
                  integralVariance μ
                    (fun z => f (e0.symm (p.1, (etail j).symm (z, p.2)))))
                (μ.prod ν₀) := by
            let G : E × (E × (Fin n → E)) → ℝ := fun p =>
              f (e0.symm (p.2.1, (etail j).symm (p.1, p.2.2)))
            have hG : Measurable G := by
              apply hf.comp
              fun_prop
            have hGbound (p : E × (E × (Fin n → E))) : |G p| ≤ B :=
              hfbound (e0.symm (p.2.1, (etail j).symm (p.1, p.2.2)))
            change Integrable (fun p : E × (Fin n → E) =>
              integralVariance μ (fun z => G (z, p))) (μ.prod ν₀)
            exact integralVariance_section_integrable μ (μ.prod ν₀) G B hB hG hGbound
          have hcoordinateInt (j : Fin (n + 1)) :
              Integrable (fun z₀ => coordinateEnergy j z₀) μ := by
            change Integrable (fun z₀ => ∫ tail₂,
              integralVariance μ (fun z => f (e0.symm (z₀, (etail j).symm (z, tail₂)))) ∂ν₀) μ
            exact (hcoordinateKernelInt j).integral_prod_left
          have hcoordinateSumInt :
              Integrable (fun z₀ => ∑ j : Fin (n + 1), coordinateEnergy j z₀) μ :=
            integrable_finsetSum Finset.univ (fun j _ => hcoordinateInt j)
          have hsectionInduction (z₀ : E) :
              integralVariance ν (fun tail => F (z₀, tail)) ≤
                ∑ j : Fin (n + 1), coordinateEnergy j z₀ := by
            have hIH := ih n (Nat.lt_succ_self n)
              (fun tail => F (z₀, tail)) B hB
              (hF.comp (measurable_prodMk_left (x := z₀)))
              (fun tail => hFbound (z₀, tail))
            simpa [coordinateEnergy, e0, etail, ν, ν₀, F] using hIH
          have hsectionIntegralBound :
              (∫ z₀, integralVariance ν (fun tail => F (z₀, tail)) ∂μ) ≤
                ∫ z₀, ∑ j : Fin (n + 1), coordinateEnergy j z₀ ∂μ :=
            integral_mono hsectionInt hcoordinateSumInt hsectionInduction
          have hfiniteSumIntegral :
              (∫ z₀, ∑ j : Fin (n + 1), coordinateEnergy j z₀ ∂μ) =
                ∑ j : Fin (n + 1), ∫ z₀, coordinateEnergy j z₀ ∂μ := by
            exact integral_finsetSum Finset.univ (fun j _ => hcoordinateInt j)
          have htransport (j : Fin (n + 1)) :
              (∫ z₀, coordinateEnergy j z₀ ∂μ) = energy j.succ := by
            simpa [coordinateEnergy, energy, e0, etail, ν, ν₀] using
              (integralVariance_piFin_jSucc_transport μ f B hB hf hfbound j)
          have haverage :
              integralVariance μ (fun z₀ => ∫ tail, F (z₀, tail) ∂ν) ≤
                ∫ tail, integralVariance μ (fun z₀ => F (z₀, tail)) ∂ν :=
            integralVariance_average_le μ ν F B hB hF hFbound
          have hsplit := integralVariance_piFin_succ_split μ f B hB hf hfbound
            (0 : Fin (n + 2))
          have hsuccSum :
              (∑ j : Fin (n + 1), ∫ z₀, coordinateEnergy j z₀ ∂μ) =
                ∑ j : Fin (n + 1), energy j.succ :=
            Finset.sum_congr rfl fun j _ => htransport j
          have hzeroCoord :
              (∫ tail, integralVariance μ (fun z₀ => F (z₀, tail)) ∂ν) = energy 0 := by
            simp [energy, F, e0, ν]
          calc
            integralVariance (Measure.pi fun _ : Fin (n + 2) => μ) f =
                (∫ z₀, integralVariance ν (fun tail => F (z₀, tail)) ∂μ) +
                  integralVariance μ (fun z₀ => ∫ tail, F (z₀, tail) ∂ν) := by
              simpa [ν, F, e0] using hsplit
            _ ≤
                (∫ z₀, ∑ j : Fin (n + 1), coordinateEnergy j z₀ ∂μ) +
                  ∫ tail, integralVariance μ (fun z₀ => F (z₀, tail)) ∂ν :=
              add_le_add hsectionIntegralBound haverage
            _ = energy 0 + ∑ j : Fin (n + 1), energy j.succ := by
              rw [hfiniteSumIntegral]
              rw [hsuccSum, hzeroCoord]
              ring
            _ = ∑ i : Fin (n + 2), energy i := by
              symm
              exact Fin.sum_univ_succ (fun i : Fin (n + 2) => energy i)

#print axioms LOOConcentration.integralVariance_piFin_succ_efronStein

end LOOConcentration
