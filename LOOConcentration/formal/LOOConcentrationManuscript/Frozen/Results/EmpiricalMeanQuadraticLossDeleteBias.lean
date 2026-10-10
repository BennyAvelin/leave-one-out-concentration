import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_quadraticLoss_delete_bias
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (n : ℕ) (X : Fin (n + 3) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) (i : Fin (n + 2)) :
    |(∫ ω, (empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω) ^ 2 ∂P) -
      (∫ ω, (empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω) ^ 2 ∂P)| =
      variance (id : ℝ → ℝ) μ / ((n + 2 : ℝ) * (n + 1 : ℝ))
:= by
  have contrast_sq_integral
        {ι : Type} [Fintype ι]
      (Y : ι → Ω → ℝ) (c : ι → ℝ)
      (hLaw : ∀ i, IdentDistrib (Y i) (id : ℝ → ℝ) P μ)
      (hInd : iIndepFun Y P)
      (hc : ∑ i, c i = 0) :
      ∫ ω, (∑ i, c i * Y i ω) ^ 2 ∂P =
        variance (id : ℝ → ℝ) μ * ∑ i, c i ^ 2 := by
    classical
    have hIdLp : MemLp (id : ℝ → ℝ) 2 μ := by
      exact (memLp_two_iff_integrable_sq (μ := μ) (f := id) (by fun_prop)).2 hSecond
    have hYLp : ∀ i, MemLp (Y i) 2 P := by
      intro i
      exact ((hLaw i).memLp_iff (p := 2)).2 hIdLp
    let W : ι → Ω → ℝ := fun i ω => c i * Y i ω
    have hWInd : iIndepFun W P :=
      hInd.comp (fun i x => c i * x) (fun i => measurable_const_mul (c i))
    have hWLp : ∀ i, MemLp (W i) 2 P := by
      intro i
      exact (hYLp i).const_mul (c i)
    have hPair : Set.Pairwise (↑(Finset.univ : Finset ι))
        (fun i j => W i ⟂ᵢ[P] W j) := by
      intro i hi j hj hij
      exact hWInd.indepFun hij
    have hZLp : MemLp (fun ω => ∑ i, W i ω) 2 P := by
      convert (memLp_finsetSum (s := Finset.univ)
        (fun i _ => hWLp i)) using 1
    have hZMean : ∫ ω, (∑ i, W i ω) ∂P = 0 := by
      calc
        ∫ ω, (∑ i, W i ω) ∂P = ∑ i, ∫ ω, W i ω ∂P := by
          convert (integral_finsetSum (μ := P) Finset.univ
            (fun i _ => (hWLp i).integrable one_le_two)) using 1
        _ = ∑ i, c i * ∫ x, id x ∂μ := by
          apply Finset.sum_congr rfl
          intro i hi
          change ∫ ω, c i * Y i ω ∂P = _
          rw [integral_const_mul, (hLaw i).integral_eq]
        _ = 0 := by
          rw [← Finset.sum_mul, hc]
          simp
    have hZVar : variance (fun ω => ∑ i, W i ω) P =
        variance (id : ℝ → ℝ) μ * ∑ i, c i ^ 2 := by
      have hVarSum : variance (fun ω => ∑ i, W i ω) P =
          ∑ i, variance (W i) P := by
        calc
          variance (fun ω => ∑ i, W i ω) P = variance (∑ i, W i) P := by
            congr 1
            funext ω
            simp only [Finset.sum_apply]
          _ = ∑ i, variance (W i) P :=
            IndepFun.variance_sum (μ := P) (s := Finset.univ)
              (fun i _ => hWLp i) hPair
      rw [hVarSum]
      calc
        ∑ i, variance (W i) P = ∑ i, c i ^ 2 * variance (Y i) P := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [W]
          rw [variance_const_mul]
        _ = ∑ i, c i ^ 2 * variance (id : ℝ → ℝ) μ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hLaw i).variance_eq]
        _ = variance (id : ℝ → ℝ) μ * ∑ i, c i ^ 2 := by
          rw [← Finset.sum_mul]
          ring
    calc
      ∫ ω, (∑ i, c i * Y i ω) ^ 2 ∂P =
          ∫ ω, ((∑ i, W i ω) - ∫ ω, (∑ i, W i ω) ∂P) ^ 2 ∂P := by
        simp only [W]
        rw [hZMean]
        simp
      _ = variance (fun ω => ∑ i, W i ω) P := by
        exact (variance_eq_integral hZLp.aemeasurable).symm
      _ = variance (id : ℝ → ℝ) μ * ∑ i, c i ^ 2 := hZVar

  have deletedIndexMap_injective {n : ℕ} (i : Fin (n + 2)) :
        Function.Injective
          (fun j : Fin (n + 2) =>
            Fin.lastCases (motive := fun _ => Fin (n + 3)) i.castSucc
              (fun k : Fin (n + 1) => (i.succAbove k).castSucc) j) := by
      intro a
      change ∀ b,
        Fin.lastCases (motive := fun _ => Fin (n + 3)) i.castSucc
          (fun k : Fin (n + 1) => (i.succAbove k).castSucc) a =
        Fin.lastCases (motive := fun _ => Fin (n + 3)) i.castSucc
          (fun k : Fin (n + 1) => (i.succAbove k).castSucc) b → a = b
      intro b hab
      revert b hab
      induction a using Fin.lastCases with
      | last =>
        intro b hab
        revert hab
        induction b using Fin.lastCases with
        | last => intro; rfl
        | cast b =>
          intro hab
          simp only [Fin.lastCases_castSucc] at hab
          simp only [Fin.lastCases_last] at hab
          have h' : i.succAbove b = i := Fin.castSucc_injective (n + 2) hab.symm
          exact (Fin.succAbove_ne i b h').elim
      | cast a =>
        intro b hab
        revert hab
        induction b using Fin.lastCases with
        | last =>
          intro hab
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at hab
          have h' : i.succAbove a = i := Fin.castSucc_injective (n + 2) hab
          exact (Fin.succAbove_ne i a h').elim
        | cast b =>
          intro hab
          simp only [Fin.lastCases_castSucc] at hab
          have h' : i.succAbove a = i.succAbove b :=
            Fin.castSucc_injective (n + 2) hab
          exact congrArg Fin.castSucc (Fin.succAbove_right_injective h')

  classical
  let cFull : Fin (n + 3) → ℝ :=
    Fin.lastCases (-1) (fun _ => ((n + 2 : ℕ) : ℝ)⁻¹)
  have hFullZero : ∑ j : Fin (n + 3), cFull j = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp [cFull, Fin.lastCases_castSucc, Fin.lastCases_last,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add]
    have hden : (↑n : ℝ) + 2 ≠ 0 := by positivity
    rw [mul_inv_cancel₀ hden]
    ring
  have hFullSq : ∑ j : Fin (n + 3), cFull j ^ 2 =
      1 + ((n + 2 : ℕ) : ℝ)⁻¹ := by
    rw [Fin.sum_univ_castSucc]
    simp [cFull, Fin.lastCases_castSucc, Fin.lastCases_last,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add]
    have hden : (↑n : ℝ) + 2 ≠ 0 := by positivity
    have hinv : ((↑n : ℝ) + 2) * (((↑n : ℝ) + 2) ^ 2)⁻¹ =
        ((↑n : ℝ) + 2)⁻¹ := by
      field_simp [hden]
    rw [hinv]
    ring
  have hFullContrast :
      ∀ ω, empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω =
      ∑ j : Fin (n + 3), cFull j * X j ω := by
    intro ω
    simp only [empiricalMean]
    rw [Fin.sum_univ_castSucc (fun j : Fin (n + 3) => cFull j * X j ω)]
    simp only [cFull, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [show ((n + 2 : ℕ) : ℝ)⁻¹ *
        (∑ j : Fin (n + 2), X j.castSucc ω) =
        ∑ j : Fin (n + 2), ((n + 2 : ℕ) : ℝ)⁻¹ * X j.castSucc ω by
          simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (n + 2)))
            (fun j => X j.castSucc ω) ((n + 2 : ℕ)⁻¹ : ℝ))]
    ring
  let delMap : Fin (n + 2) → Fin (n + 3) :=
    Fin.lastCases (i.castSucc)
      (fun j : Fin (n + 1) => (i.succAbove j).castSucc)
  let YDel : Fin (n + 2) → Ω → ℝ := fun j => X (delMap j)
  let cDel : Fin (n + 2) → ℝ :=
    Fin.lastCases (-1) (fun _ => ((n + 1 : ℕ) : ℝ)⁻¹)
  have hDelInd : iIndepFun YDel P := by
    exact hInd.precomp (deletedIndexMap_injective i)
  have hDelLaw : ∀ j, IdentDistrib (YDel j) (id : ℝ → ℝ) P μ := by
    intro j
    exact hLaw (delMap j)
  have hDelZero : ∑ j : Fin (n + 2), cDel j = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp [cDel, Fin.lastCases_castSucc, Fin.lastCases_last,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add]
    have hden : (↑n : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_inv_cancel₀ hden]
    ring
  have hDelSq : ∑ j : Fin (n + 2), cDel j ^ 2 =
      1 + ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [Fin.sum_univ_castSucc]
    simp [cDel, Fin.lastCases_castSucc, Fin.lastCases_last,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add]
    have hden : (↑n : ℝ) + 1 ≠ 0 := by positivity
    have hinv : ((↑n : ℝ) + 1) * (((↑n : ℝ) + 1) ^ 2)⁻¹ =
        ((↑n : ℝ) + 1)⁻¹ := by
      field_simp [hden]
    rw [hinv]
    ring
  have hDelContrast :
      ∀ ω, empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω =
      ∑ j : Fin (n + 2), cDel j * YDel j ω := by
    intro ω
    simp only [empiricalMean]
    rw [Fin.sum_univ_castSucc (fun j : Fin (n + 2) => cDel j * YDel j ω)]
    simp [cDel, YDel, delMap, Fin.lastCases_castSucc, Fin.lastCases_last, Nat.cast_add]
    have hmul : ((↑n : ℝ) + 1)⁻¹ *
        (∑ j : Fin (n + 1), X ((i.succAbove j).castSucc) ω) =
        ∑ j : Fin (n + 1), ((↑n : ℝ) + 1)⁻¹ *
          X ((i.succAbove j).castSucc) ω := by
      simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun j => X ((i.succAbove j).castSucc) ω)
        (((↑n : ℝ) + 1)⁻¹))
    rw [hmul]
    simp only [sub_eq_add_neg]
  have hDelMoment :
      ∫ ω, (empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω) ^ 2 ∂P =
      variance (id : ℝ → ℝ) μ * (1 + ((n + 1 : ℕ) : ℝ)⁻¹) := by
    simp only [hDelContrast]
    rw [contrast_sq_integral YDel cDel hDelLaw hDelInd hDelZero]
    rw [hDelSq]
  have hFullMoment :
      ∫ ω, (empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω) ^ 2 ∂P =
      variance (id : ℝ → ℝ) μ * (1 + ((n + 2 : ℕ) : ℝ)⁻¹) := by
    simp only [hFullContrast]
    rw [contrast_sq_integral X cFull hLaw hInd hFullZero]
    rw [hFullSq]
  rw [hDelMoment, hFullMoment]
  have hpos :
      0 ≤ variance (id : ℝ → ℝ) μ *
        (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) := by
    apply mul_nonneg (variance_nonneg _ _)
    have hden1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
    have hden2 : (↑n : ℝ) + 2 ≠ 0 := by positivity
    have hstep : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (n + 1)
    field_simp [hden1, hden2]
    simp only [zero_mul]
    exact sub_nonneg.mpr hstep
  rw [show variance (id : ℝ → ℝ) μ * (1 + ((n + 1 : ℕ) : ℝ)⁻¹) -
      variance (id : ℝ → ℝ) μ * (1 + ((n + 2 : ℕ) : ℝ)⁻¹) =
      variance (id : ℝ → ℝ) μ *
        (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) by ring,
    abs_of_nonneg hpos]
  have hden1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
  have hden2 : (↑n : ℝ) + 2 ≠ 0 := by positivity
  have hden : ((↑n : ℝ) + 2) * ((↑n : ℝ) + 1) ≠ 0 :=
    mul_ne_zero hden2 hden1
  push_cast
  field_simp [hden1, hden2, hden]
  ring

end LOOConcentration.Manuscript
