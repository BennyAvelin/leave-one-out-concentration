import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_absoluteLoss_delete_bias
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (n : ℕ) (X : Fin (n + 3) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) (i : Fin (n + 2)) :
    |(∫ ω, |empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω| ∂P) -
      (∫ ω, |empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω| ∂P)| ≤
      2 * (∫ x : ℝ, |x| ∂μ) / (n + 1 : ℝ)
:= by
  classical
  have hIdLp : MemLp (id : ℝ → ℝ) 2 μ := by
    exact (memLp_two_iff_integrable_sq (μ := μ) (f := id) (by fun_prop)).2 hSecond
  have hXInt : ∀ k : Fin (n + 3), Integrable (X k) P := by
    intro k
    exact (((hLaw k).memLp_iff (p := 2)).2 hIdLp).integrable one_le_two
  have hXAbsInt : ∀ k : Fin (n + 3), Integrable (fun ω => |X k ω|) P := by
    intro k
    exact (hXInt k).abs
  let m : ℝ := ∫ x : ℝ, |x| ∂μ
  have hXAbsEq : ∀ k : Fin (n + 3), (∫ ω, |X k ω| ∂P) = m := by
    intro k
    simpa only [Real.norm_eq_abs, id_eq, m] using (hLaw k).norm.integral_eq
  have hm : 0 ≤ m := by
    exact integral_nonneg (fun x => abs_nonneg x)

  let cDel : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  let cFull : ℝ := ((n + 2 : ℕ) : ℝ)⁻¹
  let delIndex : Fin (n + 1) → Fin (n + 3) :=
    fun j => (i.succAbove j).castSucc
  let delSet : Finset (Fin (n + 3)) := Finset.univ.image delIndex
  have hDelIndexInj : Function.Injective delIndex := by
    intro a b hab
    apply Fin.succAbove_right_injective
    exact Fin.castSucc_injective (n + 2) hab
  have hDelSum (ω : Ω) :
      (∑ j : Fin (n + 1), X (delIndex j) ω) =
        ∑ k ∈ delSet, X k ω := by
    simpa only [delSet, delIndex] using
      (Finset.sum_image (s := (Finset.univ : Finset (Fin (n + 1))))
        (g := fun j : Fin (n + 1) => (i.succAbove j).castSucc)
        (f := fun k : Fin (n + 3) => X k ω)
        hDelIndexInj.injOn).symm
  let A : Ω → ℝ := fun ω => cDel * ∑ k ∈ delSet, X k ω
  let Yi : Ω → ℝ := fun ω => X i.castSucc ω
  let B : Ω → ℝ := fun ω => cFull * ∑ j : Fin (n + 2), X j.castSucc ω
  let Z : Ω → ℝ := fun ω => X (Fin.last (n + 2)) ω

  have hXiNot : i.castSucc ∉ delSet := by
    intro hi
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
    exact (Fin.succAbove_ne i j (Fin.castSucc_injective (n + 2) hj)).elim
  have hZNot : Fin.last (n + 2) ∉ delSet := by
    intro hz
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hz
    exact (Fin.castSucc_ne_last _ ) hj
  have hDelIndYi : (fun ω => ∑ k ∈ delSet, X k ω) ⟂ᵢ[P] Yi := by
    have h := hInd.indepFun_finsetSum_of_notMem₀
      (fun k => (hLaw k).aemeasurable_fst) hXiNot
    apply h.congr
    · filter_upwards [] with ω
      simp only [Finset.sum_apply]
    · rfl
  have hDelIndZ : (fun ω => ∑ k ∈ delSet, X k ω) ⟂ᵢ[P] Z := by
    have h := hInd.indepFun_finsetSum_of_notMem₀
      (fun k => (hLaw k).aemeasurable_fst) hZNot
    apply h.congr
    · filter_upwards [] with ω
      simp only [Finset.sum_apply]
    · rfl
  have hAIndYi : A ⟂ᵢ[P] Yi := by
    change ((fun x : ℝ => cDel * x) ∘
      (fun ω => ∑ k ∈ delSet, X k ω)) ⟂ᵢ[P] Yi
    exact hDelIndYi.comp (measurable_const_mul cDel) measurable_id
  have hAIndZ : A ⟂ᵢ[P] Z := by
    change ((fun x : ℝ => cDel * x) ∘
      (fun ω => ∑ k ∈ delSet, X k ω)) ⟂ᵢ[P] Z
    exact hDelIndZ.comp (measurable_const_mul cDel) measurable_id

  have hAInt : Integrable A P := by
    exact (integrable_finsetSum delSet (fun k hk => hXInt k)).const_mul cDel
  have hBInt : Integrable B P := by
    exact (integrable_finsetSum Finset.univ
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin (n + 2)))) =>
        hXInt j.castSucc)).const_mul cFull
  have hYiInt : Integrable Yi P := hXInt i.castSucc
  have hZInt : Integrable Z P := hXInt (Fin.last (n + 2))
  have hAAbsInt : Integrable (fun ω => |A ω|) P := hAInt.abs
  have hYiAbsInt : Integrable (fun ω => |Yi ω|) P := hYiInt.abs
  have hZAbsInt : Integrable (fun ω => |Z ω|) P := hZInt.abs
  have hHeldInt : Integrable (fun ω => |A ω - Yi ω|) P := (hAInt.sub hYiInt).abs
  have hFreshInt : Integrable (fun ω => |A ω - Z ω|) P := (hAInt.sub hZInt).abs
  have hFullInt : Integrable (fun ω => |B ω - Z ω|) P := (hBInt.sub hZInt).abs

  have hAEM : AEMeasurable A P := hAInt.aemeasurable
  have hYiEM : AEMeasurable Yi P := (hLaw i.castSucc).aemeasurable_fst
  have hZEM : AEMeasurable Z P := (hLaw (Fin.last (n + 2))).aemeasurable_fst
  have hPair : IdentDistrib (fun ω => (A ω, Yi ω))
      (fun ω => (A ω, Z ω)) P P := by
    refine ⟨hAEM.prodMk hYiEM, hAEM.prodMk hZEM, ?_⟩
    calc
      P.map (fun ω => (A ω, Yi ω)) = (P.map A).prod (P.map Yi) :=
        hAIndYi.map_prod_eq_prod_map_map hAEM hYiEM
      _ = (P.map A).prod (P.map Z) := by
        rw [(hLaw i.castSucc).map_eq, (hLaw (Fin.last (n + 2))).map_eq]
      _ = P.map (fun ω => (A ω, Z ω)) :=
        (hAIndZ.map_prod_eq_prod_map_map hAEM hZEM).symm
  have hLossPair : IdentDistrib (fun ω => |A ω - Yi ω|)
      (fun ω => |A ω - Z ω|) P P :=
    hPair.comp (u := fun p : ℝ × ℝ => |p.1 - p.2|) (by fun_prop)
  have hLossEq : (∫ ω, |A ω - Yi ω| ∂P) =
      ∫ ω, |A ω - Z ω| ∂P := hLossPair.integral_eq

  have hcDel : 0 ≤ cDel := by positivity
  have hSumAbsInt : Integrable (fun ω => ∑ k ∈ delSet, |X k ω|) P :=
    integrable_finsetSum delSet (fun k hk => hXAbsInt k)
  have hAvgAbsPoint (ω : Ω) : |A ω| ≤ cDel * ∑ k ∈ delSet, |X k ω| := by
    simp only [A, abs_mul, abs_of_nonneg hcDel]
    exact mul_le_mul_of_nonneg_left
      (Finset.abs_sum_le_sum_abs (fun k => X k ω) delSet) hcDel
  have hAvgAbsBound : (∫ ω, |A ω| ∂P) ≤ m := by
    have hRhsInt : Integrable (fun ω => cDel * ∑ k ∈ delSet, |X k ω|) P :=
      hSumAbsInt.const_mul cDel
    calc
      (∫ ω, |A ω| ∂P) ≤ ∫ ω, cDel * ∑ k ∈ delSet, |X k ω| ∂P :=
        integral_mono hAAbsInt hRhsInt hAvgAbsPoint
      _ = cDel * ∑ k ∈ delSet, ∫ ω, |X k ω| ∂P := by
        rw [integral_const_mul, integral_finsetSum delSet
          (fun k hk => hXAbsInt k)]
      _ = cDel * ∑ j : Fin (n + 1), ∫ ω, |X (delIndex j) ω| ∂P := by
        rw [Finset.sum_image hDelIndexInj.injOn]
      _ = cDel * ∑ j : Fin (n + 1), m := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact hXAbsEq (delIndex j)
      _ = m := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        dsimp [cDel]
        have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hden]

  have hHeldPoint (ω : Ω) : |A ω - Yi ω| ≤ |A ω| + |Yi ω| := by
    calc
      |A ω - Yi ω| = |A ω + -Yi ω| := by rw [sub_eq_add_neg]
      _ ≤ |A ω| + |-Yi ω| := abs_add_le _ _
      _ = |A ω| + |Yi ω| := by simp
  have hHeldAbsBound : (∫ ω, |A ω - Yi ω| ∂P) ≤ 2 * m := by
    calc
      (∫ ω, |A ω - Yi ω| ∂P) ≤ ∫ ω, |A ω| + |Yi ω| ∂P :=
        integral_mono hHeldInt (hAAbsInt.add hYiAbsInt) hHeldPoint
      _ = (∫ ω, |A ω| ∂P) + (∫ ω, |Yi ω| ∂P) :=
        integral_add hAAbsInt hYiAbsInt
      _ ≤ m + m := by
        rw [hXAbsEq i.castSucc]
        exact add_le_add hAvgAbsBound le_rfl
      _ = 2 * m := by ring

  have hFullSum (ω : Ω) :
      (∑ j : Fin (n + 2), X j.castSucc ω) =
        X i.castSucc ω + ∑ j : Fin (n + 1), X (delIndex j) ω := by
    simpa only [delIndex] using
      (Fin.sum_univ_succAbove (fun j : Fin (n + 2) => X j.castSucc ω) i)
  have hAB (ω : Ω) : A ω - B ω = cFull * (A ω - Yi ω) := by
    dsimp [A, B, Yi, cDel, cFull]
    rw [hFullSum ω, ← hDelSum ω]
    have hdenDel : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hdenFull : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hdenDel, hdenFull]
    push_cast
    ring
  have hABAbs (ω : Ω) : |A ω - B ω| = cFull * |A ω - Yi ω| := by
    rw [hAB ω, abs_mul, abs_of_nonneg (by positivity : 0 ≤ cFull)]
  have hABInt : Integrable (fun ω => |A ω - B ω|) P := (hAInt.sub hBInt).abs
  have hABAbsBound : (∫ ω, |A ω - B ω| ∂P) ≤
      2 * m / ((n + 2 : ℕ) : ℝ) := by
    calc
      (∫ ω, |A ω - B ω| ∂P) = cFull * (∫ ω, |A ω - Yi ω| ∂P) := by
        rw [show (fun ω => |A ω - B ω|) =
            (fun ω => cFull * |A ω - Yi ω|) from funext hABAbs,
          integral_const_mul]
      _ ≤ cFull * (2 * m) :=
        mul_le_mul_of_nonneg_left hHeldAbsBound (by positivity)
      _ = 2 * m / ((n + 2 : ℕ) : ℝ) := by
        simp [cFull, div_eq_mul_inv, mul_assoc]
        ring_nf

  have hReverse (ω : Ω) :
      abs (abs (A ω - Z ω) - abs (B ω - Z ω)) ≤ abs (A ω - B ω) := by
    calc
      abs (abs (A ω - Z ω) - abs (B ω - Z ω)) ≤
          abs ((A ω - Z ω) - (B ω - Z ω)) := abs_abs_sub_abs_le_abs_sub _ _
      _ = abs (A ω - B ω) := by congr 1; ring
  have hMainBound :
      |(∫ ω, |A ω - Yi ω| ∂P) - (∫ ω, |B ω - Z ω| ∂P)| ≤
        2 * m / ((n + 2 : ℕ) : ℝ) := by
    have hLossDiffInt : Integrable
        (fun ω => |A ω - Z ω| - |B ω - Z ω|) P := hFreshInt.sub hFullInt
    calc
      |(∫ ω, |A ω - Yi ω| ∂P) - (∫ ω, |B ω - Z ω| ∂P)| =
          ‖∫ ω, (|A ω - Z ω| - |B ω - Z ω|) ∂P‖ := by
        rw [hLossEq, integral_sub hFreshInt hFullInt]
        exact (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖|A ω - Z ω| - |B ω - Z ω|‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, |A ω - B ω| ∂P := by
        simpa only [Real.norm_eq_abs] using
          (integral_mono hLossDiffInt.norm hABInt hReverse)
      _ ≤ 2 * m / ((n + 2 : ℕ) : ℝ) := hABAbsBound
  have hDenOrder : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (n + 1)
  have hRateOrder : 2 * m / ((n + 2 : ℕ) : ℝ) ≤
      2 * m / ((n + 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * m)
      (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hDenOrder
  have hA_repr (ω : Ω) :
      empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) = A ω := by
    simp only [A, empiricalMean]
    rw [hDelSum ω]
  have hB_repr (ω : Ω) :
      empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) = B ω := by
    simp only [B, empiricalMean, cFull, Nat.cast_add, Nat.cast_one]
    push_cast
    ring
  have hHeldSource :
      (∫ ω, |empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω| ∂P) = ∫ ω, |A ω - Yi ω| ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hA_repr ω]
  have hFullSource :
      (∫ ω, |empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω| ∂P) = ∫ ω, |B ω - Z ω| ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hB_repr ω]
  calc
    |(∫ ω, |empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω| ∂P) -
      (∫ ω, |empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω| ∂P)| =
        |(∫ ω, |A ω - Yi ω| ∂P) - (∫ ω, |B ω - Z ω| ∂P)| := by
          rw [hHeldSource, hFullSource]
    _ ≤ 2 * m / ((n + 2 : ℕ) : ℝ) := hMainBound
    _ ≤ 2 * m / ((n + 1 : ℕ) : ℝ) := hRateOrder
    _ = 2 * (∫ x : ℝ, |x| ∂μ) / (n + 1 : ℝ) := by
      simp only [m, Nat.cast_add, Nat.cast_one]

end LOOConcentration.Manuscript
