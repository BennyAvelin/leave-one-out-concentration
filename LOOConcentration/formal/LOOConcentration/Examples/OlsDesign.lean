import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Order.OrderClosed
import LOOConcentration.Frozen.Foundations.DeleteAt

set_option autoImplicit false

namespace LOOConcentration

/-!
# Deterministic design quantities for the OLS example

The sample coordinates are the covariate and noise coordinates `(X_i,e_i)`.
The design norm below is the unnormalized Euclidean norm on all scalar
coordinates, as in the manuscript.
-/

/-- The sample mean of the covariate coordinates. -/
noncomputable def olsXBar {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  (∑ i : Fin N, (G i).1) / (N : ℝ)

/-- The sample mean of the noise coordinates. -/
noncomputable def olsEBar {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  (∑ i : Fin N, (G i).2) / (N : ℝ)

/-- The centered design sum of squares. -/
noncomputable def olsCenteredDesign {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  ∑ i : Fin N, ((G i).1 - olsXBar G) ^ 2

/-- The centered covariate-noise cross term. -/
noncomputable def olsCenteredCross {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  ∑ i : Fin N, ((G i).1 - olsXBar G) * ((G i).2 - olsEBar G)

/-- The totalized least-squares slope; real division is zero when the design is zero. -/
noncomputable def olsNoiseSlope {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  olsCenteredCross G / olsCenteredDesign G

/-- Squared Euclidean norm of all covariate and noise coordinates. -/
def olsNoiseNormSq {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  ∑ i : Fin N, ((G i).1 ^ 2 + (G i).2 ^ 2)

/-- Unnormalized Euclidean norm of all covariate and noise coordinates. -/
noncomputable def olsNoiseNorm {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  Real.sqrt (olsNoiseNormSq G)

/-- The OLS good set at sample size `n + 2`, with the finite coordinate condition
written as a universal quantifier. -/
def olsGoodSet (n : ℕ) : Set (Fin (n + 2) → ℝ × ℝ) :=
  {G | olsNoiseNorm G ≤ 3 * Real.sqrt (n + 2 : ℝ) ∧
    olsCenteredDesign G ≥ (n + 2 : ℝ) / 2 ∧
    ∀ i : Fin (n + 2), (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64}

private lemma continuous_fin_sum {N : ℕ} {α : Type*} [TopologicalSpace α]
    (f : Fin N → α → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => ∑ i : Fin N, f i x) := by
  exact continuous_finsetSum Finset.univ (fun i _ => hf i)

theorem continuous_olsXBar {N : ℕ} :
    Continuous (olsXBar : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsXBar
  exact (continuous_fin_sum (α := Fin N → ℝ × ℝ)
    (fun i (G : Fin N → ℝ × ℝ) => (G i).1)
    (fun i => continuous_fst.comp (continuous_apply i))).div_const (N : ℝ)

theorem continuous_olsEBar {N : ℕ} :
    Continuous (olsEBar : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsEBar
  exact (continuous_fin_sum (α := Fin N → ℝ × ℝ)
    (fun i (G : Fin N → ℝ × ℝ) => (G i).2)
    (fun i => continuous_snd.comp (continuous_apply i))).div_const (N : ℝ)

theorem continuous_olsCenteredDesign {N : ℕ} :
    Continuous (olsCenteredDesign : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsCenteredDesign
  apply continuous_fin_sum (α := Fin N → ℝ × ℝ)
  intro i
  exact ((continuous_fst.comp (continuous_apply i)).sub continuous_olsXBar).pow 2

theorem continuous_olsCenteredCross {N : ℕ} :
    Continuous (olsCenteredCross : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsCenteredCross
  apply continuous_fin_sum (α := Fin N → ℝ × ℝ)
  intro i
  exact (((continuous_fst.comp (continuous_apply i)).sub continuous_olsXBar).mul
    ((continuous_snd.comp (continuous_apply i)).sub continuous_olsEBar))

theorem measurable_olsNoiseSlope {N : ℕ} :
    Measurable (olsNoiseSlope : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsNoiseSlope
  exact continuous_olsCenteredCross.measurable.div continuous_olsCenteredDesign.measurable

theorem continuous_olsNoiseNormSq {N : ℕ} :
    Continuous (olsNoiseNormSq : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsNoiseNormSq
  apply continuous_fin_sum (α := Fin N → ℝ × ℝ)
  intro i
  exact (continuous_fst.comp (continuous_apply i)).pow 2 |>.add
    ((continuous_snd.comp (continuous_apply i)).pow 2)

theorem continuous_olsNoiseNorm {N : ℕ} :
    Continuous (olsNoiseNorm : (Fin N → ℝ × ℝ) → ℝ) := by
  unfold olsNoiseNorm
  exact Real.continuous_sqrt.comp continuous_olsNoiseNormSq

theorem measurable_olsXBar {N : ℕ} :
    Measurable (olsXBar : (Fin N → ℝ × ℝ) → ℝ) := continuous_olsXBar.measurable

theorem measurable_olsEBar {N : ℕ} :
    Measurable (olsEBar : (Fin N → ℝ × ℝ) → ℝ) := continuous_olsEBar.measurable

theorem measurable_olsCenteredDesign {N : ℕ} :
    Measurable (olsCenteredDesign : (Fin N → ℝ × ℝ) → ℝ) :=
  continuous_olsCenteredDesign.measurable

theorem measurable_olsCenteredCross {N : ℕ} :
    Measurable (olsCenteredCross : (Fin N → ℝ × ℝ) → ℝ) :=
  continuous_olsCenteredCross.measurable

theorem measurable_olsNoiseNormSq {N : ℕ} :
    Measurable (olsNoiseNormSq : (Fin N → ℝ × ℝ) → ℝ) :=
  continuous_olsNoiseNormSq.measurable

theorem measurable_olsNoiseNorm {N : ℕ} :
    Measurable (olsNoiseNorm : (Fin N → ℝ × ℝ) → ℝ) := continuous_olsNoiseNorm.measurable

theorem olsGoodSet_isClosed (n : ℕ) : IsClosed (olsGoodSet n) := by
  have hnorm : IsClosed {G : Fin (n + 2) → ℝ × ℝ |
      olsNoiseNorm G ≤ 3 * Real.sqrt (n + 2 : ℝ)} :=
    isClosed_le continuous_olsNoiseNorm continuous_const
  have hdesign : IsClosed {G : Fin (n + 2) → ℝ × ℝ |
      (n + 2 : ℝ) / 2 ≤ olsCenteredDesign G} :=
    isClosed_le continuous_const continuous_olsCenteredDesign
  have hcoord : ∀ i : Fin (n + 2), IsClosed
      {G : Fin (n + 2) → ℝ × ℝ | (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64} := by
    intro i
    exact isClosed_le ((continuous_fst.comp (continuous_apply i)).pow 2) continuous_const
  have hcoords : IsClosed
      {G : Fin (n + 2) → ℝ × ℝ | ∀ i : Fin (n + 2), (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64} := by
    rw [show {G : Fin (n + 2) → ℝ × ℝ |
        ∀ i : Fin (n + 2), (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64} =
        ⋂ i : Fin (n + 2),
          {G : Fin (n + 2) → ℝ × ℝ | (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64} by
      ext G
      simp]
    exact isClosed_iInter hcoord
  rw [show olsGoodSet n =
      {G : Fin (n + 2) → ℝ × ℝ | olsNoiseNorm G ≤ 3 * Real.sqrt (n + 2 : ℝ)} ∩
        ({G | (n + 2 : ℝ) / 2 ≤ olsCenteredDesign G} ∩
          {G | ∀ i : Fin (n + 2), (G i).1 ^ 2 ≤ (n + 2 : ℝ) / 64}) by
    ext G
    simp [olsGoodSet]]
  exact hnorm.inter (hdesign.inter hcoords)

theorem measurableSet_olsGoodSet (n : ℕ) : MeasurableSet (olsGoodSet n) :=
  (olsGoodSet_isClosed n).measurableSet

private lemma sum_deleteAt {n : ℕ} (G : Fin (n + 2) → ℝ × ℝ)
    (i : Fin (n + 2)) (f : ℝ × ℝ → ℝ) :
    (∑ j : Fin (n + 1), f (deleteAt G i j)) =
      (∑ j : Fin (n + 2), f (G j)) - f (G i) := by
  have h := Fin.sum_univ_succAbove (fun j : Fin (n + 2) => f (G j)) i
  change (∑ j : Fin (n + 1), f (G (i.succAbove j))) = _
  linarith

private lemma olsCenteredDesign_eq_sumSq_sub_meanSq {N : ℕ}
    (hN : 0 < N) (G : Fin N → ℝ × ℝ) :
    olsCenteredDesign G =
      (∑ i : Fin N, (G i).1 ^ 2) -
        (∑ i : Fin N, (G i).1) ^ 2 / (N : ℝ) := by
  let c : ℝ := (∑ j : Fin N, (G j).1) / (N : ℝ)
  have hcross : (∑ i : Fin N, 2 * (G i).1 * c) =
      2 * c * (∑ i : Fin N, (G i).1) := by
    calc
      _ = ∑ i : Fin N, c * (2 * (G i).1) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin N, 2 * (G i).1 := by rw [Finset.mul_sum]
      _ = 2 * c * ∑ i : Fin N, (G i).1 := by rw [← Finset.mul_sum]; ring
  have hconst : (∑ _i : Fin N, c ^ 2) = (N : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  unfold olsCenteredDesign olsXBar
  calc
    _ = ∑ i : Fin N,
        ((G i).1 ^ 2 - 2 * (G i).1 *
          ((∑ j : Fin N, (G j).1) / (N : ℝ)) +
          ((∑ j : Fin N, (G j).1) / (N : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin N, (G i).1 ^ 2) -
        2 * ((∑ j : Fin N, (G j).1) / (N : ℝ)) *
          (∑ i : Fin N, (G i).1) +
        (N : ℝ) * ((∑ j : Fin N, (G j).1) / (N : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
    _ = (∑ i : Fin N, (G i).1 ^ 2) -
        (∑ i : Fin N, (G i).1) ^ 2 / (N : ℝ) := by
      have hcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp [hcast]; ring

theorem ols_deletedCenteredDesign_identity {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (i : Fin (n + 2)) :
    olsCenteredDesign (deleteAt G i) =
      olsCenteredDesign G - ((n + 2 : ℝ) / (n + 1 : ℝ)) *
        ((G i).1 - olsXBar G) ^ 2 := by
  have hfull := olsCenteredDesign_eq_sumSq_sub_meanSq (N := n + 2) (by omega) G
  have hdel := olsCenteredDesign_eq_sumSq_sub_meanSq (N := n + 1) (by omega)
    (deleteAt G i)
  have hxsum := sum_deleteAt G i fun z => z.1
  have hxsq := sum_deleteAt G i fun z => z.1 ^ 2
  rw [hdel, hfull, hxsum, hxsq]
  have hN : (n + 2 : ℝ) ≠ 0 := by positivity
  have hNm1 : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [olsXBar]
  field_simp [hN, hNm1]
  push_cast
  ring

private lemma olsXBar_sq_le_normSq_div {N : ℕ}
    (G : Fin N → ℝ × ℝ) :
    (olsXBar G) ^ 2 ≤ olsNoiseNormSq G / (N : ℝ) := by
  have hmean := sum_div_card_sq_le_sum_sq_div_card
    (s := Finset.univ) (f := fun i : Fin N => (G i).1)
  have hcoord : (∑ i : Fin N, (G i).1 ^ 2) ≤ olsNoiseNormSq G := by
    unfold olsNoiseNormSq
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (G i).2]
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have hmean' : (olsXBar G) ^ 2 ≤
      (∑ i : Fin N, (G i).1 ^ 2) / (N : ℝ) := by
    simpa [olsXBar, hcard] using hmean
  exact le_trans hmean' (div_le_div_of_nonneg_right hcoord (by positivity))

theorem ols_deletedCenteredDesign_lower_bound {n : ℕ}
    (hn : 192 ≤ n + 2) (G : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (i : Fin (n + 2)) :
    olsCenteredDesign (deleteAt G i) ≥ (n + 2 : ℝ) / 4 := by
  have hnorm := hG.1
  have hdesign := hG.2.1
  have hmax := hG.2.2 i
  have hmean := olsXBar_sq_le_normSq_div G
  have hnormSq : olsNoiseNormSq G ≤ 9 * (n + 2 : ℝ) := by
    have hnonneg : 0 ≤ olsNoiseNormSq G := by
      unfold olsNoiseNormSq
      exact Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hRhs : 0 ≤ 3 * Real.sqrt (n + 2 : ℝ) := by positivity
    change Real.sqrt (olsNoiseNormSq G) ≤ 3 * Real.sqrt (n + 2 : ℝ) at hnorm
    have hsquared := (sq_le_sq₀ (Real.sqrt_nonneg _) hRhs).2 hnorm
    rw [Real.sq_sqrt hnonneg] at hsquared
    rw [show (3 * Real.sqrt (n + 2 : ℝ)) ^ 2 =
        9 * (n + 2 : ℝ) by rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num]
      at hsquared
    exact hsquared
  have hmean9 : (olsXBar G) ^ 2 ≤ 9 := by
    have h := le_trans hmean (div_le_div_of_nonneg_right hnormSq (by positivity))
    have hquot : 9 * (n + 2 : ℝ) / (n + 2 : ℝ) = 9 := by
      field_simp
    push_cast at h
    rw [hquot] at h
    exact h
  rw [ols_deletedCenteredDesign_identity]
  have hdiff : ((G i).1 - olsXBar G) ^ 2 ≤
      2 * (G i).1 ^ 2 + 2 * (olsXBar G) ^ 2 := by
    nlinarith only [sq_nonneg ((G i).1 + olsXBar G)]
  have hfactor : (n + 2 : ℝ) / (n + 1 : ℝ) ≤ 2 := by
    have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hlin : (n + 2 : ℝ) ≤ 2 * (n + 1 : ℝ) := by
      have : (1 : ℝ) ≤ (n + 2 : ℝ) := by linarith
      linarith
    exact (div_le_iff₀ hden).2 hlin
  have hdrop : ((n + 2 : ℝ) / (n + 1 : ℝ)) *
      ((G i).1 - olsXBar G) ^ 2 ≤ 4 * (G i).1 ^ 2 + 4 * (olsXBar G) ^ 2 := by
    calc
      _ ≤ 2 * ((G i).1 - olsXBar G) ^ 2 :=
        mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
      _ ≤ 2 * (2 * (G i).1 ^ 2 + 2 * (olsXBar G) ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff (by norm_num)
      _ = _ := by ring
  have hthreshold : (n + 2 : ℝ) / 2 -
      4 * ((n + 2 : ℝ) / 64) - 4 * 9 ≥ (n + 2 : ℝ) / 4 := by
    have hnreal : (192 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast hn
    linarith
  calc
    olsCenteredDesign G - ((n + 2 : ℝ) / (n + 1 : ℝ)) *
        ((G i).1 - olsXBar G) ^ 2 ≥
      (n + 2 : ℝ) / 2 - (4 * (G i).1 ^ 2 + 4 * (olsXBar G) ^ 2) := by
        linarith only [hdesign, hdrop]
    _ ≥ (n + 2 : ℝ) / 2 -
        4 * ((n + 2 : ℝ) / 64) - 4 * 9 := by
        linarith only [hmax, hmean9]
    _ ≥ (n + 2 : ℝ) / 4 := hthreshold

theorem ols_deletedNoiseNorm_le {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (i : Fin (n + 2)) :
    olsNoiseNorm (deleteAt G i) ≤ olsNoiseNorm G := by
  have hsum := sum_deleteAt G i fun z => z.1 ^ 2 + z.2 ^ 2
  have hnonneg : 0 ≤ (G i).1 ^ 2 + (G i).2 ^ 2 := by positivity
  have hsq : olsNoiseNormSq (deleteAt G i) ≤ olsNoiseNormSq G := by
    have hidentity : olsNoiseNormSq (deleteAt G i) =
        olsNoiseNormSq G - ((G i).1 ^ 2 + (G i).2 ^ 2) := by
      unfold olsNoiseNormSq
      exact hsum
    rw [hidentity]
    linarith
  unfold olsNoiseNorm
  exact Real.sqrt_le_sqrt hsq

end LOOConcentration
