import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_expectedQuadraticLoss_derivative
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) :
    LocallyLipschitz (fun z : ℝ =>
      ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2 ∂P) ∧
    ∀ z : ℝ,
      HasDerivAt (fun t : ℝ =>
        ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - t) ^ 2 ∂P)
        (2 * (z - ∫ x : ℝ, x ∂μ)) z ∧
      |deriv (fun t : ℝ =>
        ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - t) ^ 2 ∂P) z| ≤
        2 * |∫ x : ℝ, x ∂μ| + 2 * |z|
:= by
  let m : ℝ := ∫ x : ℝ, x ∂μ
  let c : ℝ := variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)
  let f : ℝ → ℝ := fun z =>
    ∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2 ∂P
  let q : ℝ → ℝ := fun z => (z - m) ^ 2 + c
  change LocallyLipschitz f ∧ ∀ z : ℝ,
    HasDerivAt f (2 * (z - m)) z ∧ |deriv f z| ≤ 2 * |m| + 2 * |z|
  have hFormula (z : ℝ) : f z = q z := by
    change
      (∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2 ∂P) =
        (z - ∫ x : ℝ, x ∂μ) ^ 2 + variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)
    let n : ℝ := (r + 1 : ℕ)
    let S : Ω → ℝ := fun ω => ∑ i : Fin (r + 1), X i ω
    let Y : Ω → ℝ := fun ω => n⁻¹ * S ω
    have hn : n ≠ 0 := by
      dsimp [n]
      positivity
    have hIdLp : MemLp (id : ℝ → ℝ) 2 μ := by
      apply (memLp_two_iff_integrable_sq (measurable_id.aestronglyMeasurable)).2
      exact hSecond
    have hXLp : ∀ i, MemLp (X i) 2 P := fun i => (hLaw i).memLp_iff.mpr hIdLp
    have hXInt : ∀ i, Integrable (X i) P := fun i => (hXLp i).integrable one_le_two
    have hSLp : MemLp S 2 P := by
      simpa [S] using
        (memLp_finsetSum (s := Finset.univ) (f := X) (fun i _ => hXLp i))
    have hYlp : MemLp Y 2 P := by
      simpa [Y] using hSLp.const_mul n⁻¹
    have hYInt : Integrable Y P := hYlp.integrable one_le_two
    have hY2Int : Integrable (fun ω => Y ω ^ 2) P := hYlp.integrable_sq
    have hEmp (ω : Ω) :
        empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) = Y ω := by
      simp [empiricalMean, Y, S, n]
    have hSumIntegral :
        (∫ ω, S ω ∂P) = ∑ i : Fin (r + 1), ∫ ω, X i ω ∂P := by
      simpa [S] using
        (integral_finsetSum (s := Finset.univ) (f := X) (fun i _ => hXInt i))
    have hMean : (∫ ω, Y ω ∂P) = ∫ x : ℝ, x ∂μ := by
      calc
        (∫ ω, Y ω ∂P) = n⁻¹ * (∫ ω, S ω ∂P) := by
          simp [Y, integral_const_mul]
        _ = n⁻¹ * ∑ i : Fin (r + 1), ∫ ω, X i ω ∂P := by rw [hSumIntegral]
        _ = n⁻¹ * ∑ i : Fin (r + 1), ∫ x : ℝ, x ∂μ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact (hLaw i).integral_eq
        _ = ∫ x : ℝ, x ∂μ := by
          field_simp [n, hn]
          simp [n]
    have hPair :
        Set.Pairwise (↑(Finset.univ : Finset (Fin (r + 1))))
          (fun i j => X i ⟂ᵢ[P] X j) := by
      intro i hi j hj hij
      exact hInd.indepFun hij
    have hVarSum :
        variance S P = ∑ i : Fin (r + 1), variance (X i) P := by
      calc
        variance S P = variance (∑ i : Fin (r + 1), X i) P := by
          congr 1
          funext ω
          simp [S]
        _ = ∑ i : Fin (r + 1), variance (X i) P :=
          IndepFun.variance_sum (μ := P) (s := Finset.univ) (X := X)
            (fun i _ => hXLp i) hPair
    have hVarEach (i : Fin (r + 1)) : variance (X i) P = variance (id : ℝ → ℝ) μ :=
      (hLaw i).variance_eq
    have hVarS : variance S P = n * variance (id : ℝ → ℝ) μ := by
      rw [hVarSum]
      simp [n, hVarEach]
    have hVarY : variance Y P = variance (id : ℝ → ℝ) μ / n := by
      calc
        variance Y P = n⁻¹ ^ 2 * variance S P := by
          simpa [Y] using (variance_const_mul n⁻¹ S P)
        _ = n⁻¹ ^ 2 * (n * variance (id : ℝ → ℝ) μ) := by rw [hVarS]
        _ = variance (id : ℝ → ℝ) μ / n := by
          field_simp [hn]
    have hSquareExpansion :
        (∫ ω, (Y ω - z) ^ 2 ∂P) =
          (∫ ω, Y ω ^ 2 ∂P) - 2 * z * (∫ ω, Y ω ∂P) + z ^ 2 := by
      calc
        (∫ ω, (Y ω - z) ^ 2 ∂P) =
            ∫ ω, (Y ω ^ 2 - (2 * z) * Y ω + z ^ 2) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = (∫ ω, Y ω ^ 2 ∂P) - 2 * z * (∫ ω, Y ω ∂P) + z ^ 2 := by
          have hIntegrableSub : Integrable (fun ω => Y ω ^ 2 - (2 * z) * Y ω) P :=
            hY2Int.sub (hYInt.const_mul (2 * z))
          change
            (∫ ω, (Y ω ^ 2 - (2 * z) * Y ω) + z ^ 2 ∂P) = _
          rw [integral_add hIntegrableSub (integrable_const (z ^ 2))]
          rw [integral_sub hY2Int (hYInt.const_mul (2 * z))]
          rw [integral_const_mul, integral_const]
          simp
    have hSquareMean :
        (∫ ω, (Y ω - z) ^ 2 ∂P) =
          (z - (∫ ω, Y ω ∂P)) ^ 2 + variance Y P := by
      rw [hSquareExpansion, variance_eq_sub hYlp]
      simp only [Pi.pow_apply]
      ring
    rw [show (∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2 ∂P) =
        (∫ ω, (Y ω - z) ^ 2 ∂P) by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hEmp]]
    rw [hSquareMean, hMean, hVarY]
    simp [n]
  have hFun : f = q := by
    funext z
    exact hFormula z
  have hqLocally : LocallyLipschitz q := by
    intro a
    let K : NNReal := ⟨2 * |a| + 2 + 2 * |m|, by positivity⟩
    have hK : (K : ℝ) = 2 * |a| + 2 + 2 * |m| := rfl
    refine ⟨K, Metric.ball a 1, Metric.ball_mem_nhds a (by norm_num), ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxball : dist x a < 1 := by simpa only [Metric.mem_ball] using hx
    have hyball : dist y a < 1 := by simpa only [Metric.mem_ball] using hy
    have hxnear : |x - a| < 1 := by simpa only [Real.dist_eq] using hxball
    have hynear : |y - a| < 1 := by simpa only [Real.dist_eq] using hyball
    have hxabs : |x| ≤ |a| + 1 := by
      calc
        |x| = |x - 0| := by simp
        _ ≤ |x - a| + |a - 0| := abs_sub_le x a 0
        _ = |x - a| + |a| := by rw [sub_zero]
        _ ≤ |a| + 1 := by linarith
    have hyabs : |y| ≤ |a| + 1 := by
      calc
        |y| = |y - 0| := by simp
        _ ≤ |y - a| + |a - 0| := abs_sub_le y a 0
        _ = |y - a| + |a| := by rw [sub_zero]
        _ ≤ |a| + 1 := by linarith
    have hneg : |-2 * m| = 2 * |m| := by simp
    have hcross : |x + y - 2 * m| ≤ 2 * |a| + 2 + 2 * |m| := by
      calc
        |x + y - 2 * m| = |(x + y) + (-2 * m)| := by congr 1; ring
        _ ≤ |x + y| + |-2 * m| := abs_add_le _ _
        _ ≤ |x| + |y| + 2 * |m| := by rw [hneg]; linarith [abs_add_le x y]
        _ ≤ 2 * |a| + 2 + 2 * |m| := by linarith
    rw [Real.dist_eq, Real.dist_eq]
    have hfactor : q x - q y = (x - y) * (x + y - 2 * m) := by
      dsimp [q]
      ring
    rw [hfactor, abs_mul]
    calc
      |x - y| * |x + y - 2 * m| ≤ |x - y| * (K : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa only [hK] using hcross
      _ = (K : ℝ) * |x - y| := by ring
  have hqDeriv (z : ℝ) : HasDerivAt q (2 * (z - m)) z := by
    simpa [q] using (((hasDerivAt_id z).sub_const m).pow 2).add_const c
  constructor
  · rw [hFun]
    exact hqLocally
  · intro z
    constructor
    · rw [hFun]
      exact hqDeriv z
    · rw [hFun]
      calc
        |deriv q z| = |2 * (z - m)| := by rw [(hqDeriv z).deriv]
        _ ≤ 2 * (|z| + |m|) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have habs : |z - m| ≤ |z| + |m| := by
            simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le z 0 m
          exact mul_le_mul_of_nonneg_left habs (by norm_num)
        _ = 2 * |m| + 2 * |z| := by ring

end LOOConcentration.Manuscript
