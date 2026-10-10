import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_quadraticRisk_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (hInd : iIndepFun X P) (z : ℝ) :
    (∫ ω, (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2 ∂P) =
      (z - ∫ x : ℝ, x ∂μ) ^ 2 + variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)
:= by
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

end LOOConcentration.Manuscript
