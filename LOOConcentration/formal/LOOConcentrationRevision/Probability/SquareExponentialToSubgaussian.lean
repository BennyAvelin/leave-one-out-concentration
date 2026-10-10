import Mathlib.Probability.Moments.SubGaussian

set_option autoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory

private lemma exp_le_one_add_self_add_sq_exp_abs (u : ℝ) :
    Real.exp u ≤ 1 + u + u ^ 2 * Real.exp |u| := by
  by_cases hsmall : |u| ≤ 1
  · have hTaylor := Real.abs_exp_sub_one_sub_id_le hsmall
    have hdiff : Real.exp u - 1 - u ≤ |Real.exp u - 1 - u| := le_abs_self _
    have hexp : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
    have hsq : u ^ 2 ≤ u ^ 2 * Real.exp |u| := by nlinarith [sq_nonneg u]
    calc
      Real.exp u = 1 + u + (Real.exp u - 1 - u) := by ring
      _ ≤ 1 + u + u ^ 2 := by linarith
      _ ≤ 1 + u + u ^ 2 * Real.exp |u| := by linarith
  · by_cases hu : 1 < u
    · have hsq : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
      have hexp : Real.exp u ≤ u ^ 2 * Real.exp |u| := by
        rw [abs_of_pos (by linarith : 0 < u)]
        calc
          Real.exp u = 1 * Real.exp u := by ring
          _ ≤ u ^ 2 * Real.exp u := mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg u)
      have hlin : 0 ≤ 1 + u := by linarith
      linarith
    · have hu' : u < -1 := by
        have hu1 : u ≤ 1 := le_of_not_gt hu
        have hnot : ¬ -1 ≤ u := by
          intro hle
          exact hsmall (abs_le.mpr ⟨by linarith, hu1⟩)
        exact lt_of_not_ge hnot
      have hexp : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have habs : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
      have hsq : u ^ 2 ≤ u ^ 2 * Real.exp |u| := by nlinarith [sq_nonneg u]
      have hpoly : 0 ≤ u + u ^ 2 := by nlinarith [sq_nonneg (u + 1)]
      linarith

private lemma abs_mul_le_young (x y a : ℝ) (ha : 0 < a) :
    |x * y| ≤ y ^ 2 / (2 * a) + a * x ^ 2 / 2 := by
  rw [abs_mul]
  have hsq : 0 ≤ (a * |x| - |y|) ^ 2 := sq_nonneg _
  have hpoly : 2 * a * (|x| * |y|) ≤ a ^ 2 * |x| ^ 2 + |y| ^ 2 := by nlinarith [hsq]
  have hden : 0 < 2 * a := by positivity
  have htarget : 2 * a * (y ^ 2 / (2 * a) + a * x ^ 2 / 2) = a ^ 2 * |x| ^ 2 + |y| ^ 2 := by
    rw [sq_abs]
    field_simp [ha.ne']
    nlinarith [sq_abs y]
  have hscaled : 2 * a * (|x| * |y|) ≤ 2 * a * (y ^ 2 / (2 * a) + a * x ^ 2 / 2) := by
    rw [htarget]
    simpa [sq_abs] using hpoly
  exact (le_of_mul_le_mul_left hscaled hden)

private lemma sq_mul_exp_half_le (y a : ℝ) (ha : 0 < a) :
    y ^ 2 * Real.exp (y ^ 2 / (2 * a)) ≤ 2 * a * Real.exp (y ^ 2 / a) := by
  let z : ℝ := y ^ 2 / (2 * a)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hze : z * Real.exp z ≤ Real.exp (2 * z) := by
    have hzle : z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
    calc
      z * Real.exp z ≤ Real.exp z * Real.exp z :=
        mul_le_mul_of_nonneg_right hzle (Real.exp_nonneg z)
      _ = Real.exp (2 * z) := by rw [← Real.exp_add]; congr 1; ring
  calc
    y ^ 2 * Real.exp (y ^ 2 / (2 * a)) = 2 * a * (z * Real.exp z) := by
      dsimp [z]
      field_simp [ha.ne']
    _ ≤ 2 * a * Real.exp (2 * z) := mul_le_mul_of_nonneg_left hze (by positivity)
    _ = 2 * a * Real.exp (y ^ 2 / a) := by
      dsimp [z]
      congr 2
      field_simp [ha.ne']

/-- A zero-mean random variable with an actual exponential-square moment has a
sub-Gaussian MGF, with the explicit conversion constant used by the revision. -/
theorem square_exponential_hasSubgaussianMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ) (a : ℝ) (ha : 0 < a)
    (hY : Integrable Y μ) (hmean : (∫ x, Y x ∂μ) = 0)
    (hSq : Integrable (fun x => Real.exp (Y x ^ 2 / a)) μ)
    (hSqI : (∫ x, Real.exp (Y x ^ 2 / a) ∂μ) ≤ 2) :
    ProbabilityTheory.HasSubgaussianMGF Y (NNReal.mk (16 * a) (by positivity)) μ := by
  have hYasm := hY.aestronglyMeasurable
  have hYsqasm : AEStronglyMeasurable (fun x => Y x ^ 2) μ := hYasm.pow 2
  have hExpInt (t : ℝ) : Integrable (fun x => Real.exp (t * Y x)) μ := by
    have hExpAsm := Real.continuous_exp.comp_aestronglyMeasurable (hYasm.const_mul t)
    have hdom := hSq.const_mul (Real.exp (a * t ^ 2 / 2))
    apply hdom.mono' hExpAsm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (t * Y x) ≤ Real.exp |t * Y x| := Real.exp_le_exp.mpr (le_abs_self _)
      _ ≤ Real.exp (Y x ^ 2 / (2 * a) + a * t ^ 2 / 2) :=
        Real.exp_le_exp.mpr (abs_mul_le_young t (Y x) a ha)
      _ ≤ Real.exp (Y x ^ 2 / a + a * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        gcongr
        linarith [ha]
      _ = Real.exp (a * t ^ 2 / 2) * Real.exp (Y x ^ 2 / a) := by rw [Real.exp_add]; ring_nf
  constructor
  · exact hExpInt
  · intro t
    let v : ℝ := a * t ^ 2
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have hCorrAsm : AEStronglyMeasurable (fun x => Y x ^ 2 * Real.exp |t * Y x|) μ :=
      hYsqasm.mul (Real.continuous_exp.comp_aestronglyMeasurable
        (continuous_abs.comp_aestronglyMeasurable (hYasm.const_mul t)))
    have hCorrDom := hSq.const_mul (2 * a * Real.exp (v / 2))
    have hCorr : Integrable (fun x => Y x ^ 2 * Real.exp |t * Y x|) μ := by
      apply hCorrDom.mono' hCorrAsm
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
      have hy := abs_mul_le_young t (Y x) a ha
      have hExp : Real.exp |t * Y x| ≤ Real.exp (Y x ^ 2 / (2 * a) + v / 2) := by
        apply Real.exp_le_exp.mpr
        simpa [v, mul_comm, mul_left_comm, mul_assoc] using hy
      calc
        Y x ^ 2 * Real.exp |t * Y x| ≤
            Y x ^ 2 * Real.exp (Y x ^ 2 / (2 * a) + v / 2) :=
          mul_le_mul_of_nonneg_left hExp (sq_nonneg _)
        _ = Real.exp (v / 2) * (Y x ^ 2 * Real.exp (Y x ^ 2 / (2 * a))) := by
          rw [Real.exp_add]
          ring
        _ ≤ Real.exp (v / 2) * (2 * a * Real.exp (Y x ^ 2 / a)) :=
          mul_le_mul_of_nonneg_left (sq_mul_exp_half_le (Y x) a ha) (Real.exp_nonneg _)
        _ = 2 * a * Real.exp (v / 2) * Real.exp (Y x ^ 2 / a) := by ring
    have hCorrI : ∫ x, Y x ^ 2 * Real.exp |t * Y x| ∂μ ≤ 4 * a * Real.exp (v / 2) := by
      have hmono := integral_mono hCorr hCorrDom (fun x => by
        have hy := abs_mul_le_young t (Y x) a ha
        have hExp : Real.exp |t * Y x| ≤ Real.exp (Y x ^ 2 / (2 * a) + v / 2) := by
          apply Real.exp_le_exp.mpr
          simpa [v, mul_comm, mul_left_comm, mul_assoc] using hy
        calc
          Y x ^ 2 * Real.exp |t * Y x| ≤
              Y x ^ 2 * Real.exp (Y x ^ 2 / (2 * a) + v / 2) :=
            mul_le_mul_of_nonneg_left hExp (sq_nonneg _)
          _ = Real.exp (v / 2) * (Y x ^ 2 * Real.exp (Y x ^ 2 / (2 * a))) := by
            rw [Real.exp_add]
            ring
          _ ≤ Real.exp (v / 2) * (2 * a * Real.exp (Y x ^ 2 / a)) :=
            mul_le_mul_of_nonneg_left (sq_mul_exp_half_le (Y x) a ha) (Real.exp_nonneg _)
          _ = 2 * a * Real.exp (v / 2) * Real.exp (Y x ^ 2 / a) := by ring)
      calc
        ∫ x, Y x ^ 2 * Real.exp |t * Y x| ∂μ ≤ _ := hmono
        _ = 2 * a * Real.exp (v / 2) * (∫ x, Real.exp (Y x ^ 2 / a) ∂μ) := by rw [integral_const_mul]
        _ ≤ 4 * a * Real.exp (v / 2) := by
          have hc : 0 ≤ 2 * a * Real.exp (v / 2) := by positivity
          calc
            2 * a * Real.exp (v / 2) * (∫ x, Real.exp (Y x ^ 2 / a) ∂μ)
                ≤ 2 * a * Real.exp (v / 2) * 2 := mul_le_mul_of_nonneg_left hSqI hc
            _ = 4 * a * Real.exp (v / 2) := by ring
    let f : α → ℝ := fun x => 1 + t * Y x
    let g : α → ℝ := fun x => t ^ 2 * (Y x ^ 2 * Real.exp |t * Y x|)
    have hf : Integrable f μ := by
      dsimp [f]
      exact (integrable_const (1 : ℝ)).add (hY.const_mul t)
    have hg : Integrable g μ := by
      dsimp [g]
      exact hCorr.const_mul (t ^ 2)
    have hTaylorInt : Integrable (fun x => f x + g x) μ := hf.add hg
    have hbase : (∫ x, (1 + t * Y x) ∂μ) = 1 := by
      rw [integral_add (integrable_const 1) (hY.const_mul t)]
      simp only [integral_const, smul_eq_mul, probReal_univ, one_mul,
        integral_const_mul, hmean, mul_zero, add_zero]
    have hTaylor : (∫ x, Real.exp (t * Y x) ∂μ) ≤ 1 + 4 * v * Real.exp (v / 2) := by
      have hmono : (∫ x, Real.exp (t * Y x) ∂μ) ≤
          ∫ x, f x + g x ∂μ := by
        apply integral_mono (hExpInt t) hTaylorInt
        intro x
        dsimp [f, g]
        calc
          Real.exp (t * Y x) ≤ 1 + t * Y x + (t * Y x) ^ 2 * Real.exp |t * Y x| :=
            exp_le_one_add_self_add_sq_exp_abs (t * Y x)
          _ = (1 + t * Y x) + t ^ 2 * (Y x ^ 2 * Real.exp |t * Y x|) := by ring
      have hbaseF : (∫ x, f x ∂μ) = 1 := by simpa [f] using hbase
      have hsplit : (∫ x, f x + g x ∂μ) = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) :=
        integral_add hf hg
      calc
        ∫ x, Real.exp (t * Y x) ∂μ ≤ (∫ x, f x ∂μ) + (∫ x, g x ∂μ) :=
          hmono.trans_eq hsplit
        _ = 1 + t ^ 2 * (∫ x, Y x ^ 2 * Real.exp |t * Y x| ∂μ) := by
          rw [hbaseF]
          dsimp [g]
          rw [integral_const_mul]
        _ ≤ 1 + 4 * v * Real.exp (v / 2) := by
          calc
            1 + t ^ 2 * (∫ x, Y x ^ 2 * Real.exp |t * Y x| ∂μ)
                ≤ 1 + t ^ 2 * (4 * a * Real.exp (v / 2)) := by gcongr
            _ = 1 + 4 * v * Real.exp (v / 2) := by dsimp [v]; ring
    have hmgf : ProbabilityTheory.mgf Y μ t ≤ Real.exp (8 * v) := by
      by_cases hv1 : v ≤ 1
      · have hehalf : Real.exp (v / 2) ≤ 2 := by
          calc
            Real.exp (v / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
            _ ≤ 2 := by
              calc
                Real.exp (1 / 2) ≤ (2 + (1 / 2)) / (2 - (1 / 2)) :=
                  Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
                _ ≤ 2 := by norm_num
        calc
          ProbabilityTheory.mgf Y μ t = ∫ x, Real.exp (t * Y x) ∂μ := by rfl
          _ ≤ 1 + 4 * v * Real.exp (v / 2) := hTaylor
          _ ≤ 1 + 8 * v := by
            calc
              1 + 4 * v * Real.exp (v / 2) ≤ 1 + 4 * v * 2 := by
                gcongr
              _ = 1 + 8 * v := by ring
          _ ≤ Real.exp (8 * v) := by linarith [Real.add_one_le_exp (8 * v)]
      · have hv1' : 1 ≤ v := le_of_not_ge hv1
        have hlarge : 2 * Real.exp (v / 2) ≤ Real.exp (8 * v) := by
          have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc
            2 * Real.exp (v / 2) ≤ Real.exp 1 * Real.exp (v / 2) :=
              mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
            _ = Real.exp (1 + v / 2) := by rw [← Real.exp_add]
            _ ≤ Real.exp (8 * v) := Real.exp_le_exp.mpr (by nlinarith [hv1'])
        have hdirect : ∫ x, Real.exp (t * Y x) ∂μ ≤ 2 * Real.exp (v / 2) := by
          have hmono := integral_mono (hExpInt t) (hSq.const_mul (Real.exp (v / 2)))
            (fun x => by
              calc
                Real.exp (t * Y x) ≤ Real.exp |t * Y x| := Real.exp_le_exp.mpr (le_abs_self _)
                _ ≤ Real.exp (Y x ^ 2 / (2*a) + v/2) := Real.exp_le_exp.mpr (abs_mul_le_young t (Y x) a ha)
                _ ≤ Real.exp (Y x ^ 2/a + v/2) := by
                  apply Real.exp_le_exp.mpr
                  gcongr
                  linarith [ha]
                _ = Real.exp (v/2) * Real.exp (Y x^2/a) := by rw [Real.exp_add]; ring_nf)
          calc
            ∫ x, Real.exp (t * Y x) ∂μ ≤ _ := hmono
            _ = Real.exp (v/2) * (∫ x, Real.exp (Y x ^ 2/a) ∂μ) := by rw [integral_const_mul]
            _ ≤ 2 * Real.exp (v/2) := by
              have hc : 0 ≤ Real.exp (v/2) := Real.exp_nonneg _
              nlinarith [mul_le_mul_of_nonneg_left hSqI hc]
        calc
          ProbabilityTheory.mgf Y μ t = ∫ x, Real.exp (t * Y x) ∂μ := by rfl
          _ ≤ 2 * Real.exp (v / 2) := hdirect
          _ ≤ Real.exp (8 * v) := hlarge
    change ProbabilityTheory.mgf Y μ t ≤ Real.exp ((16 * a) * t ^ 2 / 2)
    have heq : 8 * v = (16 * a) * t ^ 2 / 2 := by dsimp [v]; ring
    rw [← heq]
    exact hmgf

example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) :
    ProbabilityTheory.HasSubgaussianMGF (fun _ : α => (0 : ℝ))
      (NNReal.mk (16 * a) (by positivity)) μ := by
  apply square_exponential_hasSubgaussianMGF μ (fun _ : α => (0 : ℝ)) a ha
  · exact integrable_const 0
  · simp
  · simp
  · simp

end LOOConcentration.Revision
