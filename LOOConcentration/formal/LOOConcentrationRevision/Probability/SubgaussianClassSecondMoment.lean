import LOOConcentration.Analysis.ClipLimit
import LOOConcentrationRevision.Probability.LipschitzIntegrability
import LOOConcentrationRevision.Probability.SubgaussianSquareExponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology

/-- A genuine whole-space sub-Gaussian Lipschitz class supplies a raw second
moment for the Euclidean norm. The candidate constant is used only through
the centered sub-Gaussian bounds of the clipped norms. -/
theorem integrable_norm_sq_of_lipschitz_subgaussian_class
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (c : ℝ≥0)
    (hClass : ∀ F : EuclideanSpace ℝ ι → ℝ,
      Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF
          (fun x => F x - ∫ y, F y ∂μ) c μ) :
    Integrable (fun x => ‖x‖ ^ 2) μ := by
  let f : ℕ → EuclideanSpace ℝ ι → ℝ :=
    fun j => LOOConcentration.clipValueSequence (fun x => ‖x‖) j
  obtain ⟨n, hn⟩ := MeasureTheory.exists_pos_ball
    (μ := μ) (0 : EuclideanSpace ℝ ι) (IsProbabilityMeasure.ne_zero μ)
  let s : Set (EuclideanSpace ℝ ι) := Metric.ball 0 n
  let q : ℝ := μ.real s
  have hq : 0 < q := by
    dsimp [q, s] at hn ⊢
    exact ENNReal.toReal_pos hn.ne' (measure_ne_top μ _)
  have hcap (j : ℕ) : 0 ≤ (j : ℝ) + 1 := by positivity
  have hFnonneg (j : ℕ) (x : EuclideanSpace ℝ ι) : 0 ≤ f j x := by
    change 0 ≤ LOOConcentration.clipValue ((j : ℝ) + 1) ‖x‖
    unfold LOOConcentration.clipValue
    exact le_max_of_le_right (le_min (norm_nonneg _) (hcap j))
  have hFabs (j : ℕ) (x : EuclideanSpace ℝ ι) :
      |f j x| ≤ (j : ℝ) + 1 := by
    rw [abs_of_nonneg (hFnonneg j x)]
    change LOOConcentration.clipValue ((j : ℝ) + 1) ‖x‖ ≤ (j : ℝ) + 1
    exact (LOOConcentration.clipValue_bounds (hcap j)).2
  have hclipLip (j : ℕ) : LipschitzWith 1 (f j) := by
    have hclip : LipschitzWith 1
        (fun u : ℝ => LOOConcentration.clipValue ((j : ℝ) + 1) u) := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      simpa only [one_mul, NNReal.coe_one, Real.dist_eq] using
        LOOConcentration.abs_clipValue_sub_le ((j : ℝ) + 1) u v
    have hnormdist (x : EuclideanSpace ℝ ι) : ‖x‖ = dist x 0 := by
      simp [EuclideanSpace.norm_eq]
    have hnorm : LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => ‖x‖) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, hnormdist x, hnormdist y]
      simpa using abs_dist_sub_le x y (0 : EuclideanSpace ℝ ι)
    change LipschitzWith 1
      (fun x : EuclideanSpace ℝ ι =>
        LOOConcentration.clipValue ((j : ℝ) + 1) ‖x‖)
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc
      dist (LOOConcentration.clipValue ((j : ℝ) + 1) ‖x‖)
          (LOOConcentration.clipValue ((j : ℝ) + 1) ‖y‖) ≤
            dist ‖x‖ ‖y‖ := by
              simpa only [one_mul, NNReal.coe_one] using
                hclip.dist_le_mul ‖x‖ ‖y‖
      _ ≤ (1 : ℝ≥0) * dist x y := hnorm.dist_le_mul x y
  have hclipInt (j : ℕ) : Integrable (f j) μ := by
    have hm : AEStronglyMeasurable (f j) μ := by
      have hc : Continuous (f j) := by
        dsimp [f, LOOConcentration.clipValueSequence]
        exact (LOOConcentration.continuous_clipValue _).comp continuous_norm
      exact hc.aestronglyMeasurable
    refine integrable_of_le_of_le (f := f j)
      (g₁ := fun _ => -((j : ℝ) + 1))
      (g₂ := fun _ => (j : ℝ) + 1) hm ?_ ?_ (integrable_const _) (integrable_const _)
    · exact Filter.Eventually.of_forall fun x => (abs_le.mp (hFabs j x)).1
    · exact Filter.Eventually.of_forall fun x => (abs_le.mp (hFabs j x)).2
  have hclipSqInt (j : ℕ) : Integrable (fun x => (f j x) ^ 2) μ := by
    have hm : AEStronglyMeasurable (fun x => (f j x) ^ 2) μ := by fun_prop
    exact integrable_of_le_of_le (f := fun x => (f j x) ^ 2)
      (g₁ := fun _ => (0 : ℝ))
      (g₂ := fun _ => ((j : ℝ) + 1) ^ 2) hm
      (Filter.Eventually.of_forall fun x => sq_nonneg (f j x))
      (Filter.Eventually.of_forall fun x => by
        have h := hFabs j x
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (f j x)) (by positivity)).2 h)
      (integrable_const 0) (integrable_const (((j : ℝ) + 1) ^ 2))
  have hvariance (j : ℕ) :
      (∫ x, (f j x - ∫ y, f j y ∂μ) ^ 2 ∂μ) ≤ 16 * (c : ℝ) := by
    let m : ℝ := ∫ y, f j y ∂μ
    let Y : EuclideanSpace ℝ ι → ℝ := fun x => f j x - m
    have hYsqInt : Integrable (fun x => Y x ^ 2) μ := by
      have hmY : AEStronglyMeasurable (fun x => Y x ^ 2) μ := by fun_prop
      refine integrable_of_le_of_le (f := fun x => Y x ^ 2)
        (g₁ := fun _ => (0 : ℝ))
        (g₂ := fun _ => (((j : ℝ) + 1) + |m|) ^ 2) hmY ?_ ?_
        (integrable_const 0) (integrable_const ((((j : ℝ) + 1) + |m|) ^ 2))
      · exact Filter.Eventually.of_forall fun x => sq_nonneg (Y x)
      · exact Filter.Eventually.of_forall fun x => by
          have hYbound : |Y x| ≤ ((j : ℝ) + 1) + |m| := by
            dsimp [Y]
            calc
              |f j x - m| ≤ |f j x| + |m| := abs_sub _ _
              _ ≤ ((j : ℝ) + 1) + |m| := by
                simpa only [add_comm] using add_le_add_left (hFabs j x) |m|
          have hB : 0 ≤ ((j : ℝ) + 1) + |m| := by positivity
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Y x)) hB).2 hYbound
    have hSG : ProbabilityTheory.HasSubgaussianMGF Y c μ := by
      dsimp [Y, m]
      exact hClass (f j) (hclipInt j) (hclipLip j)
    by_cases hc : c = 0
    · subst c
      have hzero := hSG.ae_eq_zero_of_hasSubgaussianMGF_zero
      have hYzero : (fun x => Y x ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
        filter_upwards [hzero] with x hx
        simp [hx]
      rw [integral_congr_ae hYzero]
      simp
    · have hcpos : 0 < c := lt_of_le_of_ne (by positivity) (Ne.symm hc)
      obtain ⟨hExpInt, hExpBound⟩ :=
        subgaussian_square_exponential_bound μ Y c hcpos hSG
      have hpoint (x : EuclideanSpace ℝ ι) :
          Y x ^ 2 ≤ 8 * (c : ℝ) * Real.exp
            (Y x ^ 2 / (8 * (c : ℝ))) := by
        have hcR : 0 < (c : ℝ) := by exact_mod_cast hcpos
        have hexp := Real.add_one_le_exp (Y x ^ 2 / (8 * (c : ℝ)))
        have hz : Y x ^ 2 / (8 * (c : ℝ)) ≤
            Real.exp (Y x ^ 2 / (8 * (c : ℝ))) := by linarith
        calc
          Y x ^ 2 = (8 * (c : ℝ)) *
              (Y x ^ 2 / (8 * (c : ℝ))) := by field_simp
          _ ≤ (8 * (c : ℝ)) *
              Real.exp (Y x ^ 2 / (8 * (c : ℝ))) :=
                mul_le_mul_of_nonneg_left hz (by positivity)
      calc
        (∫ x, Y x ^ 2 ∂μ) ≤
            ∫ x, 8 * (c : ℝ) *
              Real.exp (Y x ^ 2 / (8 * (c : ℝ))) ∂μ := by
                apply integral_mono_ae hYsqInt
                  (hExpInt.const_mul (8 * (c : ℝ)))
                  (Filter.Eventually.of_forall hpoint)
        _ = 8 * (c : ℝ) *
            ∫ x, Real.exp (Y x ^ 2 / (8 * (c : ℝ))) ∂μ := by
              rw [integral_const_mul]
        _ ≤ 8 * (c : ℝ) * 2 := by
              gcongr
        _ = 16 * (c : ℝ) := by ring
  have hlocalbound (j : ℕ) :
      (q * (∫ x, f j x ∂μ) ^ 2) ≤
        2 * (16 * (c : ℝ)) + 2 * q * (n : ℝ) ^ 2 := by
    let m : ℝ := ∫ x, f j x ∂μ
    let Y : EuclideanSpace ℝ ι → ℝ := fun x => f j x - m
    have hYsqInt : Integrable (fun x => Y x ^ 2) μ := by
      have hmY : AEStronglyMeasurable (fun x => Y x ^ 2) μ := by fun_prop
      exact integrable_of_le_of_le (f := fun x => Y x ^ 2)
        (g₁ := fun _ => (0 : ℝ))
        (g₂ := fun _ => (((j : ℝ) + 1) + |m|) ^ 2) hmY
        (Filter.Eventually.of_forall fun x => sq_nonneg (Y x))
        (Filter.Eventually.of_forall fun x => by
          have hYbound : |Y x| ≤ ((j : ℝ) + 1) + |m| := by
            dsimp [Y]
            calc
              |f j x - m| ≤ |f j x| + |m| := abs_sub _ _
              _ ≤ ((j : ℝ) + 1) + |m| := by
                simpa only [add_comm] using add_le_add_left (hFabs j x) |m|
          have hB : 0 ≤ ((j : ℝ) + 1) + |m| := by positivity
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Y x)) hB).2 hYbound)
        (integrable_const 0) (integrable_const ((((j : ℝ) + 1) + |m|) ^ 2))
    have hpoint :
        (fun _ : EuclideanSpace ℝ ι => m ^ 2) ≤ᵐ[μ.restrict s]
          (fun x => 2 * Y x ^ 2 + 2 * (n : ℝ) ^ 2) := by
      filter_upwards [ae_restrict_mem (by dsimp [s]; exact measurableSet_ball)] with x hx
      have hnorm : ‖x‖ < (n : ℝ) := by simpa [s, Metric.mem_ball, dist_zero_right] using hx
      have hclipbound : |f j x| ≤ ‖x‖ := by
        dsimp [f, LOOConcentration.clipValueSequence]
        simpa only [abs_of_nonneg (norm_nonneg x)] using
          LOOConcentration.abs_clipValue_le_abs
            (A := (j : ℝ) + 1) (u := ‖x‖) (by positivity)
      have hfsq : (f j x) ^ 2 ≤ (n : ℝ) ^ 2 := by
        have hfnonneg := hFnonneg j x
        have hfle : f j x ≤ (n : ℝ) := by
          have hfle' : f j x ≤ ‖x‖ := by
            simpa only [abs_of_nonneg hfnonneg] using hclipbound
          exact hfle'.trans hnorm.le
        exact (sq_le_sq₀ hfnonneg (by positivity)).2 hfle
      have halg : (f j x - Y x) ^ 2 ≤ 2 * (f j x) ^ 2 + 2 * Y x ^ 2 := by
        nlinarith [sq_nonneg (f j x + Y x)]
      have hmEq : f j x - Y x = m := by dsimp [Y]; ring
      nlinarith [halg, hfsq, hmEq]
    have hleftInt : IntegrableOn (fun _ : EuclideanSpace ℝ ι => m ^ 2) s μ := by
      exact integrable_const _
    have hYsqOn : IntegrableOn (fun x => 2 * Y x ^ 2) s μ := by
      change Integrable _ (μ.restrict s)
      exact (hYsqInt.const_mul 2).mono_measure Measure.restrict_le_self
    have hconstOn : IntegrableOn
        (fun _ : EuclideanSpace ℝ ι => 2 * (n : ℝ) ^ 2) s μ := integrable_const _
    have hrightInt : IntegrableOn
        (fun x => 2 * Y x ^ 2 + 2 * (n : ℝ) ^ 2) s μ := hYsqOn.add hconstOn
    have hlocal := setIntegral_mono_ae_restrict hleftInt hrightInt hpoint
    have hsmall : (∫ x in s, Y x ^ 2 ∂μ) ≤ ∫ x, Y x ^ 2 ∂μ :=
      setIntegral_le_integral hYsqInt (Filter.Eventually.of_forall fun x => sq_nonneg _)
    have hmass : ∫ x in s, (m ^ 2) ∂μ = q * m ^ 2 := by
      rw [setIntegral_const]
      simp [q, smul_eq_mul]
    have hright :
        (∫ x in s, (2 * Y x ^ 2 + 2 * (n : ℝ) ^ 2) ∂μ) =
          2 * (∫ x in s, Y x ^ 2 ∂μ) + 2 * q * (n : ℝ) ^ 2 := by
      calc
        (∫ x in s, (2 * Y x ^ 2 + 2 * (n : ℝ) ^ 2) ∂μ) =
            (∫ x in s, 2 * Y x ^ 2 ∂μ) +
              (∫ x in s, (fun _ => 2 * (n : ℝ) ^ 2) x ∂μ) :=
                integral_add hYsqOn hconstOn
        _ = 2 * (∫ x in s, Y x ^ 2 ∂μ) + μ.real s * (2 * (n : ℝ) ^ 2) := by
              rw [integral_const_mul, setIntegral_const]
              simp only [smul_eq_mul]
        _ = 2 * (∫ x in s, Y x ^ 2 ∂μ) + 2 * q * (n : ℝ) ^ 2 := by
              simp only [q]
              ring
    rw [hmass, hright] at hlocal
    have hvar : (∫ x, Y x ^ 2 ∂μ) ≤ 16 * (c : ℝ) := by
      simpa [Y, m] using hvariance j
    nlinarith [hlocal, hsmall, hvar]
  have hmeanSq (j : ℕ) :
      (∫ x, f j x ∂μ) ^ 2 ≤
        2 * (16 * (c : ℝ)) / q + 2 * (n : ℝ) ^ 2 := by
    field_simp [ne_of_gt hq]
    nlinarith [hlocalbound j]
  have hrawbound (j : ℕ) :
      (∫ x, (f j x) ^ 2 ∂μ) ≤ 32 * (c : ℝ) +
        64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2 := by
    let m : ℝ := ∫ x, f j x ∂μ
    let Y : EuclideanSpace ℝ ι → ℝ := fun x => f j x - m
    have hYsqInt : Integrable (fun x => Y x ^ 2) μ := by
      have hmY : AEStronglyMeasurable (fun x => Y x ^ 2) μ := by fun_prop
      exact integrable_of_le_of_le (f := fun x => Y x ^ 2)
        (g₁ := fun _ => (0 : ℝ))
        (g₂ := fun _ => (((j : ℝ) + 1) + |m|) ^ 2) hmY
        (Filter.Eventually.of_forall fun x => sq_nonneg (Y x))
        (Filter.Eventually.of_forall fun x => by
          have hYbound : |Y x| ≤ ((j : ℝ) + 1) + |m| := by
            dsimp [Y]
            calc
              |f j x - m| ≤ |f j x| + |m| := abs_sub _ _
              _ ≤ ((j : ℝ) + 1) + |m| := by
                simpa only [add_comm] using add_le_add_left (hFabs j x) |m|
          have hB : 0 ≤ ((j : ℝ) + 1) + |m| := by positivity
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Y x)) hB).2 hYbound)
        (integrable_const 0) (integrable_const ((((j : ℝ) + 1) + |m|) ^ 2))
    have hpoint : (fun x => (f j x) ^ 2) ≤ᵐ[μ]
        (fun x => 2 * Y x ^ 2 + 2 * m ^ 2) := by
      filter_upwards [] with x
      have hY : f j x = Y x + m := by dsimp [Y]; ring
      nlinarith [sq_nonneg (Y x - m), hY]
    have hrhsInt : Integrable (fun x => 2 * Y x ^ 2 + 2 * m ^ 2) μ :=
      (hYsqInt.const_mul 2).add (integrable_const _)
    have hraw := integral_mono_ae (hclipSqInt j) hrhsInt hpoint
    have hrewrite :
        (∫ x, 2 * Y x ^ 2 + 2 * m ^ 2 ∂μ) =
          2 * (∫ x, Y x ^ 2 ∂μ) + 2 * m ^ 2 := by
      rw [integral_add (hYsqInt.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      simp
    rw [hrewrite] at hraw
    have hvar : (∫ x, Y x ^ 2 ∂μ) ≤ 16 * (c : ℝ) := by
      simpa [Y, m] using hvariance j
    have hmean : m ^ 2 ≤ 2 * (16 * (c : ℝ)) / q + 2 * (n : ℝ) ^ 2 := by
      simpa [m] using hmeanSq j
    have hmeanRaw : 2 * m ^ 2 ≤ 64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2 := by
      calc
        2 * m ^ 2 ≤ 2 * (2 * (16 * (c : ℝ)) / q + 2 * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmean (by norm_num)
        _ = 64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2 := by ring
    calc
      (∫ x, (f j x) ^ 2 ∂μ) ≤
          2 * (∫ x, Y x ^ 2 ∂μ) + 2 * m ^ 2 := hraw
      _ ≤ 2 * (16 * (c : ℝ)) +
            (64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hvar (by norm_num)) hmeanRaw
      _ = 32 * (c : ℝ) + 64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2 := by ring
  let K : ℝ := 32 * (c : ℝ) + 64 * (c : ℝ) / q + 4 * (n : ℝ) ^ 2
  have hFatou :
      (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≤ ENNReal.ofReal K := by
    have hconv (x : EuclideanSpace ℝ ι) :
        Tendsto (fun j : ℕ => ENNReal.ofReal (f j x ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (‖x‖ ^ 2))) := by
      have hclip := LOOConcentration.clipValueSequence_tendsto
        (fun x : EuclideanSpace ℝ ι => ‖x‖) x
      have hcont : Continuous (fun z : ℝ => ENNReal.ofReal (z ^ 2)) :=
        ENNReal.continuous_ofReal.comp (continuous_id.pow 2)
      change Tendsto (fun j => ENNReal.ofReal (f j x ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖x‖ ^ 2)))
      exact hcont.continuousAt.tendsto.comp hclip
    have hpointwise (x : EuclideanSpace ℝ ι) :
        Filter.liminf (fun j : ℕ => ENNReal.ofReal (f j x ^ 2)) atTop =
          ENNReal.ofReal (‖x‖ ^ 2) := (hconv x).liminf_eq
    have hfatou := MeasureTheory.lintegral_liminf_le'
      (μ := μ) (f := fun j x => ENNReal.ofReal (f j x ^ 2))
      (u := atTop) (fun j => by fun_prop)
    have hseq (j : ℕ) :
        (∫⁻ x, ENNReal.ofReal (f j x ^ 2) ∂μ) ≤ ENNReal.ofReal K := by
      have hEq := ofReal_integral_eq_lintegral_ofReal (hclipSqInt j)
        (Filter.Eventually.of_forall fun x => sq_nonneg (f j x))
      calc
        (∫⁻ x, ENNReal.ofReal (f j x ^ 2) ∂μ) =
            ENNReal.ofReal (∫ x, (f j x) ^ 2 ∂μ) := hEq.symm
        _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (by
          simpa [K] using hrawbound j)
    calc
      (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) =
          ∫⁻ x, Filter.liminf
            (fun j : ℕ => ENNReal.ofReal (f j x ^ 2)) atTop ∂μ := by
              apply lintegral_congr_ae
              filter_upwards [] with x
              exact (hpointwise x).symm
      _ ≤ Filter.liminf
          (fun j : ℕ => ∫⁻ x, ENNReal.ofReal (f j x ^ 2) ∂μ) atTop := hfatou
      _ ≤ ENNReal.ofReal K :=
          Filter.liminf_le_of_frequently_le
            ((Filter.Eventually.of_forall hseq).frequently)
  have hfinite : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFatou
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ := by
    fun_prop
  have hnonneg : 0 ≤ᵐ[μ] fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hfinite

#print axioms integrable_norm_sq_of_lipschitz_subgaussian_class

end LOOConcentration.Revision
