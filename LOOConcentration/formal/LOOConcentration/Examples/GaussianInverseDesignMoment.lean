import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.GaussianSquareMGF
import LOOConcentration.Examples.GaussianCenteredDesign
import LOOConcentration.Examples.OlsGaussianTails

set_option autoImplicit false

open MeasureTheory
open Filter
open Real
open scoped ENNReal NNReal
open scoped Topology

namespace LOOConcentration

@[fun_prop]
private lemma measurable_standardGaussianSqSum {d : ℕ} :
    Measurable (standardGaussianSqSum (r := d)) := by
  unfold standardGaussianSqSum
  fun_prop

private lemma standardGaussianSqSum_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ standardGaussianSqSum x := by
  unfold standardGaussianSqSum
  exact Finset.sum_nonneg fun i hi => sq_nonneg (x i)

private instance instStandardGaussianNullSingleton : NullSingletonClass standardGaussian :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)

private theorem integral_one_add_two_mul_rpow {d : ℕ} (hd : 2 < d) :
    (∫ t : ℝ in Set.Ioi 0, (1 + 2 * t) ^ (-(d : ℝ) / 2)) =
      1 / ((d : ℝ) - 2) := by
  let p : ℝ := -(d : ℝ) / 2
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hp : p < -1 := by dsimp [p]; linarith
  have hp1 : p + 1 ≠ 0 := by linarith
  have hbaseInt : IntegrableOn (fun u : ℝ => (u + 1) ^ p) (Set.Ioi 0) := by
    exact integrableOn_add_rpow_Ioi_of_lt hp (by norm_num)
  have hInt : IntegrableOn (fun t : ℝ => (1 + 2 * t) ^ p) (Set.Ioi 0) := by
    have hbaseInt' : IntegrableOn (fun u : ℝ => (u + 1) ^ p)
        (Set.Ioi (2 * 0)) := by simpa using hbaseInt
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (u + 1) ^ p) 0 (a := 2) (by norm_num)).2 hbaseInt'
    have hcomp' : IntegrableOn (fun t : ℝ => (2 * t + 1) ^ p) (Set.Ioi 0) := by
      simpa using hcomp
    exact hcomp'.congr_fun (fun t ht => by
      change (2 * t + 1) ^ p = (1 + 2 * t) ^ p
      rw [show 2 * t + 1 = 1 + 2 * t by ring]) measurableSet_Ioi
  let F : ℝ → ℝ := fun t => (1 + 2 * t) ^ (p + 1) / (2 * (p + 1))
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt F ((1 + 2 * x) ^ p) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.mp hx
    have hbase : 0 < 1 + 2 * x := by linarith [hx0]
    have hlin : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_const_mul (2 : ℝ) (x := x)).const_add (1 : ℝ)
    have hpow : HasDerivAt (fun y : ℝ => y ^ (p + 1))
        ((p + 1) * (1 + 2 * x) ^ p) (1 + 2 * x) := by
      simpa only [add_sub_cancel_right] using
        (hasDerivAt_rpow_const (p := p + 1) (Or.inl (ne_of_gt hbase)))
    have hcomp := hpow.comp x hlin
    have hF := hcomp.div_const (2 * (p + 1))
    have hcoef : ((p + 1) * (1 + 2 * x) ^ p * 2) / (2 * (p + 1)) =
        (1 + 2 * x) ^ p := by
      field_simp [hp1]
    rw [hcoef] at hF
    change HasDerivAt F ((1 + 2 * x) ^ p) x at hF
    exact hF
  have hlinTop : Tendsto (fun t : ℝ => 1 + 2 * t) atTop atTop := by
    have hle : (fun t : ℝ => t) ≤ᶠ[atTop] (fun t => 1 + 2 * t) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      linarith
    exact tendsto_atTop_mono' atTop hle tendsto_id
  have hrpow : Tendsto (fun y : ℝ => y ^ (p + 1)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(p + 1))
  have hlimit : Tendsto F atTop (𝓝 0) := by
    simpa [F] using (hrpow.comp hlinTop).div_const (2 * (p + 1))
  have hcalc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hInt hlimit
  have hvalue : (∫ t : ℝ in Set.Ioi 0, (1 + 2 * t) ^ p) =
      -1 / (2 * (p + 1)) := by
    calc
      _ = 0 - F 0 := hcalc
      _ = -1 / (2 * (p + 1)) := by
        simp [F, Real.one_rpow]
        field_simp [hp1]
  have hdenom : 2 * (p + 1) = 2 - (d : ℝ) := by dsimp [p]; ring
  rw [show (-(d : ℝ) / 2) = p by rfl]
  rw [hvalue, hdenom]
  have hdne : (d : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have htwoDne : 2 - (d : ℝ) ≠ 0 := by linarith
  field_simp [hdne, htwoDne]
  ring

private theorem laplace_lintegral_of_pos {q : ℝ} (hq : 0 < q) :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-t * q))
      ∂(volume.restrict (Set.Ioi 0))) = ENNReal.ofReal (q⁻¹) := by
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-t * q)) (Set.Ioi 0) := by
    have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-q) * t)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := -q) (by linarith) 0
    exact hbase.congr_fun (fun t ht => by
      apply congrArg Real.exp
      ring) measurableSet_Ioi
  have hval : (∫ t : ℝ, Real.exp (-t * q)
      ∂(volume.restrict (Set.Ioi 0))) = q⁻¹ := by
    have h := integral_exp_mul_Ioi (a := -q) (by linarith) 0
    calc
      _ = ∫ t : ℝ in Set.Ioi 0, Real.exp ((-q) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change Real.exp (-t * q) = Real.exp ((-q) * t)
        rw [show -t * q = (-q) * t by ring]
      _ = -Real.exp ((-q) * 0) / (-q) := h
      _ = q⁻¹ := by
        simp only [mul_zero, Real.exp_zero]
        field_simp [hq.ne']
  calc
    _ = ENNReal.ofReal (∫ t : ℝ, Real.exp (-t * q)
          ∂(volume.restrict (Set.Ioi 0))) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hInt
        exact ae_of_all _ fun t => (Real.exp_pos _).le
    _ = ENNReal.ofReal (q⁻¹) := by rw [hval]

private theorem ae_standardGaussianSqSum_pos {d : ℕ} (hd : 0 < d) :
    ∀ᵐ x : Fin d → ℝ ∂(Measure.pi fun _ : Fin d => standardGaussian),
      0 < standardGaussianSqSum x := by
  let i : Fin d := ⟨0, hd⟩
  have hcoord := Measure.ae_eval_ne (μ := fun _ : Fin d => standardGaussian) i (0 : ℝ)
  filter_upwards [hcoord] with x hx
  by_contra hq
  have hsum : standardGaussianSqSum x = 0 := le_antisymm (le_of_not_gt hq)
    (standardGaussianSqSum_nonneg x)
  have hle : x i ^ 2 ≤ standardGaussianSqSum x := by
    unfold standardGaussianSqSum
    exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hsq : x i ^ 2 = 0 := by nlinarith
  exact hx (sq_eq_zero_iff.mp hsq)

private theorem lintegral_inv_standardGaussianSqSum_pi {d : ℕ} (hd : 2 < d) :
    (∫⁻ x : Fin d → ℝ,
      ENNReal.ofReal ((standardGaussianSqSum x)⁻¹)
        ∂(Measure.pi fun _ : Fin d => standardGaussian)) =
      ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => standardGaussian
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let K : (Fin d → ℝ) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-z.2 * standardGaussianSqSum z.1))
  have hK : Measurable K := by
    dsimp [K]
    fun_prop
  have hpos := ae_standardGaussianSqSum_pos (by omega : 0 < d)
  calc
    _ = ∫⁻ x : Fin d → ℝ, ∫⁻ t : ℝ, K (x, t) ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      simpa [K, μ, ν] using (laplace_lintegral_of_pos hx).symm
    _ = ∫⁻ t : ℝ, ∫⁻ x : Fin d → ℝ, K (x, t) ∂μ ∂ν := by
      calc
        _ = ∫⁻ z : (Fin d → ℝ) × ℝ, K z ∂(μ.prod ν) :=
          (lintegral_prod K hK.aemeasurable).symm
        _ = ∫⁻ t : ℝ, ∫⁻ x : Fin d → ℝ, K (x, t) ∂μ ∂ν :=
          lintegral_prod_symm' K hK
    _ = ∫⁻ t : ℝ, ENNReal.ofReal ((1 + 2 * t) ^ (-(d : ℝ) / 2)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := Set.mem_Ioi.mp ht
      have hInt : Integrable (fun x : Fin d → ℝ =>
          Real.exp (-t * standardGaussianSqSum x)) μ := by
        simpa [μ, standardGaussian] using
          (integrable_exp_sqSum_standardGaussian_pi (r := d) (t := -t)
            (by linarith [ht0]))
      have hmgf : (∫ x : Fin d → ℝ,
          Real.exp (-t * standardGaussianSqSum x) ∂μ) =
          (1 + 2 * t) ^ (-(d : ℝ) / 2) := by
        have hm := integral_exp_sqSum_standardGaussian_pi (r := d) (t := -t)
          (by linarith [ht0])
        rw [show (1 - 2 * -t : ℝ) = 1 + 2 * t by ring] at hm
        simpa [μ, standardGaussian] using hm
      calc
        _ = ENNReal.ofReal (∫ x : Fin d → ℝ,
            Real.exp (-t * standardGaussianSqSum x) ∂μ) := by
          symm
          apply ofReal_integral_eq_lintegral_ofReal hInt
          exact ae_of_all _ fun x => (Real.exp_pos _).le
        _ = ENNReal.ofReal ((1 + 2 * t) ^ (-(d : ℝ) / 2)) := by rw [hmgf]
    _ = ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        exact integral_one_add_two_mul_rpow hd
      · have hp : (-(d : ℝ) / 2) < -1 := by
          have hd' : (2 : ℝ) < d := by exact_mod_cast hd
          linarith
        have hbase := integrableOn_add_rpow_Ioi_of_lt
          (a := -(d : ℝ) / 2) hp (by norm_num : (-1 : ℝ) < 0)
        have hbase' : IntegrableOn (fun u : ℝ =>
            (u + 1) ^ (-(d : ℝ) / 2)) (Set.Ioi (2 * 0)) := by simpa using hbase
        have hcomp := (integrableOn_Ioi_comp_mul_left_iff
          (fun u : ℝ => (u + 1) ^ (-(d : ℝ) / 2)) 0
          (a := 2) (by norm_num : (0 : ℝ) < 2)).2 hbase'
        have hcomp' : IntegrableOn (fun t : ℝ =>
            (2 * t + 1) ^ (-(d : ℝ) / 2)) (Set.Ioi 0) := by simpa using hcomp
        change IntegrableOn (fun t : ℝ =>
          (1 + 2 * t) ^ (-(d : ℝ) / 2)) (Set.Ioi 0)
        exact hcomp'.congr_fun (fun t ht => by
          change (2 * t + 1) ^ (-(d : ℝ) / 2) =
            (1 + 2 * t) ^ (-(d : ℝ) / 2)
          rw [show 2 * t + 1 = 1 + 2 * t by ring]) measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := Set.mem_Ioi.mp ht
        exact Real.rpow_nonneg (by linarith [ht0]) _

theorem integrable_inv_standardGaussianSqSum_pi {d : ℕ} (hd : 2 < d) :
    Integrable (fun x : Fin d → ℝ => (standardGaussianSqSum x)⁻¹)
      (Measure.pi fun _ : Fin d => standardGaussian) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => standardGaussian
  let f : (Fin d → ℝ) → ℝ := fun x => (standardGaussianSqSum x)⁻¹
  have hnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact inv_nonneg.mpr (standardGaussianSqSum_nonneg x)
  have hfinite : (∫⁻ x : Fin d → ℝ, ‖f x‖ₑ ∂μ) < ∞ := by
    calc
      _ = ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (f x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        simp [f, Real.enorm_eq_ofReal (hnonneg x)]
      _ = ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
        simpa [μ, f] using lintegral_inv_standardGaussianSqSum_pi hd
      _ < ∞ := ENNReal.ofReal_lt_top
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).2 hfinite⟩

theorem integral_inv_standardGaussianSqSum_pi {d : ℕ} (hd : 2 < d) :
    (∫ x : Fin d → ℝ, (standardGaussianSqSum x)⁻¹
      ∂(Measure.pi fun _ : Fin d => standardGaussian)) =
      1 / ((d : ℝ) - 2) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => standardGaussian
  let f : (Fin d → ℝ) → ℝ := fun x => (standardGaussianSqSum x)⁻¹
  have hf := integrable_inv_standardGaussianSqSum_pi hd
  have hnonneg : 0 ≤ᵐ[μ] f := ae_of_all _ fun x => inv_nonneg.mpr
    (standardGaussianSqSum_nonneg x)
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hf.aestronglyMeasurable]
  rw [show (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (f x) ∂μ) =
      ENNReal.ofReal (1 / ((d : ℝ) - 2)) from by
        simpa [μ, f] using lintegral_inv_standardGaussianSqSum_pi hd]
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 := by linarith
  have hval : 0 ≤ 1 / ((d : ℝ) - 2) := by positivity
  rw [ENNReal.toReal_ofReal hval]

theorem integrable_inv_olsCenteredDesign_gaussian {d : ℕ} (hd : 2 < d) :
    Integrable (fun G : Fin (d + 1) → ℝ × ℝ => (olsCenteredDesign G)⁻¹)
      (olsPairGaussianLaw (d + 1)) := by
  let μ := olsPairGaussianLaw (d + 1)
  let ν := Measure.pi fun _ : Fin d => standardGaussian
  have hpush : Measure.map olsCenteredDesign μ = ν.map standardGaussianSqSum := by
    change Measure.map olsCenteredDesign (olsPairGaussianLaw (d + 1)) =
      (Measure.pi fun _ : Fin d => standardGaussian).map
        (fun x => ∑ i : Fin d, x i ^ 2)
    simpa [olsPairGaussianLaw, standardGaussian] using
      olsCenteredDesign_gaussian_pushforward d
  have hbase := integrable_inv_standardGaussianSqSum_pi hd
  have hstat : Integrable (fun y : ℝ => y⁻¹) (ν.map standardGaussianSqSum) := by
    exact (integrable_map_measure (by fun_prop)
      (measurable_standardGaussianSqSum.aemeasurable)).mpr hbase
  have hmap : Integrable (fun y : ℝ => y⁻¹) (Measure.map olsCenteredDesign μ) :=
    hpush ▸ hstat
  exact (integrable_map_measure (by fun_prop)
    measurable_olsCenteredDesign.aemeasurable).mp hmap

theorem integral_inv_olsCenteredDesign_gaussian {d : ℕ} (hd : 2 < d) :
    (∫ G : Fin (d + 1) → ℝ × ℝ,
      (olsCenteredDesign G)⁻¹ ∂olsPairGaussianLaw (d + 1)) =
      1 / ((d : ℝ) - 2) := by
  let μ := olsPairGaussianLaw (d + 1)
  let ν := Measure.pi fun _ : Fin d => standardGaussian
  have hpush : Measure.map olsCenteredDesign μ = ν.map standardGaussianSqSum := by
    change Measure.map olsCenteredDesign (olsPairGaussianLaw (d + 1)) =
      (Measure.pi fun _ : Fin d => standardGaussian).map
        (fun x => ∑ i : Fin d, x i ^ 2)
    simpa [olsPairGaussianLaw, standardGaussian] using
      olsCenteredDesign_gaussian_pushforward d
  have hbase := integral_inv_standardGaussianSqSum_pi hd
  calc
    _ = ∫ y : ℝ, y⁻¹ ∂Measure.map olsCenteredDesign μ := by
      symm
      exact integral_map measurable_olsCenteredDesign.aemeasurable (by fun_prop)
    _ = ∫ y : ℝ, y⁻¹ ∂ν.map standardGaussianSqSum := by rw [hpush]
    _ = ∫ x : Fin d → ℝ, (standardGaussianSqSum x)⁻¹ ∂ν := by
      exact integral_map measurable_standardGaussianSqSum.aemeasurable (by fun_prop)
    _ = 1 / ((d : ℝ) - 2) := by
      simpa [ν] using hbase

theorem integral_inv_olsCenteredDesign_gaussian_sample {N : ℕ} (hN : 3 < N) :
    (∫ G : Fin N → ℝ × ℝ, (olsCenteredDesign G)⁻¹ ∂olsPairGaussianLaw N) =
      1 / ((N : ℝ) - 3) := by
  let d := N - 1
  have hd : 2 < d := by dsimp [d]; omega
  have hdim : d + 1 = N := by dsimp [d]; omega
  rw [← hdim]
  rw [integral_inv_olsCenteredDesign_gaussian hd]
  congr 1
  push_cast
  ring

#print axioms ae_standardGaussianSqSum_pos
#print axioms integrable_inv_standardGaussianSqSum_pi
#print axioms integral_inv_standardGaussianSqSum_pi
#print axioms integrable_inv_olsCenteredDesign_gaussian
#print axioms integral_inv_olsCenteredDesign_gaussian
#print axioms integral_inv_olsCenteredDesign_gaussian_sample

end LOOConcentration
