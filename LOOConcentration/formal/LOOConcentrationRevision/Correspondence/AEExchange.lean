module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Almost everywhere exchange with arbitrary coefficients

The first theorem exchanges iterated almost everywhere quantifiers when a
measurable predicate is restricted by an arbitrary observation-side predicate.
The second theorem uses rational upper coefficient boxes to exchange affine
bounds whose coefficient functions need not be measurable.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal

namespace LOOConcentration.Correspondence

/-- Exchange iterated almost everywhere quantifiers under an arbitrary gate
on a finite-measure observation space. -/
theorem ae_ae_exchange_imp {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {ν : Measure X} {μ : Measure Z} [SFinite ν] [IsFiniteMeasure μ]
    {Q : X → Z → Prop} (hQ : MeasurableSet {p : X × Z | Q p.1 p.2})
    (E : Z → Prop) :
    (∀ᵐ x ∂ν, ∀ᵐ z ∂μ, E z → Q x z) ↔
      ∀ᵐ z ∂μ, ∀ᵐ x ∂ν, E z → Q x z := by
  let H : Set Z := toMeasurable μ {z | E z}
  have hH : MeasurableSet H := by
    exact measurableSet_toMeasurable μ {z | E z}
  have hQx (x : X) : MeasurableSet {z | Q x z} := by
    have h := measurable_prodMk_left hQ (x := x)
    convert h using 1
    ext z
    rfl
  have hgate : MeasurableSet {p : X × Z | p.2 ∈ H} := by
    have h := hH.preimage (measurable_snd : Measurable (Prod.snd : X × Z → Z))
    convert h using 1
    ext p
    rfl
  have hImp : MeasurableSet {p : X × Z | p.2 ∈ H → Q p.1 p.2} := by
    have h := hgate.compl.union hQ
    convert h using 1
    ext ⟨x, z⟩
    exact imp_iff_not_or
  constructor
  · intro h
    have hHq : ∀ᵐ x ∂ν, ∀ᵐ z ∂μ, z ∈ H → Q x z := by
      filter_upwards [h] with x hx
      have hzero : μ ({z | E z} ∩ {z | ¬ Q x z}) = 0 := by
        have hzero := ae_iff.mp hx
        have hset : {z | ¬ (E z → Q x z)} = {z | E z} ∩ {z | ¬ Q x z} := by
          ext z
          simp
        rw [hset] at hzero
        exact hzero
      have hzeroH : μ (H ∩ {z | ¬ Q x z}) = 0 := by
        have hQbad : MeasurableSet {z | ¬ Q x z} := by
          change MeasurableSet ({z | Q x z}ᶜ)
          exact (hQx x).compl
        calc
          μ (H ∩ {z | ¬ Q x z}) =
              μ (toMeasurable μ {z | E z} ∩ {z | ¬ Q x z}) := rfl
          _ = μ ({z | E z} ∩ {z | ¬ Q x z}) :=
            Measure.measure_toMeasurable_inter hQbad (measure_ne_top μ _)
          _ = 0 := hzero
      have hset : {z | ¬ (z ∈ H → Q x z)} = H ∩ {z | ¬ Q x z} := by
        ext z
        simp
      rw [ae_iff, hset]
      exact hzeroH
    have hflip := (ae_ae_comm hImp).mp hHq
    filter_upwards [hflip] with z hz
    filter_upwards [hz] with x hx
    intro hzE
    exact hx (subset_toMeasurable μ {z | E z} hzE)
  · intro h
    have hC : MeasurableSet {z | ∀ᵐ x ∂ν, Q x z} := by
      let B : Set (Z × X) := {p | ¬ Q p.2 p.1}
      have hB : MeasurableSet B := by
        have h := hQ.compl.preimage measurable_swap
        convert h using 1
        ext ⟨z, x⟩
        rfl
      let f : Z → ℝ≥0∞ := fun z => ν (Prod.mk z ⁻¹' B)
      have hf : Measurable f := by
        dsimp [f]
        exact measurable_measure_prodMk_left hB
      have hEq : {z | ∀ᵐ x ∂ν, Q x z} = {z | f z = 0} := by
        ext z
        change (∀ᵐ x ∂ν, Q x z) ↔ f z = 0
        rw [ae_iff]
        rfl
      rw [hEq]
      exact isClosed_singleton.measurableSet.preimage hf
    have hnull : μ ({z | E z} ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z}) = 0 := by
      have hzero := ae_iff.mp h
      have hset : {z | ¬ (∀ᵐ x ∂ν, E z → Q x z)} =
          {z | E z} ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z} := by
        ext z
        by_cases hz : E z <;> simp [hz]
      rw [hset] at hzero
      exact hzero
    have hnullH : μ (H ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z}) = 0 := by
      have hBad : MeasurableSet {z | ¬ ∀ᵐ x ∂ν, Q x z} := by
        change MeasurableSet ({z | ∀ᵐ x ∂ν, Q x z}ᶜ)
        exact hC.compl
      calc
        μ (H ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z}) =
            μ (toMeasurable μ {z | E z} ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z}) := rfl
        _ = μ ({z | E z} ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z}) :=
          Measure.measure_toMeasurable_inter hBad (measure_ne_top μ _)
        _ = 0 := hnull
    have hAEH : ∀ᵐ z ∂μ, z ∈ H → ∀ᵐ x ∂ν, Q x z := by
      have hset : {z | ¬ (z ∈ H → ∀ᵐ x ∂ν, Q x z)} =
          H ∩ {z | ¬ ∀ᵐ x ∂ν, Q x z} := by
        ext z
        simp
      rw [ae_iff, hset]
      exact hnullH
    have hHq : ∀ᵐ z ∂μ, ∀ᵐ x ∂ν, z ∈ H → Q x z := by
      filter_upwards [hAEH] with z hz
      by_cases hzH : z ∈ H
      · filter_upwards [hz hzH] with x hx
        intro _
        exact hx
      · exact Filter.Eventually.of_forall fun _ hx => False.elim (hzH hx)
    have hflip := (ae_ae_comm hImp).mpr hHq
    filter_upwards [hflip] with x hx
    filter_upwards [hx] with z hz
    intro hzE
    exact hz (subset_toMeasurable μ {z | E z} hzE)

/-- Exchange iterated almost everywhere quantifiers in an affine bound with
arbitrary real observation-side rates. -/
theorem ae_ae_exchange_real_rates {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {ν : Measure X} {μ : Measure Z} [SFinite ν] [IsFiniteMeasure μ]
    (G : X × Z → ℝ) (size : X → ℝ) (a b : Z → ℝ)
    (hG : Measurable G) (hsize : Measurable size) (hsize_nonneg : ∀ x, 0 ≤ size x) :
    (∀ᵐ x ∂ν, ∀ᵐ z ∂μ, G (x, z) ≤ a z + b z * size x) ↔
      ∀ᵐ z ∂μ, ∀ᵐ x ∂ν, G (x, z) ≤ a z + b z * size x := by
  let Q : ℚ → ℚ → X → Z → Prop :=
    fun q r x z => G (x, z) ≤ (q : ℝ) + (r : ℝ) * size x
  let E : ℚ → ℚ → Z → Prop :=
    fun q r z => a z < (q : ℝ) ∧ b z < (r : ℝ)
  have hQ (q r : ℚ) : MeasurableSet {p : X × Z | Q q r p.1 p.2} := by
    dsimp [Q]
    apply measurableSet_le hG
    fun_prop
  have hactual (x : X) (z : Z)
      (hqrs : ∀ q r : ℚ, E q r z → Q q r x z) :
      G (x, z) ≤ a z + b z * size x := by
    by_contra hnot
    have hgap : 0 < G (x, z) - (a z + b z * size x) := by
      have : a z + b z * size x < G (x, z) := lt_of_not_ge hnot
      linarith
    let gap := G (x, z) - (a z + b z * size x)
    let eps := gap / (2 * (size x + 1))
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      exact hgap
    have hden_pos : 0 < 2 * (size x + 1) := by
      have hsize1 : 0 < size x + 1 := by linarith [hsize_nonneg x]
      positivity
    have heps : 0 < eps := by
      dsimp [eps]
      exact div_pos hgap_pos hden_pos
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_add_of_pos_right (a z) heps)
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (lt_add_of_pos_right (b z) heps)
    have hqr := hqrs q r ⟨hq₁, hr₁⟩
    have hproxy : (q : ℝ) + (r : ℝ) * size x <
        a z + b z * size x + eps * (size x + 1) := by
      calc
        (q : ℝ) + (r : ℝ) * size x <
            (a z + eps) + (r : ℝ) * size x := by linarith
        _ ≤ (a z + eps) + (b z + eps) * size x := by
          have hmul := mul_le_mul_of_nonneg_right (le_of_lt hr₂) (hsize_nonneg x)
          linarith
        _ = a z + b z * size x + eps * (size x + 1) := by ring
    have hcancel : eps * (size x + 1) = gap / 2 := by
      have hnonzero : size x + 1 ≠ 0 := by linarith [hsize_nonneg x]
      dsimp [eps]
      field_simp [hnonzero]
    have hhalf : gap / 2 < gap := by
      linarith
    have hstrict : (q : ℝ) + (r : ℝ) * size x < G (x, z) := by
      calc
        (q : ℝ) + (r : ℝ) * size x <
            a z + b z * size x + eps * (size x + 1) := hproxy
        _ < a z + b z * size x + gap := by
          rw [hcancel]
          linarith
        _ = G (x, z) := by
          dsimp [gap]
          ring
    exact (not_lt_of_ge hqr) hstrict
  constructor
  · intro h
    have hproxy (q r : ℚ) :
        ∀ᵐ x ∂ν, ∀ᵐ z ∂μ, E q r z → Q q r x z := by
      filter_upwards [h] with x hx
      filter_upwards [hx] with z hz
      intro hE
      rcases hE with ⟨hq, hr⟩
      calc
        G (x, z) ≤ a z + b z * size x := hz
        _ ≤ (q : ℝ) + b z * size x :=
          by linarith
        _ ≤ (q : ℝ) + (r : ℝ) * size x := by
          have hmul := mul_le_mul_of_nonneg_right (le_of_lt hr) (hsize_nonneg x)
          linarith
    have hproxy' (q r : ℚ) :
        ∀ᵐ z ∂μ, ∀ᵐ x ∂ν, E q r z → Q q r x z :=
      (ae_ae_exchange_imp (hQ q r) (E q r)).1 (hproxy q r)
    have hproxy_all : ∀ᵐ z ∂μ, ∀ q : ℚ, ∀ r : ℚ,
        ∀ᵐ x ∂ν, E q r z → Q q r x z := by
      apply ae_all_iff.mpr
      intro q
      apply ae_all_iff.mpr
      intro r
      exact hproxy' q r
    filter_upwards [hproxy_all] with z hz
    have hproxy_x : ∀ᵐ x ∂ν, ∀ q : ℚ, ∀ r : ℚ, E q r z → Q q r x z := by
      apply ae_all_iff.mpr
      intro q
      apply ae_all_iff.mpr
      intro r
      exact hz q r
    filter_upwards [hproxy_x] with x hx
    exact hactual x z hx
  · intro h
    have hproxy (q r : ℚ) :
        ∀ᵐ z ∂μ, ∀ᵐ x ∂ν, E q r z → Q q r x z := by
      filter_upwards [h] with z hz
      filter_upwards [hz] with x hx
      intro hE
      rcases hE with ⟨hq, hr⟩
      calc
        G (x, z) ≤ a z + b z * size x := hx
        _ ≤ (q : ℝ) + b z * size x :=
          by linarith
        _ ≤ (q : ℝ) + (r : ℝ) * size x := by
          have hmul := mul_le_mul_of_nonneg_right (le_of_lt hr) (hsize_nonneg x)
          linarith
    have hproxy' (q r : ℚ) :
        ∀ᵐ x ∂ν, ∀ᵐ z ∂μ, E q r z → Q q r x z :=
      (ae_ae_exchange_imp (hQ q r) (E q r)).2 (hproxy q r)
    have hproxy_all : ∀ᵐ x ∂ν, ∀ q : ℚ, ∀ r : ℚ,
        ∀ᵐ z ∂μ, E q r z → Q q r x z := by
      apply ae_all_iff.mpr
      intro q
      apply ae_all_iff.mpr
      intro r
      exact hproxy' q r
    filter_upwards [hproxy_all] with x hx
    have hproxy_z : ∀ᵐ z ∂μ, ∀ q : ℚ, ∀ r : ℚ, E q r z → Q q r x z := by
      apply ae_all_iff.mpr
      intro q
      apply ae_all_iff.mpr
      intro r
      exact hx q r
    filter_upwards [hproxy_z] with z hz
    exact hactual x z hz

end LOOConcentration.Correspondence
