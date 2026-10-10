import LOOConcentration.Results.GoodSetTailTransfer
import LOOConcentration.Analysis.DatasetClipMollify
import LOOConcentration.Concentration.SegmentEstimate
import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Local slope of the actual good-set extension

The extension has a global Lipschitz estimate in the frozen dataset norm.
Flattening coordinates is an equivalence with exact frozen-norm transport;
the inherited function-space norm is not identified with the Euclidean norm.
-/

set_option autoImplicit false

open Filter
open MeasureTheory
open scoped Topology

namespace LOOConcentration

private def goodSetExtension_coordinateEquiv {k m n : ℕ} :
    DataCarrier k m n ≃
      EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) where
  toFun := datasetToEuclidean
  invFun := datasetFromEuclidean
  left_inv := datasetFromEuclidean_toEuclidean
  right_inv := datasetToEuclidean_fromEuclidean

private theorem goodSetExtension_datasetNorm_sub_eq_euclidean
    {k m n : ℕ} (D E : DataCarrier k m n) :
    datasetNorm (D - E) =
      ‖goodSetExtension_coordinateEquiv D -
        goodSetExtension_coordinateEquiv E‖ := by
  simpa [goodSetExtension_coordinateEquiv] using datasetNorm_sub_eq_euclidean D E

private theorem goodSetExtension_punctured_neBot {k m n : ℕ}
    (D : DataCarrier k m n) : NeBot (𝓝[≠] D) := by
  have hPerfect : PerfectSpace (DataCarrier k m n) := perfectSpace_of_module ℝ _
  have hAcc : AccPt D (𝓟 (Set.univ : Set (DataCarrier k m n))) :=
    hPerfect.univ_preperfect D (by simp)
  have hPunctured := accPt_principal_iff_nhdsWithin.mp hAcc
  have hset : (Set.univ : Set (DataCarrier k m n)) \ {D} = {E | E ≠ D} := by
    ext E
    simp
  rw [hset] at hPunctured
  exact hPunctured

/-- Regard the corrected McShane extension on the full carrier as an actual
frozen locally Lipschitz dataset function. -/
noncomputable def goodSetLipschitzExtension_localFunction {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    LocallyLipschitzDataFunction k m (n + 1) := by
  refine ⟨goodSetLipschitzExtension D₀ hD₀ hLK hLip, ?_⟩
  intro D
  refine ⟨Set.univ, by simp, LK, hLK, ?_⟩
  intro E hE F hF
  exact goodSetLipschitzExtension_lipschitz D₀ hD₀ hLK hLip E F

/-- The actual extension's frozen local slope is bounded everywhere by its
source Lipschitz constant. The punctured-neighborhood limsup is finite by the
local Lipschitz witness and nontrivial because the real dataset carrier is a
perfect space. -/
theorem goodSetLipschitzExtension_localSlope_le {k m n : ℕ}
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    ∀ D : DataCarrier k m (n + 1),
      datasetLocalSlope
        (goodSetLipschitzExtension_localFunction D₀ hD₀ hLK hLip) D ≤ LK := by
  let F := goodSetLipschitzExtension_localFunction D₀ hD₀ hLK hLip
  intro D
  let q : DataCarrier k m (n + 1) → ℝ := fun E =>
    |F.1 E - F.1 D| / datasetNorm (E - D)
  have hbounded : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) q := by
    simpa [q, F] using datasetSlope_bounded F D
  have hfreq : ∃ᶠ E in 𝓝[≠] D, 0 ≤ q E :=
    @Filter.Frequently.of_forall _ _ (goodSetExtension_punctured_neBot D) _
      (fun E => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have hcobounded : (𝓝[≠] D).IsCoboundedUnder (· ≤ ·) q :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := 0) hfreq
  rw [datasetLocalSlope]
  change limsup q (𝓝[≠] D) ≤ LK
  apply (Filter.limsup_le_iff' hcobounded hbounded).2
  intro c hc
  filter_upwards [self_mem_nhdsWithin] with E hED
  have hne : E ≠ D := by simpa using hED
  have hcoord_ne : goodSetExtension_coordinateEquiv E ≠
      goodSetExtension_coordinateEquiv D := by
    intro hcoord
    exact hne (goodSetExtension_coordinateEquiv.injective hcoord)
  have hden : 0 < datasetNorm (E - D) := by
    rw [goodSetExtension_datasetNorm_sub_eq_euclidean]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hcoord_ne)
  have hsource : |F.1 E - F.1 D| ≤ LK * datasetNorm (E - D) := by
    exact goodSetLipschitzExtension_lipschitz D₀ hD₀ hLK hLip E D
  have hnum : |F.1 E - F.1 D| ≤ c * datasetNorm (E - D) := by
    calc
      |F.1 E - F.1 D| ≤ LK * datasetNorm (E - D) := hsource
      _ ≤ c * datasetNorm (E - D) :=
        mul_le_mul_of_nonneg_right (le_of_lt hc) (Real.sqrt_nonneg _)
  exact (div_le_iff₀ hden).2 hnum

/-- The full-carrier integrability producer for this actual extension, obtained
from the reviewed wave-7 L²/MemLp/Bochner-integrability result. -/
theorem goodSetLipschitzExtension_localFunction_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ)
    {K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2))}
    {H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ} {LK : ℝ}
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2))
    (hD₀ : D₀ ∈ K) (hLK : 0 ≤ LK)
    (hLip : ∀ D ∈ K, ∀ E ∈ K,
      |H D - H E| ≤ LK * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    Integrable
      (goodSetLipschitzExtension_localFunction D₀ hD₀ hLK hLip).1 ν := by
  simpa [goodSetLipschitzExtension_localFunction] using
    (goodSetLipschitzExtension_integrable μ hM₂ D₀ hD₀ hLK hLip)

end LOOConcentration

#print axioms LOOConcentration.goodSetLipschitzExtension_localFunction
#print axioms LOOConcentration.goodSetLipschitzExtension_localSlope_le
#print axioms LOOConcentration.goodSetLipschitzExtension_localFunction_integrable
