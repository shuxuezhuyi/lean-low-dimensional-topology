module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.CommonPerpendicularInvariance
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalPeripheralGeodesics
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ThreePeripheralMatrices
public import LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition

/-!
# The original annular perpendicular axes lie on the original core frontier

The actual boundary-hyperbolic words identify their complete axes with the
boundary of the same Nielsen lift. The original six perpendicular feet therefore
lie on that frontier, ready for the native mirror-slice construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Mobius Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "K" =>
  HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹' fuchsianNielsenCore D hNE
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "A" => annularPeripheralMatrix E r x (zero_lt_one.trans hE) hr
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout

/-- An actual invariant line of a literal peripheral matrix is on the same core frontier. -/
theorem annularPeripheralInvariantLine_subset_originalNielsenLift_frontier
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (i : Fin 3) (N : HalfPlaneLine)
    (hN : (A i • · : ℍ → ℍ) '' N.carrier = N.carrier) :
    N.carrier ⊆ frontier K := by
  obtain ⟨hA, ht, M, _q, hphysical, _hcov, _hperiod, _hlength, _htrace⟩ :=
    annularDiscPeripheralWord_original_simple_closed_geodesic E r x hE hr hin hout
      hB i (A i) (annularPeripheralMatrix_disc E r x hE hr hin hout i)
  have haxis : N = hHyperbolicAxis (A i) hA ht :=
    hHyperbolicAxis_unique_invariant (A i) hA ht N hN
  obtain ⟨L, hL, hML⟩ :=
    nielsenBoundaryHyperbolic_axis_mem_family D hNE (g i) (hB i) M
  have hMfront :
      (Subtype.val : (D).domain.carrier → ExtendedComplex) ⁻¹' M.carrier ⊆
        frontier (fuchsianNielsenCore D hNE) := by
    intro u hu
    change u.val ∈ M.carrier at hu
    rw [hML] at hu
    obtain ⟨u', ⟨v, hvL, hvu'⟩, hu'u⟩ := hu
    have hvu : (D).finiteCoordinate.symm v = u :=
      hvu'.trans (Subtype.ext hu'u)
    obtain ⟨w, hwF, hwv⟩ :=
      nielsenBoundaryDiscLineFamily_subset_frontier D hNE L hL hvL
    have hwu : w = u := by
      apply (D).finiteCoordinate.injective
      rw [hwv, ← hvu, (D).finiteCoordinate.apply_symm_apply]
    exact hwu ▸ hwF
  have hcoord (z : ℍ) : ((P).cayleyCoordinate z).val =
      cayleyMobius.val (halfPlaneBoundaryPoint z) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
    change _ = cayleyMobius.val (((z : ℂ) : ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  intro z hz
  have hzAxis : z ∈ (hHyperbolicAxis (A i) hA ht).carrier := haxis ▸ hz
  have hzM : ((P).cayleyCoordinate z).val ∈ M.carrier := by
    rw [← hphysical]
    exact ⟨halfPlaneBoundaryPoint z, ⟨z, hzAxis, rfl⟩, (hcoord z).symm⟩
  change z ∈ frontier ((P).cayleyCoordinate ⁻¹' fuchsianNielsenCore D hNE)
  rw [← (P).cayleyCoordinate.preimage_frontier]
  exact hMfront hzM

/-- The three common perpendiculars from the same six feet are complete frontier axes. -/
theorem annularSixFeet_axes_subset_originalNielsenLift_frontier
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    K12.carrier ⊆ frontier K ∧ K23.carrier ⊆ frontier K ∧
      K31.carrier ⊆ frontier K := by
  refine ⟨?_, ?_, ?_⟩
  · apply annularPeripheralInvariantLine_subset_originalNielsenLift_frontier
      E r x hE hr hin hout hB 0 K12
    change (reflectionProductSL (S 0) (S 1) • · : ℍ → ℍ) '' K12.carrier = K12.carrier
    exact reflectionProductSL_preserves_perpendicular (S 0) (S 1) K12 p12 p21 h12 h21
  · apply annularPeripheralInvariantLine_subset_originalNielsenLift_frontier
      E r x hE hr hin hout hB 2 K23
    change (reflectionProductSL (S 1) (S 2) • · : ℍ → ℍ) '' K23.carrier = K23.carrier
    exact reflectionProductSL_preserves_perpendicular (S 1) (S 2) K23 p23 p32 h23 h32
  · apply annularPeripheralInvariantLine_subset_originalNielsenLift_frontier
      E r x hE hr hin hout hB 1 K31
    change (reflectionProductSL (S 2) (S 0) • · : ℍ → ℍ) '' K31.carrier = K31.carrier
    exact reflectionProductSL_preserves_perpendicular (S 2) (S 0) K31 p31 p13 h31 h13

/-- Every one of the same six chosen feet lies on the actual native core frontier. -/
theorem annularSixFeet_mem_originalNielsenLift_frontier
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    p12 ∈ frontier K ∧ p21 ∈ frontier K ∧ p23 ∈ frontier K ∧
      p32 ∈ frontier K ∧ p31 ∈ frontier K ∧ p13 ∈ frontier K := by
  obtain ⟨hF12, hF23, hF31⟩ :=
    annularSixFeet_axes_subset_originalNielsenLift_frontier E r x hE hr hin hout hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  exact ⟨hF12 h12.2.1, hF12 h21.2.1, hF23 h23.2.1,
    hF23 h32.2.1, hF31 h31.2.1, hF31 h13.2.1⟩

/-- The old explicit boundary-recognition input supplies the needed frontier feet. -/
theorem annularSixFeet_frontier_of_boundaryRecognition
    (hBoundary : LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    p12 ∈ frontier K ∧ p21 ∈ frontier K ∧ p23 ∈ frontier K ∧
      p32 ∈ frontier K ∧ p31 ∈ frontier K ∧ p13 ∈ frontier K := by
  exact annularSixFeet_mem_originalNielsenLift_frontier E r x hE hr hin hout
    (hBoundary E r x hE hr hin hout).1 K12 K23 K31 p12 p21 p23 p32 p31 p13
    h12 h21 h23 h32 h31 h13

end LowDimensionalTopology.Geometry.Hyperbolic
