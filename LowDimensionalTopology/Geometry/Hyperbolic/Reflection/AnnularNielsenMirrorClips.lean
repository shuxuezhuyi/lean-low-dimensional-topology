module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularCommonFeetDistinct
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeMirrorConvexSlice
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularMirrorFrontier
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairAllMirrorNielsenInvariance

/-!
# The three exact mirror clips of the original annular Nielsen lift

The same six perpendicular feet bound the intersections of the same actual
Nielsen lift with its three original mirrors. Boundary hyperbolicity is the
explicit existing geometric input; no clip equality is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "K" =>
  HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹' fuchsianNielsenCore D hNE
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout

/-- Each literal mirror meets the same original core in its exact open foot-to-foot segment. -/
theorem annularSixFeet_originalNielsenLift_mirror_clips
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    K ∩ (S 0).carrier = openHSegment p12 p13 ∧
      K ∩ (S 1).carrier = openHSegment p21 p23 ∧
      K ∩ (S 2).carrier = openHSegment p32 p31 := by
  obtain ⟨hoK, hnK, hcK⟩ :=
    annularPairOriginalNielsenLift_properties E r x hE hr hin hout
  obtain ⟨hp12, hp21, hp23, hp32, hp31, hp13⟩ :=
    annularSixFeet_mem_originalNielsenLift_frontier E r x hE hr hin hout hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ :=
    annular_common_perpendicular_feet_ne E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  refine ⟨?_, ?_, ?_⟩
  · exact hcK.inter_mirror_eq_openHSegment hoK hnK (S 0)
      (annularPairMirrors_preserve_originalNielsenLift E r x hE hr hin hout 0)
      p12 p13 h12.1 h13.1 hp12 hp13 hne0
  · exact hcK.inter_mirror_eq_openHSegment hoK hnK (S 1)
      (annularPairMirrors_preserve_originalNielsenLift E r x hE hr hin hout 1)
      p21 p23 h21.1 h23.1 hp21 hp23 hne1
  · exact hcK.inter_mirror_eq_openHSegment hoK hnK (S 2)
      (annularPairMirrors_preserve_originalNielsenLift E r x hE hr hin hout 2)
      p32 p31 h32.1 h31.1 hp32 hp31 hne2.symm

end LowDimensionalTopology.Geometry.Hyperbolic
