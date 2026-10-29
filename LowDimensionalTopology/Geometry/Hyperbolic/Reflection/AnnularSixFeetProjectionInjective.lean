module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularClippedMirrorProjectionInjective
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularNielsenMirrorClips

/-!
# The three actual finite mirror segments project injectively

The same six feet and the original ordinary boundary-hyperbolicity input
provide the three exact Nielsen clips. The native orbit projection is
injective on each full closed foot-to-foot segment.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)

local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "π" =>
  orbitProjection (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ

/-- The original projection is injective on each of the three closed segments
between the same six common-perpendicular feet, including their endpoints. -/
theorem annularSixFeet_orbitProjection_injOn_closed_mirror_segments
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    InjOn π (closedHSegment p12 p13) ∧
      InjOn π (closedHSegment p21 p23) ∧
      InjOn π (closedHSegment p32 p31) := by
  obtain ⟨hclip0, hclip1, hclip2⟩ :=
    annularSixFeet_originalNielsenLift_mirror_clips E r x hE hr hin hout hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ :=
    annular_common_perpendicular_feet_ne E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  exact ⟨annularPairOrbitProjection_injOn_closed_mirror_clip E r x hE hr hin hout
      0 p12 p13 hne0 hclip0,
    annularPairOrbitProjection_injOn_closed_mirror_clip E r x hE hr hin hout
      1 p21 p23 hne1 hclip1,
    annularPairOrbitProjection_injOn_closed_mirror_clip E r x hE hr hin hout
      2 p32 p31 hne2.symm hclip2⟩

end LowDimensionalTopology.Geometry.Hyperbolic
