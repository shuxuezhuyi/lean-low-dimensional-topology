module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalEndpointPairs
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularDistinctMirrorClips
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularNielsenMirrorClips
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCayleyOrbitTransport

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups.Action

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹'
  fuchsianNielsenCore D hNE
local notation "Moriginal" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" => HyperbolicSurfaceModel.halfPlaneCover Moriginal
local notation "πnative" => orbitProjection G ℍ

/-- The same three closed foot-to-foot mirror segments have disjoint images
on the unchanged original disc quotient, including all six endpoints. -/
theorem annularSixFeet_original_closedMirrorClips_pairwise_disjoint
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature D hNE hFG 0 [] 0 3)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    Pairwise (fun i j => Disjoint (π '' closedHSegment (u i) (v i))
      (π '' closedHSegment (u j) (v j))) := by
  let u : Fin 3 → ℍ := ![p12, p21, p32]
  let v : Fin 3 → ℍ := ![p13, p23, p31]
  change Pairwise (fun i j => Disjoint (π '' closedHSegment (u i) (v i))
    (π '' closedHSegment (u j) (v j)))
  obtain ⟨hclip0, hclip1, hclip2⟩ :=
    annularSixFeet_originalNielsenLift_mirror_clips E r x hE hr hin hout hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hclip (i : Fin 3) : K ∩ (S i).carrier = openHSegment (u i) (v i) := by
    fin_cases i
    · exact hclip0
    · exact hclip1
    · exact hclip2
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ :=
    annular_common_perpendicular_feet_ne E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hne (i : Fin 3) : u i ≠ v i := by
    fin_cases i
    · exact hne0
    · exact hne1
    · exact hne2.symm
  have hpairs : Pairwise (fun i j =>
      ({π (u i), π (v i)} : Set (MobiusDomainQuotient (D).domain)) ≠
        {π (u j), π (v j)}) :=
    annularSixFeet_original_endpointPairs_pairwise_ne E r x hE hr hin hout hB hsig
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  have hproj (z : ℍ) : Φ (πnative z) = π z :=
    (annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z).trans
      (annularOriginal_halfPlaneCover_eq_cayleyProjection E r x hE hr hin hout z).symm
  have hpairsNative : Pairwise (fun i j =>
      ({πnative (u i), πnative (v i)} : Set (orbitQuotient G ℍ)) ≠
        {πnative (u j), πnative (v j)}) := by
    intro i j hij he
    apply hpairs hij
    have himage := congrArg (fun T : Set (orbitQuotient G ℍ) => Φ '' T) he
    simpa only [image_pair, hproj] using himage
  have hnative : Pairwise (fun i j => Disjoint
      (πnative '' closedHSegment (u i) (v i))
      (πnative '' closedHSegment (u j) (v j))) := by
    intro i j hij
    exact annularPairOrbitProjection_mirror_clips_disjoint E r x hE hr hin hout
      i j (u i) (v i) (u j) (v j) (hne i) (hne j) (hclip i) (hclip j) (hpairsNative hij)
  have himage (T : Set ℍ) : Φ '' (πnative '' T) = π '' T := by
    rw [image_image]
    exact congrArg (fun f : ℍ → MobiusDomainQuotient (D).domain => f '' T) (funext hproj)
  intro i j hij
  simpa only [himage] using disjoint_image_of_injective Φ.injective (hnative hij)

end LowDimensionalTopology.Geometry.Hyperbolic
