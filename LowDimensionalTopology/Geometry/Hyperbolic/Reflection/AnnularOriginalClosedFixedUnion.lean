module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalClosedSlices
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalFixedUnion

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
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹' fuchsianNielsenCore D hNE
local notation "Moriginal" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" => HyperbolicSurfaceModel.halfPlaneCover Moriginal
local notation "J" => annularPairDiscQuotientReflection E r x hE hr hin hout
local notation "πn" => orbitProjection G ℍ
local notation "Jn" => annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr

/-- The same original closed core has exactly the three disjoint entire closed clips as its fixed set. -/
theorem annularSixFeet_original_closedCore_fixed_union
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature D hNE hFG 0 [] 0 3)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    ({q : MobiusDomainQuotient (D).domain | q ∈ threeBoundaryClosedCore D hNE ∧ J q = q} =
      ⋃ i : Fin 3, π '' closedHSegment (u i) (v i)) ∧
      Pairwise (fun i j =>
        Disjoint (π '' closedHSegment (u i) (v i)) (π '' closedHSegment (u j) (v j))) := by
  dsimp only
  let u : Fin 3 → ℍ := ![p12, p21, p32]
  let v : Fin 3 → ℍ := ![p13, p23, p31]
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  obtain ⟨hforward, hdisjoint⟩ := annularSixFeet_original_closedClips_fixed_and_disjoint
    E r x hE hr hin hout hTorsion hB hsig K12 K23 K31 p12 p21 p23 p32 p31 p13
      h12 h21 h23 h32 h31 h13
  obtain ⟨hc0, hc1, hc2⟩ := annularSixFeet_originalNielsenLift_closed_mirror_clips
    E r x hE hr hin hout hB K12 K23 K31 p12 p21 p23 p32 p31 p13
      h12 h21 h23 h32 h31 h13
  have hclip (i : Fin 3) : closure K ∩ (S i).carrier = closedHSegment (u i) (v i) := by
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  have hG (a : G) : MapsTo (a.val : ℍ → ℍ) (closure K) (closure K) := by
    have ha : MapsTo (a.val : ℍ → ℍ) K K := fun z hz =>
      annularPairNativeGroup_preserves_originalNielsenLift E r x hE hr hin hout a z hz
    exact ha.closure a.val.continuous
  have hproj (z : ℍ) : Φ (πn z) = π z :=
    annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z
  refine ⟨subset_antisymm ?_ hforward, hdisjoint⟩
  rintro q ⟨hq, hJq⟩
  obtain ⟨ξ, hξ, hξq⟩ := hq
  let w : ℍ := (P).cayleyCoordinate.symm ξ
  have hw : w ∈ closure K := by
    rw [← (P).cayleyCoordinate.preimage_closure]
    change (P).cayleyCoordinate ((P).cayleyCoordinate.symm ξ) ∈
      closure (fuchsianNielsenCore D hNE)
    simpa only [(P).cayleyCoordinate.apply_symm_apply] using hξ
  have hwq : π w = q := by
    change mobiusDomainProjection (D).domain
      ((P).cayleyCoordinate ((P).cayleyCoordinate.symm ξ)) = q
    rw [(P).cayleyCoordinate.apply_symm_apply]
    exact hξq
  have hnw : πn w = Φ.symm q := by
    apply Φ.injective
    rw [hproj w, hwq, Φ.apply_symm_apply]
  have hfix : Jn (Φ.symm q) = Φ.symm q := by
    apply Φ.injective
    change J q = Φ (Φ.symm q)
    rw [Φ.apply_symm_apply]
    exact hJq
  obtain ⟨i, z, hzS, hpz⟩ :=
    (annularPairQuotientReflection_fixed_iff_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion (Φ.symm q)).mp hfix
  have he : πn z = πn w := hpz.trans hnw.symm
  obtain ⟨a, ha⟩ := (Quotient.exact he : MulAction.orbitRel G ℍ z w)
  have haz : a • w = z := ha
  have hzK : z ∈ closure K := haz ▸ hG a hw
  have hzclip : z ∈ closedHSegment (u i) (v i) := (hclip i) ▸ And.intro hzK hzS
  have hzq : π z = q := by
    rw [← hproj z, hpz, Φ.apply_symm_apply]
  exact mem_iUnion.mpr ⟨i, z, hzclip, hzq⟩

end LowDimensionalTopology.Geometry.Hyperbolic
