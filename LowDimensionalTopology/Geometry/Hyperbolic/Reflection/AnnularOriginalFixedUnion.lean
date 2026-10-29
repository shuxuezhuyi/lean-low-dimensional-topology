module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularCoreFixedLocus
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularThreeMirrorClipsDisjoint

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹' fuchsianNielsenCore D hNE
local notation "C" => threeBoundaryOpenCore D hNE
local notation "Moriginal" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" => HyperbolicSurfaceModel.halfPlaneCover Moriginal
local notation "J" => annularPairDiscQuotientReflection E r x hE hr hin hout

/-- The fixed locus on the unchanged original open core is the exact union of its three open clips. -/
theorem annularSixFeet_original_openCore_fixed_union
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    {q : MobiusDomainQuotient (D).domain | q ∈ C ∧ J q = q} =
      ⋃ i : Fin 3, π '' openHSegment (u i) (v i) := by
  dsimp only
  let u : Fin 3 → ℍ := ![p12, p21, p32]
  let v : Fin 3 → ℍ := ![p13, p23, p31]
  obtain ⟨hc0, hc1, hc2⟩ := annularSixFeet_originalNielsenLift_mirror_clips
    E r x hE hr hin hout hB K12 K23 K31 p12 p21 p23 p32 p31 p13
      h12 h21 h23 h32 h31 h13
  have hclip (i : Fin 3) : K ∩ (S i).carrier = openHSegment (u i) (v i) := by
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  have hfixed (q : MobiusDomainQuotient (D).domain) (hq : q ∈ C) :
      J q = q ↔ ∃ i : Fin 3, ∃ z ∈ K ∩ (S i).carrier, π z = q := by
    have hf := annularPairDiscCoreReflection_fixed_iff_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion ⟨q, hq⟩
    constructor
    · intro h
      apply hf.mp
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val (hf.mpr h)
  ext q
  constructor
  · rintro ⟨hq, hJq⟩
    obtain ⟨i, z, hz, hpz⟩ := (hfixed q hq).mp hJq
    exact mem_iUnion.mpr ⟨i, z, (hclip i) ▸ hz, hpz⟩
  · intro hq
    obtain ⟨i, z, hz, hpz⟩ := mem_iUnion.mp hq
    have hzclip : z ∈ K ∩ (S i).carrier := (hclip i).symm ▸ hz
    have hqC : q ∈ C := ⟨(P).cayleyCoordinate z, hzclip.1, hpz⟩
    exact ⟨hqC, (hfixed q hqC).mpr ⟨i, z, hzclip, hpz⟩⟩

/-- The entire closed clips are fixed in the same original closed core and are pairwise disjoint. -/
theorem annularSixFeet_original_closedClips_fixed_and_disjoint
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature D hNE hFG 0 [] 0 3)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    ((⋃ i : Fin 3, π '' closedHSegment (u i) (v i)) ⊆
      {q : MobiusDomainQuotient (D).domain | q ∈ threeBoundaryClosedCore D hNE ∧ J q = q}) ∧
      Pairwise (fun i j =>
        Disjoint (π '' closedHSegment (u i) (v i)) (π '' closedHSegment (u j) (v j))) := by
  dsimp only
  let u : Fin 3 → ℍ := ![p12, p21, p32]
  let v : Fin 3 → ℍ := ![p13, p23, p31]
  let : T2Space (MobiusDomainQuotient (D).domain) :=
    mobiusDomainQuotient_t2 (D).domain (D).discontinuous
  have hopen : {q : MobiusDomainQuotient (D).domain | q ∈ C ∧ J q = q} =
      ⋃ i : Fin 3, π '' openHSegment (u i) (v i) :=
    annularSixFeet_original_openCore_fixed_union E r x hE hr hin hout hTorsion hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ := annular_common_perpendicular_feet_ne
    E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hne (i : Fin 3) : u i ≠ v i := by
    fin_cases i
    · exact hne0
    · exact hne1
    · exact hne2.symm
  have hπ : Continuous π :=
    (mobiusDomainProjection_continuous (D).domain).comp (P).cayleyCoordinate.continuous
  have hclosed : IsClosed {q : MobiusDomainQuotient (D).domain | J q = q} :=
    isClosed_eq (J).continuous continuous_id
  have hsub (i : Fin 3) : π '' openHSegment (u i) (v i) ⊆
      {q : MobiusDomainQuotient (D).domain | q ∈ C ∧ J q = q} := by
    intro q hq
    rw [hopen]
    exact mem_iUnion.mpr ⟨i, hq⟩
  refine ⟨?_, annularSixFeet_original_closedMirrorClips_pairwise_disjoint
    E r x hE hr hin hout hB hsig K12 K23 K31 p12 p21 p23 p32 p31 p13
      h12 h21 h23 h32 h31 h13⟩
  intro q hq
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hq
  have hcl : π z ∈ closure (π '' openHSegment (u i) (v i)) := by
    apply image_closure_subset_closure_image hπ
    exact ⟨z, (closure_openHSegment (hne i)).symm ▸ hz, rfl⟩
  have hC : π z ∈ closure C := closure_mono (fun _ hy => (hsub i hy).1) hcl
  refine ⟨?_, (closure_minimal (fun _ hy => (hsub i hy).2) hclosed) hcl⟩
  rw [← closure_threeBoundaryOpenCore D hNE]
  exact hC

end LowDimensionalTopology.Geometry.Hyperbolic
