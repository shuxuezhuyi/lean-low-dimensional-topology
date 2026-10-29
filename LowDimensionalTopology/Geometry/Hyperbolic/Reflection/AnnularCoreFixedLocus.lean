module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularQuotientFixedLocus
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairAllMirrorNielsenInvariance
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairDiscCoreReflection

/-! The existing fixed-locus equivalence restricts to the same original
Nielsen core and transports through the actual restricted Cayley map. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
variable (hin : 1 + r < x) (hout : x + r < E)

local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "π" => orbitProjection G ℍ
local notation "J" => annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹'
  fuchsianNielsenCore (HalfPlaneFuchsianGroup.cayleyData P)
  (annularPairReflectionDiscGroup_nonElementary E r x hE hr hin)
local notation "C" => π '' K
local notation "Cd" => threeBoundaryOpenCore (HalfPlaneFuchsianGroup.cayleyData P)
  (annularPairReflectionDiscGroup_nonElementary E r x hE hr hin)

/-- Every fixed point in the actual native core image has an original mirror
lift in the same literal Nielsen lift, under the explicit torsion premise. -/
theorem annularPairQuotientReflection_fixed_iff_core_mirror_projection_of_torsion
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (q : orbitQuotient G ℍ) (hq : q ∈ C) :
    J q = q ↔ ∃ i : Fin 3, ∃ z ∈ K ∩ (S i).carrier, π z = q := by
  constructor
  · intro hf
    obtain ⟨i, z, hz, hp⟩ :=
      (annularPairQuotientReflection_fixed_iff_mirror_projection_of_torsion
        E r x hE hr hin hout hTorsion q).mp hf
    obtain ⟨w, hw, hpw⟩ := hq
    have he : π z = π w := hp.trans hpw.symm
    obtain ⟨g, hg⟩ := (Quotient.exact he : MulAction.orbitRel G ℍ z w)
    have hzK : g • w ∈ K :=
      annularPairNativeGroup_preserves_originalNielsenLift E r x hE hr hin hout g w hw
    have hgw : g • w = z := hg
    exact ⟨i, g • w, ⟨hzK, hgw.symm ▸ hz⟩, (congrArg π hgw).trans hp⟩
  · rintro ⟨i, z, hz, hp⟩
    exact (annularPairQuotientReflection_fixed_iff_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion q).mpr ⟨i, z, hz.2, hp⟩

/-- The unchanged native core reflection has exactly the original clipped
mirror projections as fixed points, with the same explicit torsion premise. -/
theorem annularPairCoreReflection_fixed_iff_mirror_projection_of_torsion
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (q : C) :
    annularPairCoreReflection E r x hE hr hin hout q = q ↔
      ∃ i : Fin 3, ∃ z ∈ K ∩ (S i).carrier, π z = q.val := by
  constructor
  · intro hf
    exact (annularPairQuotientReflection_fixed_iff_core_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion q.val q.property).mp (congrArg Subtype.val hf)
  · intro hf
    apply Subtype.ext
    change J q.val = q.val
    exact (annularPairQuotientReflection_fixed_iff_core_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion q.val q.property).mpr hf

/-- The same actual disc-core reflection has exactly the Cayley projections
of the same clipped original mirrors as fixed points, under the torsion input. -/
theorem annularPairDiscCoreReflection_fixed_iff_mirror_projection_of_torsion
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (q : Cd) :
    annularPairDiscCoreReflection E r x hE hr hin hout q = q ↔
      ∃ i : Fin 3, ∃ z ∈ K ∩ (S i).carrier,
        mobiusDomainProjection (P).cayleyData.domain ((P).cayleyCoordinate z) = q.val := by
  let H : C ≃ₜ Cd := annularPairCayleyCoreHomeomorph E r x hE hr hin hout
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  let Rn : C ≃ₜ C := annularPairCoreReflection E r x hE hr hin hout
  let Rd : Cd ≃ₜ Cd := annularPairDiscCoreReflection E r x hE hr hin hout
  have hconj : Rd = H.symm.trans (Rn.trans H) :=
    annularPairDiscCoreReflection_eq_conjugate E r x hE hr hin hout
  have hfix : Rd q = q ↔ Rn (H.symm q) = H.symm q := by
    rw [hconj]
    change H (Rn (H.symm q)) = q ↔ Rn (H.symm q) = H.symm q
    constructor
    · intro hf
      have hh := congrArg H.symm hf
      simpa only [H.symm_apply_apply] using hh
    · intro hf
      exact (congrArg H hf).trans (H.apply_symm_apply q)
  have hΦq : Φ ((H.symm q).val) = q.val := by
    exact congrArg Subtype.val (H.apply_symm_apply q)
  change Rd q = q ↔ _
  constructor
  · intro hf
    obtain ⟨i, z, hz, hp⟩ :=
      (annularPairCoreReflection_fixed_iff_mirror_projection_of_torsion
        E r x hE hr hin hout hTorsion (H.symm q)).mp (hfix.mp hf)
    refine ⟨i, z, hz, ?_⟩
    calc
      mobiusDomainProjection (P).cayleyData.domain ((P).cayleyCoordinate z) = Φ (π z) :=
        (annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z).symm
      _ = Φ ((H.symm q).val) := congrArg Φ hp
      _ = q.val := hΦq
  · rintro ⟨i, z, hz, hp⟩
    apply hfix.mpr
    apply (annularPairCoreReflection_fixed_iff_mirror_projection_of_torsion
      E r x hE hr hin hout hTorsion (H.symm q)).mpr
    refine ⟨i, z, hz, ?_⟩
    apply Φ.injective
    calc
      Φ (π z) = mobiusDomainProjection (P).cayleyData.domain ((P).cayleyCoordinate z) :=
        annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z
      _ = q.val := hp
      _ = Φ ((H.symm q).val) := hΦq.symm

end LowDimensionalTopology.Geometry.Hyperbolic
