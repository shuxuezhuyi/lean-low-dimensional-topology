module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCarrier
public import Mathlib.Topology.Homeomorph.Quotient

/-! The faithful annular native group and its actual Cayley disc group have
homeomorphic original orbit quotients. The exact projection square identifies
the literal native core image with the existing three-boundary open core. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Surfaces

/-- The unchanged native pair-product group is faithfully identified with
the unchanged whole Cayley disc group. -/
def annularPairCayleyGroupEquiv (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    annularPairReflectionGroup E r x hE hr ≃*
      annularPairReflectionDiscGroup E r x hE hr := by
  let G := annularPairReflectionGroup E r x hE hr
  let hG := annularPairReflectionGroup_le_conformal E r x hE hr
  let F := nativeConformalSubgroupMobiusHom G hG
  exact (MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry G hG).injective).trans
    (subgroupConjugateEquivalence cayleyMobius F.range)

/-- The faithful group identification intertwines the actual native action
with the actual Cayley coordinate and the original disc-domain action. -/
theorem annularPairCayleyGroupEquiv_action
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E)
    (g : annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) (z : ℍ) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    letI : MulAction (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr)
        P.cayleyData.domain.carrier := mobiusDomainAction P.cayleyData.domain
    P.cayleyCoordinate (g • z) =
      annularPairCayleyGroupEquiv E r x (zero_lt_one.trans hE) hr g • P.cayleyCoordinate z := by
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let hG := annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr
  let F := nativeConformalSubgroupMobiusHom G hG
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let : MulAction (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr)
        P.cayleyData.domain.carrier := mobiusDomainAction P.cayleyData.domain
  let e₀ : G ≃* F.range :=
    MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry G hG).injective
  let := P.nativeAction
  have hphysical : e₀ g • z = g • z := by
    apply Mobius.halfPlaneBoundaryPoint_injective
    have he := P.nativeAction_boundary (e₀ g) z
    change (F g).val (Mobius.halfPlaneBoundaryPoint z) =
      Mobius.halfPlaneBoundaryPoint (e₀ g • z) at he
    exact he.symm.trans (nativeConformalSubgroupMobiusHom_action G hG g z)
  have hc := P.cayleyCoordinate_equivariant (e₀ g) z
  rw [hphysical] at hc
  exact hc

/-- The actual native annular orbit quotient is homeomorphic to the original
disc-domain quotient by the same full Cayley group. -/
def annularPairCayleyOrbitHomeomorph
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    orbitQuotient (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ ≃ₜ
      MobiusDomainQuotient P.cayleyData.domain := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  letI : MulAction (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr)
        P.cayleyData.domain.carrier := mobiusDomainAction P.cayleyData.domain
  let e := annularPairCayleyGroupEquiv E r x (zero_lt_one.trans hE) hr
  have hact (g : annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) (z : ℍ) :
      P.cayleyCoordinate (g • z) = e g • P.cayleyCoordinate z :=
    annularPairCayleyGroupEquiv_action E r x hE hr hin hout g z
  exact Homeomorph.Quotient.congr P.cayleyCoordinate (by
    intro u v
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e g, ?_⟩
      exact (hact g v).symm.trans (congrArg P.cayleyCoordinate hg)
    · rintro ⟨g, hg⟩
      let g' : annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr := g
      refine ⟨e.symm g', ?_⟩
      apply P.cayleyCoordinate.injective
      calc
        P.cayleyCoordinate (e.symm g' • v) =
            e (e.symm g') • P.cayleyCoordinate v := hact (e.symm g') v
        _ = g' • P.cayleyCoordinate v :=
          congrArg (fun f => f • P.cayleyCoordinate v) (e.apply_symm_apply g')
        _ = P.cayleyCoordinate u := hg)

@[simp]
theorem annularPairCayleyOrbitHomeomorph_projection
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) (z : ℍ) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
        (orbitProjection (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ z) =
      mobiusDomainProjection P.cayleyData.domain (P.cayleyCoordinate z) := rfl

/-- The homeomorphism sends the literal native image of the original Nielsen
lift onto the existing threeBoundaryOpenCore of that same actual disc model. -/
theorem annularPairCayleyOrbitHomeomorph_coreImage
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    annularPairCayleyOrbitHomeomorph E r x hE hr hin hout ''
        (orbitProjection G ℍ ''
          (P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE)) =
      threeBoundaryOpenCore P.cayleyData hNE := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let N := fuchsianNielsenCore P.cayleyData hNE
  let K := P.cayleyCoordinate ⁻¹' N
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  change Φ '' (orbitProjection G ℍ '' K) = mobiusDomainProjection P.cayleyData.domain '' N
  apply subset_antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨P.cayleyCoordinate z, hz, ?_⟩
    exact (annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z).symm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, hz⟩ := P.cayleyCoordinate.surjective v
    refine ⟨orbitProjection G ℍ z, ⟨z, ?_, rfl⟩, ?_⟩
    · change P.cayleyCoordinate z ∈ N
      rw [hz]
      exact hv
    · calc
        Φ (orbitProjection G ℍ z) =
            mobiusDomainProjection P.cayleyData.domain (P.cayleyCoordinate z) :=
          annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z
        _ = mobiusDomainProjection P.cayleyData.domain v :=
          congrArg (mobiusDomainProjection P.cayleyData.domain) hz

end LowDimensionalTopology.Geometry.Hyperbolic
