/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedGeodesicRays
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.LocalConvexity

/-!
# Actual closed hyperbolic-plane models
-/

@[expose] public section
open Set
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem ClosedDiscHConvex.isPreconnected {S : Set 𝕔𝔻} (hS : ClosedDiscHConvex S) :
    IsPreconnected S :=
  (isPreconnected_closedKlein_image_iff S).mp
    ((closedDiscHConvex_iff_klein_convex S).mp hS).isPreconnected

theorem ClosedDiscHConvex.isLocallyClosedDiscHConvex {S : Set 𝕔𝔻} (hS : ClosedDiscHConvex S) :
    IsLocallyClosedDiscHConvex S := by
  intro p hp
  exact ⟨univ,isOpen_univ,mem_univ p,by simpa only [inter_univ] using hS⟩

/-- The source local condition is precisely the genuine ambient Euclidean one in
actual compact Klein coordinates, including neighborhoods of ideal endpoints. -/
theorem locallyClosedDiscHConvex_iff_klein_IsLocallyConvexSet (S : Set 𝕔𝔻) :
    IsLocallyClosedDiscHConvex S ↔ Auxiliary.Analysis.IsLocallyConvexSet (closedKleinCoordinate '' S) :=
  locallyClosedDiscHConvex_iff_klein_local S

/--
on the actual closed disc. No compactness or uniform radius
is imposed on the set; its closedness is in the genuine closed-model topology.
-/
theorem closedDiscHConvex_of_isClosed_isPreconnected_isLocallyConvex {S : Set 𝕔𝔻}
    (hclosed : IsClosed S) (hconn : IsPreconnected S) (hlocal : IsLocallyClosedDiscHConvex S) :
    ClosedDiscHConvex S := by
  apply (closedDiscHConvex_iff_klein_convex S).mpr
  exact Auxiliary.Analysis.convex_of_isClosed_isPreconnected_isLocallyConvex
    ((isClosed_closedKlein_image_iff S).mpr hclosed)
    ((isPreconnected_closedKlein_image_iff S).mpr hconn)
    ((locallyClosedDiscHConvex_iff_klein_IsLocallyConvexSet S).mp hlocal)

theorem closedDiscHConvex_iff_isPreconnected_isLocallyConvex_of_isClosed {S : Set 𝕔𝔻}
    (hclosed : IsClosed S) :
    ClosedDiscHConvex S ↔ IsPreconnected S ∧ IsLocallyClosedDiscHConvex S :=
  ⟨fun hS => ⟨hS.isPreconnected,hS.isLocallyClosedDiscHConvex⟩,
    fun hS => closedDiscHConvex_of_isClosed_isPreconnected_isLocallyConvex hclosed hS.1 hS.2⟩

/-- Compactified H segments are the actual compactified disc arcs transported by
the genuine extended Cayley homeomorphism, including the true infinite point. -/
def closedModelHSegment (p q : ClosedHalfPlaneModel) : Set ClosedHalfPlaneModel :=
  closedModelCayleyHomeomorph ⁻¹' closedModelDiscHSegment
    (closedModelCayleyHomeomorph p) (closedModelCayleyHomeomorph q)

theorem cayley_image_closedModelHSegment (p q : ClosedHalfPlaneModel) :
    closedModelCayleyHomeomorph '' closedModelHSegment p q =
      closedModelDiscHSegment (closedModelCayleyHomeomorph p) (closedModelCayleyHomeomorph q) :=
  closedModelCayleyHomeomorph.surjective.image_preimage _

/-- Actual closed H convexity, using its actual finite and ideal hyperbolic arcs. -/
def ClosedHalfPlaneHConvex (S : Set ClosedHalfPlaneModel) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, closedModelHSegment p q ⊆ S

theorem closedHalfPlaneHConvex_iff_cayley (S : Set ClosedHalfPlaneModel) :
    ClosedHalfPlaneHConvex S ↔ ClosedDiscHConvex (closedModelCayleyHomeomorph '' S) := by
  constructor
  · intro hS p hp q hq
    obtain ⟨x,hx,rfl⟩ := hp
    obtain ⟨y,hy,rfl⟩ := hq
    rw [← cayley_image_closedModelHSegment]
    exact image_mono (hS x hx y hy)
  · intro hS p hp q hq x hx
    obtain ⟨y,hy,he⟩ := hS _ (mem_image_of_mem _ hp) _ (mem_image_of_mem _ hq) hx
    exact closedModelCayleyHomeomorph.injective he ▸ hy

/-- Local convexity uses actual relative open neighborhoods in the genuine H compactification. -/
def IsLocallyClosedHalfPlaneHConvex (S : Set ClosedHalfPlaneModel) : Prop :=
  ∀ p ∈ S, ∃ U : Set ClosedHalfPlaneModel,
    IsOpen U ∧ p ∈ U ∧ ClosedHalfPlaneHConvex (S ∩ U)

theorem locallyClosedHalfPlaneHConvex_iff_cayley (S : Set ClosedHalfPlaneModel) :
    IsLocallyClosedHalfPlaneHConvex S ↔
      IsLocallyClosedDiscHConvex (closedModelCayleyHomeomorph '' S) := by
  constructor
  · intro hS p hp
    obtain ⟨x,hx,rfl⟩ := hp
    obtain ⟨U,hU,hxU,hconv⟩ := hS x hx
    refine ⟨closedModelCayleyHomeomorph '' U,closedModelCayleyHomeomorph.isOpenMap U hU,
      mem_image_of_mem _ hxU,?_⟩
    have hc := (closedHalfPlaneHConvex_iff_cayley (S ∩ U)).mp hconv
    rw [image_inter closedModelCayleyHomeomorph.injective] at hc
    exact hc
  · intro hS p hp
    obtain ⟨V,hV,hpV,hconv⟩ := hS _ (mem_image_of_mem _ hp)
    refine ⟨closedModelCayleyHomeomorph ⁻¹' V,
      hV.preimage closedModelCayleyHomeomorph.continuous,hpV,?_⟩
    apply (closedHalfPlaneHConvex_iff_cayley _).mpr
    rw [image_inter_preimage]
    exact hconv

theorem ClosedHalfPlaneHConvex.isPreconnected {S : Set ClosedHalfPlaneModel}
    (hS : ClosedHalfPlaneHConvex S) : IsPreconnected S :=
  closedModelCayleyHomeomorph.isPreconnected_image.mp
    ((closedHalfPlaneHConvex_iff_cayley S).mp hS).isPreconnected

theorem ClosedHalfPlaneHConvex.isLocallyClosedHalfPlaneHConvex {S : Set ClosedHalfPlaneModel}
    (hS : ClosedHalfPlaneHConvex S) : IsLocallyClosedHalfPlaneHConvex S := by
  intro p hp
  exact ⟨univ,isOpen_univ,mem_univ p,by simpa only [inter_univ] using hS⟩

/-- on the genuine closed H model, with its true infinite ideal point. -/
theorem closedHalfPlaneHConvex_of_isClosed_isPreconnected_isLocallyConvex
    {S : Set ClosedHalfPlaneModel} (hclosed : IsClosed S) (hconn : IsPreconnected S)
    (hlocal : IsLocallyClosedHalfPlaneHConvex S) : ClosedHalfPlaneHConvex S := by
  apply (closedHalfPlaneHConvex_iff_cayley S).mpr
  exact closedDiscHConvex_of_isClosed_isPreconnected_isLocallyConvex
    (closedModelCayleyHomeomorph.isClosedMap _ hclosed)
    (closedModelCayleyHomeomorph.isPreconnected_image.mpr hconn)
    ((locallyClosedHalfPlaneHConvex_iff_cayley S).mp hlocal)

theorem closedHalfPlaneHConvex_iff_isPreconnected_isLocallyConvex_of_isClosed
    {S : Set ClosedHalfPlaneModel} (hclosed : IsClosed S) :
    ClosedHalfPlaneHConvex S ↔ IsPreconnected S ∧ IsLocallyClosedHalfPlaneHConvex S :=
  ⟨fun hS => ⟨hS.isPreconnected,hS.isLocallyClosedHalfPlaneHConvex⟩,
    fun hS => closedHalfPlaneHConvex_of_isClosed_isPreconnected_isLocallyConvex hclosed hS.1 hS.2⟩

theorem closedModelHSegment_self (p : ClosedHalfPlaneModel) : closedModelHSegment p p = {p} := by
  rw [closedModelHSegment,closedModelDiscHSegment_self]
  ext x
  exact closedModelCayleyHomeomorph.injective.eq_iff

theorem closedModelHSegment_interior (z w : ℍ) :
    closedModelHSegment (halfPlaneToClosedModel z) (halfPlaneToClosedModel w) =
      halfPlaneToClosedModel '' closedHSegment z w := by
  apply closedModelCayleyHomeomorph.injective.image_injective
  rw [cayley_image_closedModelHSegment,closedModelCayley_on_interior,
    closedModelCayley_on_interior,closedModelDiscHSegment_interior,
    closedDiscHSegment_eq_cayley_image,discToHalfPlane_halfPlaneToDisc,
    discToHalfPlane_halfPlaneToDisc,image_image,image_image]
  apply Set.image_congr
  intro u _
  exact (closedModelCayley_on_interior u).symm

/-- The actual closed H segment with one ideal endpoint is the closure of the
already formalized genuine isometric H ray, including an ideal endpoint at infinity. -/
theorem closedModelHSegment_ray (z : ℍ) (p : ClosedHalfPlaneModel)
    (hp : p.1 ∈ halfPlaneIdealBoundary) :
    closedModelHSegment (halfPlaneToClosedModel z) p =
      closure (halfPlaneToClosedModel '' hRay z p.1) :=
  cayley_pullback_closed_segment_ray z p hp

/-- The actual H segment between its two ideal ends is the genuine complete h-line closure. -/
theorem closedModelHSegment_ideal_endpoints (L : HalfPlaneLine)
    (p q : ClosedHalfPlaneModel) (hp : p.1 ∈ halfPlaneIdealBoundary)
    (hq : q.1 ∈ halfPlaneIdealBoundary) (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier) :
    closedModelHSegment p q = L.closedCarrier :=
  cayley_pullback_closed_segment_ideal_endpoints L p q hp hq hpq hpL hqL

end
end LowDimensionalTopology.Geometry.Hyperbolic
