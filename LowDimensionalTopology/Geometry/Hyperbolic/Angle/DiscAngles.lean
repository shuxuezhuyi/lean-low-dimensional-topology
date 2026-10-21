/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.AngleDomains

/-!
# Actual native disc ray angles
-/

@[expose] public section
open Set
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A native disc ray is its genuine point set with an actual isometric half-line
witness and true ideal accumulation endpoint. -/
def DiscRayAt (z : 𝔻) := {R : Set 𝔻 // ∃ a : OnePoint ℂ,
  a ∈ extendedDiscIdealBoundary ∧ IsDiscHLineRay z a R}

def DiscRayAt.idealEndpoint {z : 𝔻} (R : DiscRayAt z) : OnePoint ℂ := R.property.choose

theorem DiscRayAt.idealEndpoint_mem {z : 𝔻} (R : DiscRayAt z) :
    R.idealEndpoint ∈ extendedDiscIdealBoundary := R.property.choose_spec.1

theorem DiscRayAt.isRay {z : 𝔻} (R : DiscRayAt z) : IsDiscHLineRay z R.idealEndpoint R.val :=
  R.property.choose_spec.2

/-- The actual inverse Cayley image is a genuine H ray. -/
def DiscRayAt.toHalfPlane {z : 𝔻} (R : DiscRayAt z) : HRayAt (discToHalfPlane z) := by
  refine ⟨discToHalfPlane '' R.val,extendedCayley.symm R.idealEndpoint,?_,R.isRay.toHalfPlane⟩
  exact (idealBoundary_cayley_iff _).mpr
    (by simpa only [extendedCayley.apply_symm_apply] using R.idealEndpoint_mem)

def HRayAt.toDiscAt (z : 𝔻) (R : HRayAt (discToHalfPlane z)) : DiscRayAt z := by
  refine ⟨halfPlaneToDisc '' R.val,extendedCayley R.idealEndpoint,
    (idealBoundary_cayley_iff _).mp R.idealEndpoint_mem,?_⟩
  have hr := R.isRay.toDisc
  simpa only [halfPlaneToDisc_discToHalfPlane] using hr

/-- This is a proved equivalence of genuine geometric point-set rays. -/
def discRayHalfPlaneEquiv (z : 𝔻) : DiscRayAt z ≃ HRayAt (discToHalfPlane z) where
  toFun := DiscRayAt.toHalfPlane
  invFun := HRayAt.toDiscAt z
  left_inv R := Subtype.ext (cayley_image_inverse_image R.val)
  right_inv R := Subtype.ext (inverse_cayley_image_image R.val)

theorem DiscRayAt.carrier_eq_cayley {z : 𝔻} (R : DiscRayAt z) :
    R.val = halfPlaneToDisc '' R.toHalfPlane.val := (cayley_image_inverse_image R.val).symm

def DiscRayAt.supportLine {z : 𝔻} (R : DiscRayAt z) : DiscLine := R.toHalfPlane.supportLine.toDiscLine

theorem DiscRayAt.support_carrier_eq_cayley {z : 𝔻} (R : DiscRayAt z) :
    R.supportLine.carrier = halfPlaneToDisc '' R.toHalfPlane.supportLine.carrier := by
  rw [DiscRayAt.supportLine,HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image]

theorem DiscRayAt.subset_support {z : 𝔻} (R : DiscRayAt z) : R.val ⊆ R.supportLine.carrier := by
  rw [R.carrier_eq_cayley,R.support_carrier_eq_cayley]
  exact image_mono R.toHalfPlane.subset_support

theorem DiscRayAt.start_mem {z : 𝔻} (R : DiscRayAt z) : z ∈ R.val := by
  rw [R.carrier_eq_cayley]
  exact ⟨discToHalfPlane z,R.toHalfPlane.start_mem,halfPlaneToDisc_discToHalfPlane z⟩

theorem HalfPlaneLine.toDiscLine_injective : Function.Injective HalfPlaneLine.toDiscLine := by
  intro L M he
  apply HalfPlaneLine.carrier_injective
  apply (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective).image_injective
  rw [← L.discCarrier_eq_cayley_image,← M.discCarrier_eq_cayley_image]
  change L.toDiscLine.carrier = M.toDiscLine.carrier
  exact congrArg DiscLine.carrier he

theorem DiscRayAt.support_eq_iff {z : 𝔻} (R S : DiscRayAt z) :
    R.supportLine = S.supportLine ↔ R.toHalfPlane.supportLine = S.toHalfPlane.supportLine :=
  HalfPlaneLine.toDiscLine_injective.eq_iff

/-- The native side is transported by the actual Cayley homeomorphism; the next
theorem identifies it with a genuine native complement component. -/
def discAngleSide {z : 𝔻} (R S : DiscRayAt z) : Set 𝔻 :=
  halfPlaneToDisc '' hAngleSide R.toHalfPlane S.toHalfPlane

theorem discAngleSide_eq_component {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {w : 𝔻} (hw : w ∈ S.val \ {z}) :
    discAngleSide R S = openDiscHalfPlane R.supportLine w := by
  have hH : R.toHalfPlane.supportLine ≠ S.toHalfPlane.supportLine :=
    fun he => hne ((R.support_eq_iff S).mpr he)
  have hwH : discToHalfPlane w ∈ S.toHalfPlane.val \ {discToHalfPlane z} := by
    refine ⟨⟨w,hw.1,rfl⟩,?_⟩
    exact discToHalfPlane_injective.ne hw.2
  rw [discAngleSide,hAngleSide_eq_component R.toHalfPlane S.toHalfPlane hH hwH,
    cayley_image_openHHalfPlane _ _
      (R.toHalfPlane.punctured_subset_compl_support S.toHalfPlane hH hwH),
    halfPlaneToDisc_discToHalfPlane]
  rfl

def properDiscAngleInterior {z : 𝔻} (R S : DiscRayAt z) : Set 𝔻 :=
  halfPlaneToDisc '' properHAngleInterior R.toHalfPlane S.toHalfPlane

def properDiscAngleExterior {z : 𝔻} (R S : DiscRayAt z) : Set 𝔻 :=
  halfPlaneToDisc '' properHAngleExterior R.toHalfPlane S.toHalfPlane

theorem properDiscAngleInterior_eq_sides {z : 𝔻} (R S : DiscRayAt z) :
    properDiscAngleInterior R S = discAngleSide R S ∩ discAngleSide S R := by
  exact image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)

theorem properDiscAngleExterior_eq_complement {z : 𝔻} (R S : DiscRayAt z) :
    properDiscAngleExterior R S = (R.val ∪ S.val)ᶜ \ properDiscAngleInterior R S := by
  change halfPlaneToDisc '' ((R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ \
    properHAngleInterior R.toHalfPlane S.toHalfPlane) = _
  rw [image_sdiff (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_compl_eq (show Function.Bijective halfPlaneToDisc from cayleyHomeomorph.bijective),
    image_union,← R.carrier_eq_cayley,← S.carrier_eq_cayley]
  rfl

/-- Native disc angles are literally unordered pairs of genuine native ray point sets. -/
abbrev DiscAngle (z : 𝔻) := Sym2 (DiscRayAt z)

def discAngleInteriorPair {z : 𝔻} (R S : DiscRayAt z) : Option (Set 𝔻) :=
  (hAngleInteriorPair R.toHalfPlane S.toHalfPlane).map (fun U => halfPlaneToDisc '' U)

def discAngleExteriorPair {z : 𝔻} (R S : DiscRayAt z) : Option (Set 𝔻) :=
  (hAngleExteriorPair R.toHalfPlane S.toHalfPlane).map (fun U => halfPlaneToDisc '' U)

theorem discAngleInteriorPair_comm {z : 𝔻} (R S : DiscRayAt z) :
    discAngleInteriorPair R S = discAngleInteriorPair S R := by
  rw [discAngleInteriorPair,discAngleInteriorPair,hAngleInteriorPair_comm]

theorem discAngleExteriorPair_comm {z : 𝔻} (R S : DiscRayAt z) :
    discAngleExteriorPair R S = discAngleExteriorPair S R := by
  rw [discAngleExteriorPair,discAngleExteriorPair,hAngleExteriorPair_comm]

def DiscAngle.interior {z : 𝔻} (A : DiscAngle z) : Option (Set 𝔻) :=
  Sym2.lift ⟨discAngleInteriorPair,discAngleInteriorPair_comm⟩ A

def DiscAngle.exterior {z : 𝔻} (A : DiscAngle z) : Option (Set 𝔻) :=
  Sym2.lift ⟨discAngleExteriorPair,discAngleExteriorPair_comm⟩ A

theorem DiscAngle.interior_pair {z : 𝔻} (R S : DiscRayAt z) :
    DiscAngle.interior s(R,S) = discAngleInteriorPair R S := rfl

theorem DiscAngle.exterior_pair {z : 𝔻} (R S : DiscRayAt z) :
    DiscAngle.exterior s(R,S) = discAngleExteriorPair R S := rfl

theorem discAngleInteriorPair_self {z : 𝔻} (R : DiscRayAt z) :
    discAngleInteriorPair R R = some ∅ := by
  simp only [discAngleInteriorPair,hAngleInteriorPair_self,Option.map_some,image_empty]

theorem discAngleExteriorPair_self {z : 𝔻} (R : DiscRayAt z) :
    discAngleExteriorPair R R = some R.valᶜ := by
  rw [discAngleExteriorPair,hAngleExteriorPair_self,Option.map_some,
    image_compl_eq (show Function.Bijective halfPlaneToDisc from cayleyHomeomorph.bijective),
    ← R.carrier_eq_cayley]

theorem discAngleInteriorPair_opposite {z : 𝔻} (R S : DiscRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : discAngleInteriorPair R S = none := by
  have hRS' : R.toHalfPlane ≠ S.toHalfPlane := (discRayHalfPlaneEquiv z).injective.ne hRS
  rw [discAngleInteriorPair,hAngleInteriorPair_opposite R.toHalfPlane S.toHalfPlane
    ((R.support_eq_iff S).mp hL) hRS',Option.map_none]

theorem discAngleExteriorPair_opposite {z : 𝔻} (R S : DiscRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : discAngleExteriorPair R S = none := by
  have hRS' : R.toHalfPlane ≠ S.toHalfPlane := (discRayHalfPlaneEquiv z).injective.ne hRS
  rw [discAngleExteriorPair,hAngleExteriorPair_opposite R.toHalfPlane S.toHalfPlane
    ((R.support_eq_iff S).mp hL) hRS',Option.map_none]

theorem discAngleInteriorPair_proper {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    discAngleInteriorPair R S = some (properDiscAngleInterior R S) := by
  have hH : R.toHalfPlane.supportLine ≠ S.toHalfPlane.supportLine :=
    fun he => hne ((R.support_eq_iff S).mpr he)
  rw [discAngleInteriorPair,hAngleInteriorPair_proper R.toHalfPlane S.toHalfPlane hH,Option.map_some]
  rfl

theorem discAngleExteriorPair_proper {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    discAngleExteriorPair R S = some (properDiscAngleExterior R S) := by
  have hH : R.toHalfPlane.supportLine ≠ S.toHalfPlane.supportLine :=
    fun he => hne ((R.support_eq_iff S).mpr he)
  rw [discAngleExteriorPair,hAngleExteriorPair_proper R.toHalfPlane S.toHalfPlane hH,Option.map_some]
  rfl

theorem DiscRayAt.different_supports_iff {z : 𝔻} (R S : DiscRayAt z) :
    R.supportLine ≠ S.supportLine ↔ R.toHalfPlane.supportLine ≠ S.toHalfPlane.supportLine :=
  not_congr (R.support_eq_iff S)

theorem DiscRayAt.union_eq_support_of_same_support {z : 𝔻} (R S : DiscRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) :
    R.val ∪ S.val = R.supportLine.carrier := by
  rw [R.carrier_eq_cayley,S.carrier_eq_cayley,← image_union,
    HRayAt.union_eq_support_of_same_support R.toHalfPlane S.toHalfPlane
      ((R.support_eq_iff S).mp hL) ((discRayHalfPlaneEquiv z).injective.ne hRS),
    ← R.support_carrier_eq_cayley]

theorem properDiscAngleInterior_hConvex {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : DiscHConvex (properDiscAngleInterior R S) :=
  (hConvex_iff_cayley_discHConvex _).mp
    (properHAngleInterior_hConvex R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne))

theorem properDiscAngleInterior_nonempty {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : (properDiscAngleInterior R S).Nonempty :=
  (properHAngleInterior_nonempty R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne)).image halfPlaneToDisc

theorem properDiscAngleExterior_nonempty {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : (properDiscAngleExterior R S).Nonempty :=
  (properHAngleExterior_nonempty R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne)).image halfPlaneToDisc

theorem properDiscAngleInterior_isOpen {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (properDiscAngleInterior R S) :=
  cayleyHomeomorph.isOpenMap _
    (properHAngleInterior_isOpen R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne))

theorem properDiscAngleExterior_isOpen {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (properDiscAngleExterior R S) :=
  cayleyHomeomorph.isOpenMap _
    (properHAngleExterior_isOpen R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne))

theorem properDiscAngleExterior_isPreconnected {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsPreconnected (properDiscAngleExterior R S) :=
  (properHAngleExterior_isPreconnected R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne)).image halfPlaneToDisc cayleyHomeomorph.continuous.continuousOn

theorem properDiscAngleExterior_not_hConvex {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : ¬ DiscHConvex (properDiscAngleExterior R S) := by
  intro hc
  have he := (hConvex_iff_cayley_discHConvex
    (properHAngleExterior R.toHalfPlane S.toHalfPlane)).mpr hc
  exact properHAngleExterior_not_hConvex R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne) he

theorem cayley_image_angle_rayComplement {z : 𝔻} (R S : DiscRayAt z) :
    halfPlaneToDisc '' (R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ = (R.val ∪ S.val)ᶜ := by
  rw [image_compl_eq (show Function.Bijective halfPlaneToDisc from cayleyHomeomorph.bijective),
    image_union,← R.carrier_eq_cayley,← S.carrier_eq_cayley]

/-- The native proper interior is exactly one actual native complement component. -/
theorem connectedComponentIn_properDiscAngleInterior {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : 𝔻} (hx : x ∈ properDiscAngleInterior R S) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properDiscAngleInterior R S := by
  obtain ⟨u,hu,rfl⟩ := hx
  have he := cayleyHomeomorph.image_connectedComponentIn
    (properHAngleInterior_subset_compl_union R.toHalfPlane S.toHalfPlane hu)
  change halfPlaneToDisc '' connectedComponentIn (R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ u =
    connectedComponentIn (halfPlaneToDisc '' (R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ) (halfPlaneToDisc u) at he
  rw [connectedComponentIn_properHAngleInterior R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne) hu,cayley_image_angle_rayComplement] at he
  exact he.symm

/-- The native proper exterior is the other actual native component. -/
theorem connectedComponentIn_properDiscAngleExterior {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : 𝔻} (hx : x ∈ properDiscAngleExterior R S) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properDiscAngleExterior R S := by
  obtain ⟨u,hu,rfl⟩ := hx
  have he := cayleyHomeomorph.image_connectedComponentIn hu.1
  change halfPlaneToDisc '' connectedComponentIn (R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ u =
    connectedComponentIn (halfPlaneToDisc '' (R.toHalfPlane.val ∪ S.toHalfPlane.val)ᶜ) (halfPlaneToDisc u) at he
  rw [connectedComponentIn_properHAngleExterior R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne) hu,cayley_image_angle_rayComplement] at he
  exact he.symm

theorem properDiscAngle_interior_exterior_partition {z : 𝔻} (R S : DiscRayAt z) :
    (R.val ∪ S.val)ᶜ = properDiscAngleInterior R S ∪ properDiscAngleExterior R S := by
  have he := congrArg (fun T : Set ℍ => halfPlaneToDisc '' T)
    (properHAngle_interior_exterior_partition R.toHalfPlane S.toHalfPlane)
  rw [image_union,cayley_image_angle_rayComplement] at he
  exact he

theorem properDiscAngle_interior_exterior_disjoint {z : 𝔻} (R S : DiscRayAt z) :
    Disjoint (properDiscAngleInterior R S) (properDiscAngleExterior R S) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rw [properDiscAngleExterior_eq_complement] at hy
  exact hy.2 hx

theorem properDiscAngle_component_classification {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : 𝔻} (hx : x ∈ (R.val ∪ S.val)ᶜ) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properDiscAngleInterior R S ∨
      connectedComponentIn (R.val ∪ S.val)ᶜ x = properDiscAngleExterior R S := by
  by_cases hxI : x ∈ properDiscAngleInterior R S
  · exact Or.inl (connectedComponentIn_properDiscAngleInterior R S hne hxI)
  · have hxE : x ∈ properDiscAngleExterior R S := by
      rw [properDiscAngleExterior_eq_complement]
      exact ⟨hx,hxI⟩
    exact Or.inr (connectedComponentIn_properDiscAngleExterior R S hne hxE)

theorem discAngleInteriorPair_some_hConvex {z : 𝔻} (R S : DiscRayAt z) {U : Set 𝔻}
    (hU : discAngleInteriorPair R S = some U) : DiscHConvex U := by
  cases hH : hAngleInteriorPair R.toHalfPlane S.toHalfPlane with
  | none => simp only [discAngleInteriorPair,hH,Option.map_none] at hU; cases hU
  | some V =>
    rw [discAngleInteriorPair,hH,Option.map_some,Option.some.injEq] at hU
    rw [← hU]
    exact (hConvex_iff_cayley_discHConvex V).mp
      (hAngleInteriorPair_some_hConvex R.toHalfPlane S.toHalfPlane hH)

theorem DiscAngle.interior_hConvex {z : 𝔻} (A : DiscAngle z) {U : Set 𝔻}
    (hU : A.interior = some U) : DiscHConvex U := by
  induction A using Sym2.inductionOn with
  | hf R S => exact discAngleInteriorPair_some_hConvex R S hU

end
end LowDimensionalTopology.Geometry.Hyperbolic
