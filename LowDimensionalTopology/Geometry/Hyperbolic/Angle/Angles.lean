/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedLocalConvexity
public import Mathlib.Data.Sym.Sym2

/-!
# Genuine unordered ray angles and actual half-plane interiors
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A genuine geometric ray, represented by its actual point set with a proved
isometric half-line witness and an actual ideal endpoint. -/
def HRayAt (z : ℍ) := {R : Set ℍ // ∃ a : OnePoint ℂ,
  a ∈ halfPlaneIdealBoundary ∧ IsHLineRay z a R}

/-- The actual ideal end is unique; the choice here introduces no additional data. -/
def HRayAt.idealEndpoint {z : ℍ} (R : HRayAt z) : OnePoint ℂ := R.property.choose

theorem HRayAt.idealEndpoint_mem {z : ℍ} (R : HRayAt z) :
    R.idealEndpoint ∈ halfPlaneIdealBoundary := R.property.choose_spec.1

theorem HRayAt.isRay {z : ℍ} (R : HRayAt z) : IsHLineRay z R.idealEndpoint R.val :=
  R.property.choose_spec.2

theorem HRayAt.trace_idealEndpoint {z : ℍ} (R : HRayAt z) :
    hTraceIdealEndpoints R.val = {R.idealEndpoint} := R.isRay.idealEndpoints_eq

theorem HRayAt.eq_canonical {z : ℍ} (R : HRayAt z) :
    R.val = hRay z R.idealEndpoint := (hRay_eq_of_isHLineRay R.isRay).symm

def HRayAt.canonical (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) : HRayAt z :=
  ⟨hRay z a,a,ha,isHLineRay_hRay z a ha⟩

theorem HRayAt.idealEndpoint_unique {z : ℍ} (R : HRayAt z) {a : OnePoint ℂ}
    (ha : IsHLineRay z a R.val) : R.idealEndpoint = a :=
  Set.singleton_injective (R.trace_idealEndpoint.symm.trans ha.idealEndpoints_eq)

theorem HRayAt.idealEndpoint_injective (z : ℍ) : Function.Injective (HRayAt.idealEndpoint (z := z)) := by
  intro R S he
  apply Subtype.ext
  rw [R.eq_canonical,S.eq_canonical,he]

theorem HRayAt.start_mem {z : ℍ} (R : HRayAt z) : z ∈ R.val := R.isRay.start_mem

/-- The actual unique complete h-line containing the ray. -/
def HRayAt.supportLine {z : ℍ} (R : HRayAt z) : HalfPlaneLine :=
  (existsUnique_halfPlaneLine_through_point_and_idealEndpoint z R.idealEndpoint
    R.idealEndpoint_mem).exists.choose

theorem HRayAt.start_mem_support {z : ℍ} (R : HRayAt z) : z ∈ R.supportLine.carrier :=
  (existsUnique_halfPlaneLine_through_point_and_idealEndpoint z R.idealEndpoint
    R.idealEndpoint_mem).exists.choose_spec.1

theorem HRayAt.ideal_mem_support {z : ℍ} (R : HRayAt z) :
    R.idealEndpoint ∈ R.supportLine.idealEndpoints :=
  (existsUnique_halfPlaneLine_through_point_and_idealEndpoint z R.idealEndpoint
    R.idealEndpoint_mem).exists.choose_spec.2

theorem HRayAt.subset_support {z : ℍ} (R : HRayAt z) : R.val ⊆ R.supportLine.carrier := by
  rw [R.eq_canonical]
  exact hRay_subset_line R.supportLine z R.start_mem_support R.idealEndpoint R.ideal_mem_support

theorem HRayAt.isClosed {z : ℍ} (R : HRayAt z) : IsClosed R.val := by
  rw [R.eq_canonical]
  exact hRay_isClosed z R.idealEndpoint R.idealEndpoint_mem

/-- Removing the finite initial point leaves a nonempty connected genuine open half-line. -/
theorem HRayAt.punctured_nonempty {z : ℍ} (R : HRayAt z) : (R.val \ {z}).Nonempty := by
  obtain ⟨γ,hγ,s,hs,hor,_⟩ := R.isRay
  rcases hor with hor | hor
  · refine ⟨γ (s + 1),?_,?_⟩
    · rw [hor]
      exact ⟨s + 1,by change s ≤ s + 1; linarith,rfl⟩
    · intro he
      have heq := hγ.1.injective (he.trans hs.symm)
      linarith
  · refine ⟨γ (s - 1),?_,?_⟩
    · rw [hor]
      exact ⟨s - 1,by change s - 1 ≤ s; linarith,rfl⟩
    · intro he
      have heq := hγ.1.injective (he.trans hs.symm)
      linarith

theorem HRayAt.punctured_isPreconnected {z : ℍ} (R : HRayAt z) :
    IsPreconnected (R.val \ {z}) := by
  obtain ⟨γ,hγ,s,hs,hor,_⟩ := R.isRay
  rw [show ({z} : Set ℍ) = {γ s} from congrArg Set.singleton hs.symm]
  rcases hor with hor | hor
  · have he : forwardHLineRay γ s \ {γ s} = γ '' Ioi s := by
      ext x
      constructor
      · rintro ⟨⟨r,hr,rfl⟩,hne⟩
        have hrs : r ≠ s := fun h => hne (congrArg γ h)
        exact ⟨r,lt_of_le_of_ne hr (Ne.symm hrs),rfl⟩
      · rintro ⟨r,hr,rfl⟩
        exact ⟨⟨r,hr.le,rfl⟩,fun h => hr.ne' (hγ.1.injective h)⟩
    rw [hor,he]
    exact isPreconnected_Ioi.image γ hγ.1.continuous.continuousOn
  · have he : backwardHLineRay γ s \ {γ s} = γ '' Iio s := by
      ext x
      constructor
      · rintro ⟨⟨r,hr,rfl⟩,hne⟩
        have hrs : r ≠ s := fun h => hne (congrArg γ h)
        exact ⟨r,lt_of_le_of_ne hr hrs,rfl⟩
      · rintro ⟨r,hr,rfl⟩
        exact ⟨⟨r,hr.le,rfl⟩,fun h => hr.ne (hγ.1.injective h)⟩
    rw [hor,he]
    exact isPreconnected_Iio.image γ hγ.1.continuous.continuousOn

/-- A ray on a different support meets the other full h-line only at the common vertex. -/
theorem HRayAt.punctured_subset_compl_support {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : S.val \ {z} ⊆ R.supportLine.carrierᶜ := by
  intro x hx hxR
  have hzx : z ≠ x := Ne.symm hx.2
  exact hne (R.supportLine.eq_of_two_points S.supportLine hzx
    R.start_mem_support hxR S.start_mem_support (S.subset_support hx.1))

/-- Select the actual side of one full line containing the other punctured ray.
The following theorem proves all choices of witness yield the same genuine component. -/
def hAngleSide {z : ℍ} (R S : HRayAt z) : Set ℍ :=
  ⋃ x ∈ S.val \ {z}, openHHalfPlane R.supportLine x

theorem hAngleSide_eq_component {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : ℍ} (hx : x ∈ S.val \ {z}) :
    hAngleSide R S = openHHalfPlane R.supportLine x := by
  have hsub := S.punctured_isPreconnected.subset_connectedComponentIn hx
    (R.punctured_subset_compl_support S hne)
  ext u
  constructor
  · intro hu
    simp only [hAngleSide,mem_iUnion] at hu
    obtain ⟨v,hvS,huv⟩ := hu
    have he := connectedComponentIn_eq (hsub hvS)
    change u ∈ connectedComponentIn R.supportLine.carrierᶜ v at huv
    change u ∈ connectedComponentIn R.supportLine.carrierᶜ x
    rw [he]
    exact huv
  · intro hu
    simp only [hAngleSide,mem_iUnion]
    exact ⟨x,hx,hu⟩

theorem hAngleSide_contains_punctured {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : S.val \ {z} ⊆ hAngleSide R S := by
  intro x hx
  rw [hAngleSide_eq_component R S hne hx]
  exact mem_connectedComponentIn (R.punctured_subset_compl_support S hne hx)

theorem hAngleSide_hConvex {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : HConvex (hAngleSide R S) := by
  obtain ⟨x,hx⟩ := S.punctured_nonempty
  rw [hAngleSide_eq_component R S hne hx]
  exact openHHalfPlane_hConvex R.supportLine x (R.punctured_subset_compl_support S hne hx)

/-- A proper angle interior is exactly the actual intersection of its two selected
complementary half-planes. -/
def properHAngleInterior {z : ℍ} (R S : HRayAt z) : Set ℍ := hAngleSide R S ∩ hAngleSide S R

theorem properHAngleInterior_comm {z : ℍ} (R S : HRayAt z) :
    properHAngleInterior R S = properHAngleInterior S R := inter_comm _ _

theorem properHAngleInterior_hConvex {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : HConvex (properHAngleInterior R S) := by
  intro u hu v hv w hw
  exact ⟨hAngleSide_hConvex R S hne u hu.1 v hv.1 hw,
    hAngleSide_hConvex S R (Ne.symm hne) u hu.2 v hv.2 hw⟩

/-- None records the genuine noncanonical opposite-ray case. Coincident rays have
empty interior; all other cases use the actual source half-plane construction. -/
def hAngleInteriorPair {z : ℍ} (R S : HRayAt z) : Option (Set ℍ) := by
  classical
  exact if R = S then some ∅ else if R.supportLine = S.supportLine then none
    else some (properHAngleInterior R S)

def hAngleExteriorPair {z : ℍ} (R S : HRayAt z) : Option (Set ℍ) := by
  classical
  exact if R = S then some R.valᶜ else if R.supportLine = S.supportLine then none
    else some ((R.val ∪ S.val)ᶜ \ properHAngleInterior R S)

theorem hAngleInteriorPair_comm {z : ℍ} (R S : HRayAt z) :
    hAngleInteriorPair R S = hAngleInteriorPair S R := by
  classical
  by_cases hRS : R = S
  · subst S
    rfl
  · simp only [hAngleInteriorPair,ite_eq_right hRS,ite_eq_right (Ne.symm hRS)]
    by_cases hL : R.supportLine = S.supportLine
    · simp only [hL,ite_true]
    · simp only [ite_eq_right hL,ite_eq_right (Ne.symm hL),properHAngleInterior_comm R S]

theorem hAngleExteriorPair_comm {z : ℍ} (R S : HRayAt z) :
    hAngleExteriorPair R S = hAngleExteriorPair S R := by
  classical
  by_cases hRS : R = S
  · subst S
    rfl
  · simp only [hAngleExteriorPair,ite_eq_right hRS,ite_eq_right (Ne.symm hRS)]
    by_cases hL : R.supportLine = S.supportLine
    · simp only [hL,ite_true]
    · simp only [ite_eq_right hL,ite_eq_right (Ne.symm hL),properHAngleInterior_comm R S,union_comm R.val S.val]

/-- The source angle is literally an unordered pair of genuine point-set rays. -/
abbrev HAngle (z : ℍ) := Sym2 (HRayAt z)

def HAngle.interior {z : ℍ} (A : HAngle z) : Option (Set ℍ) :=
  Sym2.lift ⟨hAngleInteriorPair,hAngleInteriorPair_comm⟩ A

def HAngle.exterior {z : ℍ} (A : HAngle z) : Option (Set ℍ) :=
  Sym2.lift ⟨hAngleExteriorPair,hAngleExteriorPair_comm⟩ A

theorem HAngle.interior_pair {z : ℍ} (R S : HRayAt z) :
    HAngle.interior s(R,S) = hAngleInteriorPair R S := rfl

theorem HAngle.exterior_pair {z : ℍ} (R S : HRayAt z) :
    HAngle.exterior s(R,S) = hAngleExteriorPair R S := rfl

theorem hAngleInteriorPair_self {z : ℍ} (R : HRayAt z) : hAngleInteriorPair R R = some ∅ := by
  simp [hAngleInteriorPair]

theorem hAngleExteriorPair_self {z : ℍ} (R : HRayAt z) : hAngleExteriorPair R R = some R.valᶜ := by
  simp [hAngleExteriorPair]

theorem hAngleInteriorPair_proper {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleInteriorPair R S = some (properHAngleInterior R S) := by
  have hRS : R ≠ S := fun h => hne (congrArg HRayAt.supportLine h)
  simp only [hAngleInteriorPair,ite_eq_right hRS,ite_eq_right hne]

/-- Different rays on the same complete h-line are exactly its two opposite halves. -/
theorem HRayAt.union_eq_support_of_same_support {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) :
    R.val ∪ S.val = R.supportLine.carrier := by
  obtain ⟨a,b,γ,t,_,_,hγ,hrange,ht,_,_,_,_⟩ :=
    R.supportLine.exists_rays_at z R.start_mem_support
  have hR := R.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    R.ideal_mem_support γ hγ.1 hrange t ht
  have hSI : S.idealEndpoint ∈ R.supportLine.idealEndpoints := hL.symm ▸ S.ideal_mem_support
  have hS := S.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    hSI γ hγ.1 hrange t ht
  rcases hR with hR | hR <;> rcases hS with hS | hS
  · exact (hRS (Subtype.ext (hR.trans hS.symm))).elim
  · rw [hR,hS,union_comm,hLineRay_union,hrange]
  · rw [hR,hS,hLineRay_union,hrange]
  · exact (hRS (Subtype.ext (hR.trans hS.symm))).elim

theorem hAngleInteriorPair_opposite {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : hAngleInteriorPair R S = none := by
  simp only [hAngleInteriorPair,ite_eq_right hRS,ite_eq_left hL]

theorem hAngleExteriorPair_opposite {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : hAngleExteriorPair R S = none := by
  simp only [hAngleExteriorPair,ite_eq_right hRS,ite_eq_left hL]

theorem hAngleExteriorPair_proper {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleExteriorPair R S = some ((R.val ∪ S.val)ᶜ \ properHAngleInterior R S) := by
  have hRS : R ≠ S := fun h => hne (congrArg HRayAt.supportLine h)
  simp only [hAngleExteriorPair,ite_eq_right hRS,ite_eq_right hne]

theorem hAngleSide_subset_compl_support {z : ℍ} (R S : HRayAt z) :
    hAngleSide R S ⊆ R.supportLine.carrierᶜ := by
  intro u hu
  simp only [hAngleSide,mem_iUnion] at hu
  obtain ⟨v,_,hv⟩ := hu
  exact connectedComponentIn_subset _ _ hv

theorem properHAngleInterior_subset_compl_union {z : ℍ} (R S : HRayAt z) :
    properHAngleInterior R S ⊆ (R.val ∪ S.val)ᶜ := by
  rintro x hx (hxR | hxS)
  · exact hAngleSide_subset_compl_support R S hx.1 (R.subset_support hxR)
  · exact hAngleSide_subset_compl_support S R hx.2 (S.subset_support hxS)

theorem HalfPlaneLine.isClosed_carrier (L : HalfPlaneLine) : IsClosed L.carrier := by
  obtain ⟨γ,hγ,hrange⟩ := L.exists_isometric_param
  rw [← hrange]
  exact hγ.isClosedEmbedding.isClosed_range

theorem hAngleSide_isOpen {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (hAngleSide R S) := by
  obtain ⟨x,hx⟩ := S.punctured_nonempty
  rw [hAngleSide_eq_component R S hne hx]
  exact R.supportLine.isClosed_carrier.isOpen_compl.connectedComponentIn

theorem properHAngleInterior_isOpen {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (properHAngleInterior R S) :=
  (hAngleSide_isOpen R S hne).inter (hAngleSide_isOpen S R (Ne.symm hne))

theorem properHAngleInterior_isPreconnected {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsPreconnected (properHAngleInterior R S) :=
  (properHAngleInterior_hConvex R S hne).isPreconnected

/-- Every canonically defined interior is convex, including the empty interior of a repeated ray. -/
theorem hAngleInteriorPair_some_hConvex {z : ℍ} (R S : HRayAt z) {U : Set ℍ}
    (hU : hAngleInteriorPair R S = some U) : HConvex U := by
  classical
  by_cases hRS : R = S
  · subst S
    rw [hAngleInteriorPair_self,Option.some.injEq] at hU
    rw [← hU]
    exact fun _ hu => hu.elim
  · by_cases hL : R.supportLine = S.supportLine
    · rw [hAngleInteriorPair_opposite R S hL hRS] at hU
      cases hU
    · rw [hAngleInteriorPair_proper R S hL,Option.some.injEq] at hU
      rw [← hU]
      exact properHAngleInterior_hConvex R S hL

theorem HAngle.interior_hConvex {z : ℍ} (A : HAngle z) {U : Set ℍ}
    (hU : A.interior = some U) : HConvex U := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleInteriorPair_some_hConvex R S hU

end
end LowDimensionalTopology.Geometry.Hyperbolic
