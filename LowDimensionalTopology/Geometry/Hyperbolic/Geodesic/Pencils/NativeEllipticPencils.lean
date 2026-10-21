/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.EllipticPencils
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

def discMetricCircle (p : 𝔻) (r : ℝ) : Set 𝔻 := {z | discPathDist z p=r}

def discMetricCircleFamily (p : 𝔻) : Set (Set 𝔻) := {S | ∃r : ℝ,0<r ∧ S=discMetricCircle p r}

def discEllipticPencil (p : 𝔻) : Set DiscLine := {L | p∈L.carrier}

theorem discMetricCircle_eq_cayley_image (p : 𝔻) (r : ℝ) :
    discMetricCircle p r=halfPlaneToDisc '' hMetricCircle (discToHalfPlane p) r := by
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change dist (discToHalfPlane z) (discToHalfPlane p)=r
    rw [←discPathDist_eq_halfPlane]
    exact hz
  · rintro ⟨w,hw,rfl⟩
    change discPathDist (halfPlaneToDisc w) p=r
    rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hw

theorem discMetricCircle_inverse_cayley_image (p : 𝔻) (r : ℝ) :
    discToHalfPlane '' discMetricCircle p r=hMetricCircle (discToHalfPlane p) r := by
  rw [discMetricCircle_eq_cayley_image,inverse_cayley_image_image]

theorem discPathDist_ne_zero_iff (z p : 𝔻) : discPathDist z p≠0 ↔ z≠p := by
  rw [discPathDist_eq_halfPlane,dist_ne_zero]
  exact discToHalfPlane_injective.ne_iff

theorem discMetricCircle_zero (p : 𝔻) : discMetricCircle p 0={p} := by
  ext z
  change discPathDist z p=0 ↔ z=p
  exact not_iff_not.mp (discPathDist_ne_zero_iff z p)

theorem discMetricCircle_nonempty (p : 𝔻) (r : ℝ) (hr : 0≤r) : (discMetricCircle p r).Nonempty := by
  rw [discMetricCircle_eq_cayley_image]
  exact (hMetricCircle_nonempty (discToHalfPlane p) r hr).image halfPlaneToDisc

/-- Corrected native P1, for every point different from the actual common center. -/
theorem existsUnique_discMetricCircle_through {p z : 𝔻} (hz : z≠p) :
    ∃!S : Set 𝔻,S∈discMetricCircleFamily p ∧ z∈S := by
  have hp : 0<discPathDist z p := by
    rw [discPathDist_eq_halfPlane]
    exact dist_pos.mpr (discToHalfPlane_injective.ne hz)
  refine ⟨discMetricCircle p (discPathDist z p),⟨⟨_,hp,rfl⟩,rfl⟩,?_⟩
  rintro S ⟨⟨r,hr,rfl⟩,hm⟩
  change discPathDist z p=r at hm
  rw [hm]

theorem center_not_mem_discMetricCircleFamily (p : 𝔻) :
    ¬∃S∈discMetricCircleFamily p,p∈S := by
  rintro ⟨S,⟨r,hr,rfl⟩,hp⟩
  change discPathDist p p=r at hp
  rw [discPathDist_eq_halfPlane,dist_self] at hp
  linarith

theorem existsUnique_discEllipticPencil_through {p z : 𝔻} (hz : z≠p) :
    ∃!L : DiscLine,L∈discEllipticPencil p ∧ z∈L.carrier := by
  exact existsUnique_discLine_through p z hz.symm

theorem same_discMetricCircle_iff {p a b : 𝔻} (hab : a≠b) :
    (∃S∈discMetricCircleFamily p,a∈S ∧ b∈S) ↔ discPathDist a p=discPathDist b p := by
  constructor
  · rintro ⟨S,⟨r,hr,rfl⟩,ha,hb⟩
    exact ha.trans hb.symm
  · intro he
    have hp : a≠p := by
      intro ha
      subst a
      have hz : discPathDist b p=0:=by
        rw [discPathDist_eq_halfPlane,dist_self] at he
        exact he.symm
      have hb : b=p := by
        apply discToHalfPlane_injective
        apply dist_eq_zero.mp
        rwa [←discPathDist_eq_halfPlane]
      exact hab hb.symm
    have hpos : 0<discPathDist a p:=by
      rw [discPathDist_eq_halfPlane]
      exact dist_pos.mpr (discToHalfPlane_injective.ne hp)
    exact ⟨discMetricCircle p (discPathDist a p),⟨_,hpos,rfl⟩,rfl,he.symm⟩

/-- Native P3 retains the actual Euclidean circle normal orthogonality. -/
theorem discMetricCircle_orthogonal (p : 𝔻) (r : ℝ) (hr : 0<r)
    (L : DiscLine) (hL : L∈discEllipticPencil p) :
    ∃C : Mobius.ComplexGeneralizedCircle,discMetricCircle p r=nativeDiscCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.val C := by
  obtain ⟨C,hC,ho⟩:=hMetricCircle_orthogonal (discToHalfPlane p) r hr L.toHalfPlane ((L.mem_carrier p).mp hL)
  refine ⟨C.image cayleyMobius,?_,?_⟩
  · rw [nativeDiscCircleCarrier_cayley_image,←hC,discMetricCircle_eq_cayley_image]
  · have he : L.toHalfPlane.extendedCircle.image cayleyMobius=L.val := by
      change L.toHalfPlane.toDiscLine.val=L.val
      rw [L.toHalfPlane_spec]
    rw [←he]
    exact ho.image _ _ _

theorem discMetricCircle_reflection (p : 𝔻) (r : ℝ) (L : DiscLine) (hL : L∈discEllipticPencil p) :
    L.reflection '' discMetricCircle p r=discMetricCircle p r := by
  rw [discMetricCircle_eq_cayley_image]
  calc
    _=halfPlaneToDisc '' (L.toHalfPlane.reflection '' hMetricCircle (discToHalfPlane p) r) := by
      rw [image_image,image_image]
      congr 1
      funext z
      change halfPlaneToDisc (L.toHalfPlane.reflection (discToHalfPlane (halfPlaneToDisc z)))=_
      rw [discToHalfPlane_halfPlaneToDisc]
    _=halfPlaneToDisc '' hMetricCircle (discToHalfPlane p) r := by
      rw [hMetricCircle_reflection _ _ _ ((L.mem_carrier p).mp hL)]

/-- Native P5 realizes the actual native curve-distance infimum. -/
theorem discMetricCircle_equidistance (p : 𝔻) (r s : ℝ) (hr : 0<r) (hs : 0≤s)
    (z : 𝔻) (hz : z∈discMetricCircle p r) :
    ∃w : 𝔻,w∈discMetricCircle p s ∧ discPathDist z w=discCurveDistance (discMetricCircle p r) (discMetricCircle p s) ∧
      discPathDist z w=|r-s| ∧ ∃L : DiscLine,L∈discEllipticPencil p ∧ z∈L.carrier ∧ w∈L.carrier := by
  have hzH : discToHalfPlane z∈hMetricCircle (discToHalfPlane p) r := by
    change dist (discToHalfPlane z) (discToHalfPlane p)=r
    rw [←discPathDist_eq_halfPlane]
    exact hz
  obtain ⟨w,hw,hd,hlen,L,hL,hzL,hwL⟩:=hMetricCircle_equidistance (discToHalfPlane p) r s hr hs (discToHalfPlane z) hzH
  refine ⟨halfPlaneToDisc w,?_,?_,?_,L.toDiscLine,?_,?_,?_⟩
  · rw [discMetricCircle_eq_cayley_image]
    exact mem_image_of_mem _ hw
  · rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc,discCurveDistance_eq_halfPlane,
      discMetricCircle_inverse_cayley_image,discMetricCircle_inverse_cayley_image]
    exact hd
  · rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hlen
  · change p∈L.toDiscLine.carrier
    rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hzL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hwL

theorem discMetricCircle_curveDistance (p : 𝔻) (r s : ℝ) (hr : 0<r) (hs : 0≤s) :
    discCurveDistance (discMetricCircle p r) (discMetricCircle p s)=|r-s| := by
  rw [discCurveDistance_eq_halfPlane,discMetricCircle_inverse_cayley_image,discMetricCircle_inverse_cayley_image]
  exact hMetricCircle_curveDistance (discToHalfPlane p) r s hr hs

theorem discEllipticPencil_perpendicularBisector_iff (p : 𝔻) {a b : 𝔻} (hab : a≠b)
    {N : DiscLine} (hN : IsDiscPerpendicularBisector N a b) :
    N∈discEllipticPencil p ↔ ∃S∈discMetricCircleFamily p,a∈S ∧ b∈S := by
  rw [same_discMetricCircle_iff hab]
  change p∈N.carrier ↔ discPathDist a p=discPathDist b p
  rw [hN.carrier_eq hab]
  change discPathDist p a=discPathDist p b ↔ discPathDist a p=discPathDist b p
  simp only [discPathDist_eq_halfPlane,dist_comm]

/-- The native zero-center metric circles are the actual Euclidean concentric circles. -/
theorem discMetricCircle_zero_euclidean (r : ℝ) (z : 𝔻) :
    z∈discMetricCircle 0 r ↔ ‖(z : ℂ)‖=Real.tanh (r/2) := by
  have hc : discPathDist z 0=discPathDist 0 z:=by simp only [discPathDist_eq_halfPlane,dist_comm]
  have ht : ‖(z : ℂ)‖=Real.tanh (discPathDist z 0/2):=by
    rw [hc]
    exact disc_norm_eq_tanh_half_distance z
  constructor
  · intro hz
    change discPathDist z 0=r at hz
    rwa [hz] at ht
  · intro hz
    have he:=congrArg Real.artanh (ht.symm.trans hz)
    rw [Real.artanh_tanh,Real.artanh_tanh] at he
    change discPathDist z 0=r
    linarith


/-- The normalized native pencil consists of exactly the actual Euclidean diameters. -/
theorem discEllipticPencil_zero_iff_diameter (L : DiscLine) :
    L∈discEllipticPencil 0 ↔ ∃a : ℂ,a≠0 ∧ L.val.val=Mobius.complexLine a 0 := by
  constructor
  · intro hL
    rcases (Mobius.isComplexGeneralizedCircle_iff L.val.val).mp L.val.property with ⟨c,r,hr,he⟩ | ⟨a,t,ha,he⟩
    · have hS : L.val=⟨Mobius.complexCircle c r,Mobius.complexCircle_isGeneralized c r hr⟩:=Subtype.ext he
      have ho:=L.property
      rw [hS] at ho
      have hc:=(complexCircle_orthogonal_discBoundary_iff c r hr).mp ho
      change (((0 : 𝔻) : ℂ) : OnePoint ℂ)∈L.val.val at hL
      rw [he,Mobius.complexCircle_coe] at hL
      have hn : ‖c‖=r:=by simpa using hL
      nlinarith
    · change (((0 : 𝔻) : ℂ) : OnePoint ℂ)∈L.val.val at hL
      rw [he,Mobius.complexLine_coe] at hL
      have ht : t=0:=by simpa using hL.symm
      exact ⟨a,ha,ht ▸ he⟩
  · rintro ⟨a,ha,he⟩
    change (((0 : 𝔻) : ℂ) : OnePoint ℂ)∈L.val.val
    rw [he,Mobius.complexLine_coe]
    simp

theorem hEllipticPencil_members_intersecting (p : ℍ) {L M : HalfPlaneLine}
    (hL : L∈hEllipticPencil p) (hM : M∈hEllipticPencil p) (hne : L≠M) : L.Intersecting M := by
  rcases L.classification M hne with hpar | hi | hd
  · obtain ⟨w,hw⟩:=hpar.2
    have hwm : w∈L.idealEndpoints∩M.idealEndpoints:=by rw [hw]; exact mem_singleton w
    exact False.elim (hne (L.eq_of_shared_ideal_and_interior M p hL hM w hwm.1 hwm.2))
  · exact hi
  · exact False.elim (Set.disjoint_left.mp hd.2.2 hL hM)

theorem discEllipticPencil_members_intersecting (p : 𝔻) {L M : DiscLine}
    (hL : L∈discEllipticPencil p) (hM : M∈discEllipticPencil p) (hne : L≠M) : L.Intersecting M := by
  have hi:=hEllipticPencil_members_intersecting (discToHalfPlane p)
    ((L.mem_carrier p).mp hL) ((M.mem_carrier p).mp hM) (DiscLine.toHalfPlane_injective.ne hne)
  refine ⟨hne,?_,p,hL,hM⟩
  rw [L.idealEndpoints_eq_cayley_image,M.idealEndpoints_eq_cayley_image,
    Set.disjoint_image_iff extendedCayley.injective]
  exact hi.2.1

/-- Both directions of the actual normalized Euclidean concentric-circle model. -/
theorem discMetricCircleFamily_zero_iff (S : Set 𝔻) :
    S∈discMetricCircleFamily 0 ↔ ∃R : ℝ,0<R ∧ R<1 ∧ S={z : 𝔻 | ‖(z : ℂ)‖=R} := by
  constructor
  · rintro ⟨r,hr,rfl⟩
    refine ⟨Real.tanh (r/2),?_,Real.tanh_lt_one _,?_⟩
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    · ext z
      exact discMetricCircle_zero_euclidean r z
  · rintro ⟨R,hR,hR1,rfl⟩
    have hnorm : ‖(R : ℂ)‖=R:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    let z : 𝔻:=Complex.UnitDisc.mk (R : ℂ) (by rwa [hnorm])
    have hz : z≠0 := by
      intro he
      have hn:=congrArg (fun w : 𝔻 => ‖(w : ℂ)‖) he
      change ‖(R : ℂ)‖=‖(0 : ℂ)‖ at hn
      rw [hnorm,norm_zero] at hn
      linarith
    let r:=discPathDist z 0
    have hr : 0<r:=by
      change 0<discPathDist z 0
      rw [discPathDist_eq_halfPlane]
      exact dist_pos.mpr (discToHalfPlane_injective.ne hz)
    have he : Real.tanh (r/2)=R := by
      have hh:=(discMetricCircle_zero_euclidean r z).mp (show z∈discMetricCircle 0 r from rfl)
      change ‖(R : ℂ)‖=Real.tanh (r/2) at hh
      rw [hnorm] at hh
      exact hh.symm
    refine ⟨r,hr,?_⟩
    ext w
    rw [discMetricCircle_zero_euclidean,he]
    rfl

end
end LowDimensionalTopology.Geometry.Hyperbolic
