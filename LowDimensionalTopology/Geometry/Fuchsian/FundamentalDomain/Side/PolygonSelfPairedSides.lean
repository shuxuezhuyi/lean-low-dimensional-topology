module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonVertexSides
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean

/-- Actual native-disc midpoints are preserved by genuine hyperbolic isometries. -/
theorem discMidpoint_image_isometry {f : Complex.UnitDisc → Complex.UnitDisc}
    (hf : let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; Isometry f)
    {a b w : Complex.UnitDisc}
    (hab : a ≠ b) (hw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscMidpoint a b w) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscMidpoint (f a) (f b) (f w) := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  refine ⟨?_,?_⟩
  · rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_isometry_image_closedHSegment hf hab]
    exact mem_image_of_mem f hw.1
  · have he := hw.2
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,
      ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] at he ⊢
    simpa only [hf.dist_eq] using he

/-- The true metric midpoint lies strictly between its distinct endpoints in Klein coordinates. -/
theorem discMidpoint_klein_openSegment {a b w : Complex.UnitDisc} (hab : a ≠ b)
    (hw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscMidpoint a b w) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w ∈ openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate b) := by
  have hh := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscMidpoint_iff_halfPlane a b w).mp hw).half_distance
  have hd : 0 < dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b) :=
    dist_pos.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne hab)
  have hwa : w ≠ a := by
    intro he
    rw [he,dist_self] at hh
    linarith [hh.1]
  have hwb : w ≠ b := by
    intro he
    rw [he,dist_self] at hh
    linarith [hh.2]
  apply mem_openSegment_of_ne_left_right (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.ne (Ne.symm hwa))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.ne (Ne.symm hwb))
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closedDiscHSegment]
  exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate hw.1

/-- Every actual nondegenerate side contains three distinct genuine disc points. -/
theorem IsFuchsianPolygonSide.exists_three_points
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a,ha,b,hb,hab⟩ := hS.2.2
  obtain ⟨w,hw,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discMidpoint (P.finiteCoordinate.injective.ne hab)
  have hwS := hS.2.1.1 _ (mem_image_of_mem P.finiteCoordinate ha)
    _ (mem_image_of_mem P.finiteCoordinate hb) hw.1
  obtain ⟨c,hc,hcw⟩ := hwS
  have ho := discMidpoint_klein_openSegment (P.finiteCoordinate.injective.ne hab) hw
  have habK := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.ne (P.finiteCoordinate.injective.ne hab)
  have hac : a ≠ c := by
    intro he
    rw [← hcw,← he] at ho
    exact habK (left_mem_openSegment_iff.mp ho)
  have hbc : b ≠ c := by
    intro he
    rw [← hcw,← he] at ho
    exact habK (right_mem_openSegment_iff.mp ho)
  exact ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩

/-- A nonidentity actual Mobius element moves some point of every genuine side. -/
theorem IsFuchsianPolygonSide.exists_moved_point
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S)
    (g : H) (hg : g ≠ 1) : ∃ a ∈ S, g • a ≠ a := by
  classical
  by_contra hn
  have hfix : ∀ a ∈ S, g • a = a := by simpa only [not_exists,not_and,not_not] using hn
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := hS.exists_three_points
  apply hg
  apply Subtype.ext
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed g.val a.val b.val c.val
    (Subtype.val_injective.ne hab) (Subtype.val_injective.ne hac) (Subtype.val_injective.ne hbc)
  · exact congrArg Subtype.val (hfix a ha)
  · exact congrArg Subtype.val (hfix b hb)
  · exact congrArg Subtype.val (hfix c hc)

/-- A literal self-paired side is characterized by the original pairing element having square one. -/
theorem fuchsianPairedSide_eq_self_iff_square_one
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    fuchsianPairedSide hD s = s ↔ fuchsianSideElement hD s ^ 2 = 1 := by
  constructor
  · intro he
    have hi := congrArg (fuchsianSideElement hD) he
    rw [fuchsianSideElement_paired] at hi
    calc
      _ = fuchsianSideElement hD s * (fuchsianSideElement hD s)⁻¹ := by rw [pow_two,hi]
      _ = 1 := mul_inv_cancel _
  · intro hs
    apply fuchsianSideElement_injective hD
    rw [fuchsianSideElement_paired]
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)

/-- A genuine nontrivial involution preserving an actual side has a fixed point strictly inside it. -/
theorem IsFuchsianPolygonSide.involution_fixed_interior
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S)
    (g : H) (hg : g ≠ 1) (hgg : g ^ 2 = 1) (himage : g • S = S) :
    ∃ x ∈ S, g • x = x ∧ IsFuchsianPolygonSideInterior P D x := by
  obtain ⟨a,ha,hmove⟩ := hS.exists_moved_point g hg
  let b := g • a
  have hb : b ∈ S := himage ▸ mem_smul_set.mpr ⟨a,ha,rfl⟩
  have hba : g • b = a := by simp only [b,← mul_smul,← pow_two,hgg,one_smul]
  have hab : P.finiteCoordinate a ≠ P.finiteCoordinate b :=
    P.finiteCoordinate.injective.ne (Ne.symm hmove)
  obtain ⟨w,hw,huniq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discMidpoint hab
  let f := P.discAction g
  have hfa : f (P.finiteCoordinate a) = P.finiteCoordinate b := by
    change P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate a)) = P.finiteCoordinate b
    rw [P.finiteCoordinate.symm_apply_apply]
  have hfb : f (P.finiteCoordinate b) = P.finiteCoordinate a := by
    change P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate b)) = P.finiteCoordinate a
    rw [P.finiteCoordinate.symm_apply_apply,hba]
  have hwf := discMidpoint_image_isometry (P.discAction_isometry g) hab hw
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscMidpoint (f (P.finiteCoordinate a)) (f (P.finiteCoordinate b)) (f w) at hwf
  rw [hfa,hfb] at hwf
  have hcomm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHSegment (P.finiteCoordinate b) (P.finiteCoordinate a) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHSegment (P.finiteCoordinate a) (P.finiteCoordinate b) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.image_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closedDiscHSegment,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closedDiscHSegment, segment_symm]
  have hmid : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscMidpoint (P.finiteCoordinate a) (P.finiteCoordinate b) (f w) := by
    refine ⟨hcomm ▸ hwf.1,?_⟩
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,dist_comm] using hwf.2.symm
  have hfw : f w = w := huniq (f w) hmid
  have hwS := hS.2.1.1 _ (mem_image_of_mem P.finiteCoordinate ha)
    _ (mem_image_of_mem P.finiteCoordinate hb) hw.1
  obtain ⟨x,hx,hxw⟩ := hwS
  have hfix : g • x = x := by
    apply P.finiteCoordinate.injective
    have he : P.finiteCoordinate (g • x) = f (P.finiteCoordinate x) := by
      change P.finiteCoordinate (g • x) =
        P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate x))
      rw [P.finiteCoordinate.symm_apply_apply]
    rw [he,hxw,hfw]
  refine ⟨x,hx,hfix,S,hS,a,ha,b,hb,Ne.symm hmove,?_⟩
  have hnorm := discOriginNormalizer_isometry (P.finiteCoordinate x)
  have hwn := discMidpoint_image_isometry hnorm hab hw
  have habn := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x)).injective.ne hab
  have hho := discMidpoint_klein_openSegment habn hwn
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate x)) ∈
    openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate a)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate b)))
  rw [hxw]
  simpa only [hxw] using hho

/-- A nonidentity stabilizer at a true side-interior point is exactly that side's original pairing element. -/
theorem IsConvexFuchsianPolygon.side_interior_fixing_eq_pairing
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {x : P.domain.carrier} (hx : x ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D x)
    (g : H) (hg : g ≠ 1) (hfix : g • x = x) : g = fuchsianSideElement hD s := by
  have hxFront := (hD.side_interior_iff_boundary_nonvertex x).mp hi
  obtain ⟨k,_hk,hunique⟩ := hD.nonvertex_incident_unique hxFront.1 hxFront.2
  have hxg : x ∈ fuchsianDomainTile P D g :=
    ⟨x,frontier_subset_closure hxFront.1,hfix⟩
  have hxs := (fuchsianSideElement_spec hD s).2 ▸ hx
  exact (hunique g ⟨hg,hxg⟩).trans
    (hunique (fuchsianSideElement hD s) ⟨(fuchsianSideElement_spec hD s).1,hxs.2⟩).symm

/-- Fixing a true interior point of the paired side forces the literal side to be self-paired. -/
theorem fuchsianPairedSide_eq_self_of_fixed_interior
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {x : P.domain.carrier} (hx : x ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D x)
    (hfix : fuchsianSideElement hD s • x = x) : fuchsianPairedSide hD s = s := by
  have hfinv : (fuchsianSideElement hD s)⁻¹ • x = x := by
    calc
      _ = (fuchsianSideElement hD s)⁻¹ • (fuchsianSideElement hD s • x) := by rw [hfix]
      _ = x := inv_smul_smul _ _
  have he := hD.side_interior_fixing_eq_pairing s hx hi _
    (inv_ne_one.mpr (fuchsianSideElement_spec hD s).1) hfinv
  apply fuchsianSideElement_injective hD
  rw [fuchsianSideElement_paired,he]

/-- self-pairing is equivalent to a true fixed point in the actual side interior. -/
theorem fuchsianPairedSide_eq_self_iff_fixed_interior
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    fuchsianPairedSide hD s = s ↔
      ∃ x ∈ s.val, fuchsianSideElement hD s • x = x ∧ IsFuchsianPolygonSideInterior P D x := by
  constructor
  · intro hs
    have hgg := (fuchsianPairedSide_eq_self_iff_square_one hD s).mp hs
    have himage : fuchsianSideElement hD s • s.val = s.val := by
      have he := fuchsianSideElement_paired_image hD s
      rw [hs] at he
      exact he
    exact s.property.involution_fixed_interior _ (fuchsianSideElement_spec hD s).1 hgg himage
  · rintro ⟨x,hx,hfix,hi⟩
    exact fuchsianPairedSide_eq_self_of_fixed_interior hD s hx hi hfix

/-- A true elliptic side-interior point has precisely the identity and its side-pairing element as stabilizer. -/
theorem IsConvexFuchsianPolygon.side_interior_stabilizer
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {x : P.domain.carrier} (hx : x ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D x)
    (hfix : fuchsianSideElement hD s • x = x) :
    (MulAction.stabilizer H x : Set H) = {1,fuchsianSideElement hD s} := by
  ext g
  simp only [mem_insert_iff,mem_singleton_iff]
  constructor
  · intro hg
    by_cases he : g = 1
    · exact Or.inl he
    · exact Or.inr (hD.side_interior_fixing_eq_pairing s hx hi g he hg)
  · rintro (rfl | rfl)
    · exact one_smul H x
    · exact hfix

/-- The actual stabilizer order at a self-pairing fixed point is exactly two. -/
theorem IsConvexFuchsianPolygon.side_interior_fixed_order_two
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {x : P.domain.carrier} (hx : x ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D x)
    (hfix : fuchsianSideElement hD s • x = x) : fuchsianPointOrder P x = 2 := by
  classical
  change Nat.card (MulAction.stabilizer H x) = 2
  apply (Nat.card_eq_two_iff' (1 : MulAction.stabilizer H x)).mpr
  let g : MulAction.stabilizer H x := ⟨fuchsianSideElement hD s,hfix⟩
  have hg : g ≠ 1 := by
    intro he
    exact (fuchsianSideElement_spec hD s).1 (congrArg Subtype.val he)
  refine ⟨g,hg,?_⟩
  intro k hk
  apply Subtype.ext
  apply hD.side_interior_fixing_eq_pairing s hx hi k.val
  · intro he
    exact hk (Subtype.ext he)
  · exact k.property

/-- The actual closed-polygon cycle of an elliptic side-interior point is a singleton. -/
theorem IsConvexFuchsianPolygon.side_interior_fixed_cycle_singleton
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {x : P.domain.carrier} (hx : x ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D x)
    (hfix : fuchsianSideElement hD s • x = x) : fuchsianPolygonCycle P D x = {x} := by
  have hf := (hD.side_interior_iff_boundary_nonvertex x).mp hi
  obtain ⟨k,_hk,hunique⟩ := hD.nonvertex_incident_unique hf.1 hf.2
  have hxcl := frontier_subset_closure hf.1
  have hxsg : x ∈ fuchsianDomainTile P D (fuchsianSideElement hD s) :=
    ((fuchsianSideElement_spec hD s).2 ▸ hx).2
  ext y
  constructor
  · rintro ⟨hy,ho⟩
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp ho
    by_cases hg : g = 1
    · simp only [hg,one_smul,mem_singleton_iff]
    · have hiG : x ∈ fuchsianDomainTile P D g⁻¹ := ⟨g • x,hy,inv_smul_smul g x⟩
      have he : g⁻¹ = fuchsianSideElement hD s :=
        (hunique _ ⟨inv_ne_one.mpr hg,hiG⟩).trans
          (hunique _ ⟨(fuchsianSideElement_spec hD s).1,hxsg⟩).symm
      have hinv : (fuchsianSideElement hD s)⁻¹ • x = x := by
        calc
          _ = (fuchsianSideElement hD s)⁻¹ • (fuchsianSideElement hD s • x) := by rw [hfix]
          _ = x := inv_smul_smul _ _
      simpa only [← he,inv_inv,mem_singleton_iff] using hinv
  · intro hy
    have he : y = x := mem_singleton_iff.mp hy
    exact he.symm ▸ ⟨hxcl,MulAction.mem_orbit_self x⟩

/-- Three genuinely distinct incident tiles are necessary at every original vertex. -/
theorem IsConvexFuchsianPolygon.vertex_incident_card_ge_three
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier}
    (hx : IsFuchsianPolygonVertex P D x) :
    3 ≤ (hD.locallyFinite.incident_finite x).toFinset.card := by
  classical
  obtain ⟨g,h,hg,hh,hgh,he⟩ := hx
  have hmem : x ∈ closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h :=
    he.symm ▸ mem_singleton x
  let s := (hD.locallyFinite.incident_finite x).toFinset
  have h1 : (1 : H) ∈ s := by
    apply (Set.Finite.mem_toFinset _).mpr
    change x ∈ (1 : H) • closure D
    simpa only [one_smul] using hmem.1.1
  have hgS : g ∈ s := (Set.Finite.mem_toFinset _).mpr hmem.1.2
  have hhS : h ∈ s := (Set.Finite.mem_toFinset _).mpr hmem.2
  have hsub : ({1,g,h} : Finset H) ⊆ s := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  simpa [hg,hh,hgh,Ne.symm hg,Ne.symm hh] using hc

/-- The geometric singleton cycle of order two lies in a true side interior, under the original vertex convention. -/
theorem IsConvexFuchsianPolygon.order_two_singleton_cycle_side_interior
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier} (hx : x ∈ closure D)
    (ho : fuchsianPointOrder P x = 2)
    (hc : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 1) :
    IsFuchsianPolygonSideInterior P D x := by
  have hnv : ¬ IsFuchsianPolygonVertex P D x := by
    intro hv
    have hthree := hD.vertex_incident_card_ge_three hv
    have htwo := hD.locallyFinite.incident_card_eq_order_mul_cycleLength x
    rw [ho,hc,mul_one] at htwo
    omega
  have hnD : x ∉ D := by
    intro hxD
    have hone := ((hD.interior_iff_order_one_and_cycle_length_one hx).mp hxD).1
    omega
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hfront : x ∈ frontier D := by
    rw [hDo.frontier_eq]
    exact ⟨hx,hnD⟩
  exact hD.nonvertex_is_side_interior hfront hnv

/-- The order-two singleton case has its literal self-paired side, actual fixed point and two-element stabilizer. -/
theorem IsConvexFuchsianPolygon.order_two_singleton_cycle_self_paired
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier} (hx : x ∈ closure D)
    (ho : fuchsianPointOrder P x = 2)
    (hc : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 1) :
    ∃ s : FuchsianPolygonSides P D, x ∈ s.val ∧ fuchsianPairedSide hD s = s ∧
      IsFuchsianPolygonSideInterior P D x ∧ fuchsianSideElement hD s • x = x ∧
      (MulAction.stabilizer H x : Set H) = {1,fuchsianSideElement hD s} := by
  have hi := hD.order_two_singleton_cycle_side_interior hx ho hc
  obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side (hi.mem_frontier hD.locallyFinite.fundamental)
  let s : FuchsianPolygonSides P D := ⟨S,hS⟩
  obtain ⟨g,hg,_⟩ := (Nat.card_eq_two_iff' (1 : MulAction.stabilizer H x)).mp ho
  have hg0 : g.val ≠ 1 := fun he => hg (Subtype.ext he)
  have he := hD.side_interior_fixing_eq_pairing s hxS hi g.val hg0 g.property
  have hfix : fuchsianSideElement hD s • x = x := he ▸ g.property
  exact ⟨s,hxS,fuchsianPairedSide_eq_self_of_fixed_interior hD s hxS hi hfix,hi,hfix,
    hD.side_interior_stabilizer s hxS hi hfix⟩

/-- Self-paired sides are paired by genuine order-two elliptic elements fixing an actual side-interior point. -/
theorem fuchsianPairedSide_self_geometric
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    (hs : fuchsianPairedSide hD s = s) :
    fuchsianSideElement hD s ^ 2 = 1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (fuchsianSideElement hD s).val ∧
      ∃ x ∈ s.val, fuchsianSideElement hD s • x = x ∧
        IsFuchsianPolygonSideInterior P D x ∧ fuchsianPointOrder P x = 2 ∧
        fuchsianPolygonCycle P D x = {x} ∧
        (MulAction.stabilizer H x : Set H) = {1,fuchsianSideElement hD s} := by
  obtain ⟨x,hx,hfix,hi⟩ := (fuchsianPairedSide_eq_self_iff_fixed_interior hD s).mp hs
  exact ⟨(fuchsianPairedSide_eq_self_iff_square_one hD s).mp hs,
    P.fixing_nonidentity_elliptic x _ hfix (fuchsianSideElement_spec hD s).1,
    x,hx,hfix,hi,hD.side_interior_fixed_order_two s hx hi hfix,
    hD.side_interior_fixed_cycle_singleton s hx hi hfix,hD.side_interior_stabilizer s hx hi hfix⟩

end LowDimensionalTopology.Geometry.Fuchsian
