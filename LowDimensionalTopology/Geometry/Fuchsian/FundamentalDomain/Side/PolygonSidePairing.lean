module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace





/-- Actual Klein-coordinate images of distinct open tiles are disjoint. -/
theorem IsFuchsianFundamentalDomain.klein_images_disjoint
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {g h : H} (hgh : g ≠ h) :
    Disjoint (P.kleinCoordinate '' (g • D)) (P.kleinCoordinate '' (h • D)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy := P.kleinCoordinate_isOpenEmbedding.injective (hxz.trans hyz.symm)
  exact hgh (hD.tile_intersection_eq hx (hxy.symm ▸ hy))

/-- Actual Klein-coordinate images of open polygon tiles are genuinely Euclidean convex. -/
theorem IsConvexFuchsianPolygon.klein_smul_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (g : H) : Convex ℝ (P.kleinCoordinate '' (g • D)) := by
  change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)) '' (g • D))
  rw [← image_image]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.smul_convex g)

/-- Every original closed tile maps into the closure of its own open Klein tile. -/
theorem UnitDiscFuchsianGroup.klein_closed_tile_subset_closure
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (g : H) :
    P.kleinCoordinate '' fuchsianDomainTile P D g ⊆ closure (P.kleinCoordinate '' (g • D)) := by
  change P.kleinCoordinate '' (g • closure D) ⊆ _
  have he : g • closure D = closure (g • D) := (Homeomorph.smul g).image_closure D
  rw [he]
  exact image_closure_subset_closure_image P.kleinCoordinate_isOpenEmbedding.continuous

/-- Three distinct closed fundamental-polygon copies share at most one actual point. -/
theorem IsConvexFuchsianPolygon.closed_tile_triple_subsingleton
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {g h : H} (hg : g ≠ 1) (hh : h ≠ 1) (hgh : g ≠ h) :
    (closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h).Subsingleton := by
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUo := P.kleinCoordinate_isOpenEmbedding.isOpenMap D hDo
  have hUn := hDn.image P.kleinCoordinate
  have hVo := P.kleinCoordinate_isOpenEmbedding.isOpenMap (g • D) ((Homeomorph.smul g).isOpenMap D hDo)
  have hVn := (hDn.image (fun x => g • x)).image P.kleinCoordinate
  have hWo := P.kleinCoordinate_isOpenEmbedding.isOpenMap (h • D) ((Homeomorph.smul h).isOpenMap D hDo)
  have hWn := (hDn.image (fun x => h • x)).image P.kleinCoordinate
  have hUV : Disjoint (P.kleinCoordinate '' D) (P.kleinCoordinate '' (g • D)) := by
    simpa only [one_smul] using hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hg)
  have hUW : Disjoint (P.kleinCoordinate '' D) (P.kleinCoordinate '' (h • D)) := by
    simpa only [one_smul] using hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hh)
  have hVW := hD.locallyFinite.fundamental.klein_images_disjoint hgh
  have hs := _root_.LowDimensionalTopology.Geometry.Euclidean.three_disjoint_open_convex_closures_subsingleton hD.klein_convex hUo hUn
    (hD.klein_smul_convex g) hVo hVn (hD.klein_smul_convex h) hWo hWn hUV hUW hVW
  have hUcl : P.kleinCoordinate '' closure D ⊆ closure (P.kleinCoordinate '' D) :=
    image_closure_subset_closure_image P.kleinCoordinate_isOpenEmbedding.continuous
  intro x hx y hy
  apply P.kleinCoordinate_isOpenEmbedding.injective
  exact hs ⟨⟨hUcl ⟨x, hx.1.1, rfl⟩, P.klein_closed_tile_subset_closure D g ⟨x, hx.1.2, rfl⟩⟩,
    P.klein_closed_tile_subset_closure D h ⟨x, hx.2, rfl⟩⟩
    ⟨⟨hUcl ⟨y, hy.1.1, rfl⟩, P.klein_closed_tile_subset_closure D g ⟨y, hy.1.2, rfl⟩⟩,
    P.klein_closed_tile_subset_closure D h ⟨y, hy.2, rfl⟩⟩

/-- A genuine side is attached to exactly one original group element. -/
theorem IsConvexFuchsianPolygon.side_element_unique
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {g h : H} (hg : g ≠ 1) (hh : h ≠ 1)
    (hn : (closure D ∩ fuchsianDomainTile P D g).Nontrivial)
    (he : closure D ∩ fuchsianDomainTile P D g = closure D ∩ fuchsianDomainTile P D h) : g = h := by
  by_contra hgh
  have hs := hD.closed_tile_triple_subsingleton hg hh hgh
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  have hx' : x ∈ closure D ∩ fuchsianDomainTile P D h := he ▸ hx
  have hy' : y ∈ closure D ∩ fuchsianDomainTile P D h := he ▸ hy
  exact hxy (hs ⟨hx, hx'.2⟩ ⟨hy, hy'.2⟩)

/-- The source's unique side-pairing element exists for every actual side. -/
theorem IsConvexFuchsianPolygon.existsUnique_side_element
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hS : IsFuchsianPolygonSide P D S) :
    ∃! g : H, g ≠ 1 ∧ S = closure D ∩ fuchsianDomainTile P D g := by
  obtain ⟨⟨g, hg, he⟩, _hseg, hn⟩ := hS
  refine ⟨g, ⟨hg, he⟩, ?_⟩
  rintro h ⟨hh, heh⟩
  apply hD.side_element_unique hh hg (heh ▸ hn)
  exact heh.symm.trans he

/-- The literal set of sides, not a separate set of group-element witnesses. -/
def FuchsianPolygonSides
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) := {S : Set P.domain.carrier // IsFuchsianPolygonSide P D S}

/-- The unique original group element associated to a literal actual side. -/
def fuchsianSideElement
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) : H :=
  (hD.existsUnique_side_element s.property).choose

theorem fuchsianSideElement_spec
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    fuchsianSideElement hD s ≠ 1 ∧
      s.val = closure D ∩ fuchsianDomainTile P D (fuchsianSideElement hD s) :=
  (hD.existsUnique_side_element s.property).choose_spec.1

/-- The original side-to-element correspondence is injective. -/
theorem fuchsianSideElement_injective
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Function.Injective (fuchsianSideElement hD) := by
  intro s t he
  apply Subtype.ext
  exact (fuchsianSideElement_spec hD s).2.trans
    ((congrArg (fun g => closure D ∩ fuchsianDomainTile P D g) he).trans
      (fuchsianSideElement_spec hD t).2.symm)

/-- The inverse original element transports the common closed-tile side exactly to its partner. -/
theorem inverse_closed_tile_intersection {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (g : H) :
    g⁻¹ • (closure D ∩ fuchsianDomainTile P D g) = closure D ∩ fuchsianDomainTile P D g⁻¹ := by
  change g⁻¹ • (closure D ∩ g • closure D) = closure D ∩ g⁻¹ • closure D
  rw [smul_set_inter, inv_smul_smul, inter_comm]

/-- The actual partner is obtained by the inverse of the original side's unique element. -/
def fuchsianPairedSide
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    FuchsianPolygonSides P D := by
  let g := fuchsianSideElement hD s
  have hg : g ≠ 1 := (fuchsianSideElement_spec hD s).1
  have he : g⁻¹ • s.val = closure D ∩ fuchsianDomainTile P D g⁻¹ := by
    rw [(fuchsianSideElement_spec hD s).2]
    exact inverse_closed_tile_intersection P D g
  have hn : (g⁻¹ • s.val).Nontrivial := s.property.2.2.image (Homeomorph.smul g⁻¹).injective
  refine ⟨g⁻¹ • s.val, ?_⟩
  rw [he]
  exact hD.side_of_nontrivial_intersection (inv_ne_one.mpr hg) (he ▸ hn)

@[simp] theorem fuchsianPairedSide_val
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    (fuchsianPairedSide hD s).val = (fuchsianSideElement hD s)⁻¹ • s.val := rfl

/-- Pairing reverses the actual original group element. -/
theorem fuchsianSideElement_paired
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    fuchsianSideElement hD (fuchsianPairedSide hD s) = (fuchsianSideElement hD s)⁻¹ := by
  apply (hD.existsUnique_side_element (fuchsianPairedSide hD s).property).unique
    (fuchsianSideElement_spec hD (fuchsianPairedSide hD s))
  refine ⟨inv_ne_one.mpr (fuchsianSideElement_spec hD s).1, ?_⟩
  rw [fuchsianPairedSide_val, (fuchsianSideElement_spec hD s).2]
  exact inverse_closed_tile_intersection P D (fuchsianSideElement hD s)

/-- The actual side pairing is an involution, allowing self-paired sides. -/
theorem fuchsianPairedSide_involutive
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Function.Involutive (fuchsianPairedSide hD) := by
  intro s
  apply Subtype.ext
  rw [fuchsianPairedSide_val, fuchsianPairedSide_val, fuchsianSideElement_paired, inv_inv, smul_inv_smul]

/-- The source's original pairing transformation sends its partner exactly back to the side. -/
theorem fuchsianSideElement_paired_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    (fuchsianSideElement hD s) • (fuchsianPairedSide hD s).val = s.val := by
  rw [fuchsianPairedSide_val, smul_inv_smul]

/-- The actual side pairing as a permutation of the literal side set. -/
def fuchsianSidePairingEquiv
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Equiv.Perm (FuchsianPolygonSides P D) := (fuchsianPairedSide_involutive hD).toPerm

end LowDimensionalTopology.Geometry.Fuchsian
