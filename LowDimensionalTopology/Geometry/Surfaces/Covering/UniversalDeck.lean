module
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import Mathlib.Topology.Covering.Deck
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homeomorph.Quotient
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Discontinuity
@[expose] public section
noncomputable section
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- A simply connected cover has a genuine deck homeomorphism carrying any point to any
other point in its fiber. -/
theorem covering_exists_deck_map [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (a b : E) (hab : p a = p b) :
    ∃ h : deck p, h • a = b := by
  obtain ⟨F, ⟨hFa, hpF⟩, _hFu⟩ := hp.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ a b hab.symm
  obtain ⟨G, ⟨hGb, hpG⟩, _hGu⟩ := hp.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ b a hab
  have hGF : (G ∘ F : E → E) = id := hp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
    (by funext x; exact (congrFun hpG (F x)).trans (congrFun hpF x)) a (by simp [hFa, hGb])
  have hFG : (F ∘ G : E → E) = id := hp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
    (by funext x; exact (congrFun hpF (G x)).trans (congrFun hpG x)) b (by simp [hFa, hGb])
  let h : E ≃ₜ E :=
    { toFun := F
      invFun := G
      left_inv := fun x => congrFun hGF x
      right_inv := fun x => congrFun hFG x
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  exact ⟨⟨h, hpF⟩, hFa⟩

/-- The deck action of a simply connected cover is transitive precisely on the actual fibers. -/
theorem covering_deck_fiber_iff_orbit [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (a b : E) : p a = p b ↔ a ∈ MulAction.orbit (deck p) b := by
  constructor
  · intro h
    exact covering_exists_deck_map hp b a h.symm
  · rintro ⟨g, rfl⟩
    exact deck.proj_smul g b

theorem covering_existsUnique_deck_map [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (a b : E) (hab : p a = p b) :
    ∃! h : deck p, h • a = b := by
  obtain ⟨g, hg⟩ := covering_exists_deck_map hp a b hab
  refine ⟨g, hg, ?_⟩
  intro h hh
  have he : (h.val : E → E) = g.val := hp.eq_of_comp_eq h.val.continuous g.val.continuous
    (h.property.trans g.property.symm) a (hh.trans hg.symm)
  exact Subtype.ext (Homeomorph.ext (fun z => congrFun he z))

/-- Local covering sheets separate all distinct deck translates; no group-action
discontinuity hypothesis is added. -/
theorem covering_deck_separated_neighborhood [PreconnectedSpace E] (hp : IsCoveringMap p) (a : E) :
    ∃ U ∈ nhds a, ∀ g : deck p, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨e, hae, he⟩ := hp.isLocalHomeomorph a
  refine ⟨e.source, e.open_source.mem_nhds hae, ?_⟩
  rintro g ⟨w, ⟨v, hv, rfl⟩, hgv⟩
  have hfix : g • v = v := by
    apply e.injOn hgv hv
    rw [← he]
    exact deck.proj_smul g v
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_deck_fixedPoint_eq_one hp g v hfix

/-- Every surjective simply connected covering is a true quotient covering by its actual deck group. -/
theorem covering_deck_isQuotientCoveringMap [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) : IsQuotientCoveringMap p (deck p) where
  __ := hp.isQuotientMap hsurj
  continuous_const_smul := fun g => g.val.continuous
  apply_eq_iff_mem_orbit := covering_deck_fiber_iff_orbit hp _ _
  disjoint := covering_deck_separated_neighborhood hp

/-- The original base is homeomorphic to the genuine orbit quotient of its universal cover. -/
def coveringDeckQuotientHomeomorph [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Quotient (MulAction.orbitRel (deck p) E) ≃ₜ X := by
  let F : C(E, X) := ⟨p, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap hsurj
  exact (Homeomorph.Quotient.congrRight (fun a b => (covering_deck_fiber_iff_orbit hp a b).symm)).trans
    hF.homeomorph

theorem coveringDeckQuotientHomeomorph_apply_mk [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (a : E) :
    coveringDeckQuotientHomeomorph hp hsurj (Quotient.mk _ a) = p a := rfl

/-- Every actual deck transformation is analytic for the complex atlas lifted from the base. -/
theorem covering_deck_analytic (A : RiemannAtlas X) (hp : IsCoveringMap p) (g : deck p) :
    RiemannAnalyticMap (A.liftLocalHomeomorph p hp.isLocalHomeomorph)
      (A.liftLocalHomeomorph p hp.isLocalHomeomorph) g.val := by
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph p p hp.isLocalHomeomorph hp.isLocalHomeomorph
    id g.val (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id A) g.val.continuous (fun x =>
      deck.proj_smul g x)

/-- Each pair of points has open neighborhoods with only finitely many deck translates meeting. -/
theorem covering_deck_locally_finite_translates [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [T2Space X] (hp : IsCoveringMap p) (a b : E) :
    ∃ U V : Set E, IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      {g : deck p | ((g • ·) '' U ∩ V).Nonempty}.Finite := by
  by_cases hab : p a = p b
  · obtain ⟨g₀, hg₀⟩ := covering_exists_deck_map hp a b hab
    obtain ⟨N, hN, hsep⟩ := covering_deck_separated_neighborhood hp a
    obtain ⟨U, hUN, hU, haU⟩ := mem_nhds_iff.mp hN
    refine ⟨U, g₀.val '' U, hU, g₀.val.isOpenMap U hU, haU, ⟨a, haU, hg₀⟩, ?_⟩
    apply (Set.finite_singleton g₀).subset
    rintro g ⟨w, ⟨u, hu, rfl⟩, v, hv, hvg⟩
    have hcomp : ((fun z : E => (g₀⁻¹ * g) • z) '' N ∩ N).Nonempty := by
      refine ⟨v, ⟨u, hUN hu, ?_⟩, hUN hv⟩
      change g₀.val.symm (g • u) = v
      change g₀.val v = g • u at hvg
      rw [← hvg]
      exact g₀.val.symm_apply_apply v
    have he := hsep (g₀⁻¹ * g) hcomp
    exact (inv_mul_eq_one.mp he).symm
  · obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
    refine ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous, haU, hbV, ?_⟩
    apply Set.finite_empty.subset
    rintro g ⟨w, ⟨z, hz, rfl⟩, hgz⟩
    exact Set.disjoint_left.mp hUV hz (by simpa only [Set.mem_preimage, deck.proj_smul] using hgz)

/-- The deck group satisfies the actual compact-set definition of proper discontinuity. -/
theorem covering_deck_properlyDiscontinuous [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [T2Space X] (hp : IsCoveringMap p) : ProperlyDiscontinuousSMul (deck p) E := by
  classical
  constructor
  intro K L hK hL
  choose U V hU hV haU hbV hfin using fun a b : E => covering_deck_locally_finite_translates hp a b
  obtain ⟨t, ht⟩ := (hK.prod hL).elim_finite_subcover
    (fun z : E × E => U z.1 z.2 ×ˢ V z.1 z.2)
    (fun z => (hU z.1 z.2).prod (hV z.1 z.2))
    (fun z _hz => Set.mem_iUnion.mpr ⟨z, haU z.1 z.2, hbV z.1 z.2⟩)
  apply (t.finite_toSet.biUnion (fun z _hz => hfin z.1 z.2)).subset
  rintro g ⟨w, ⟨u, hu, rfl⟩, hgu⟩
  obtain ⟨z, hz, huz⟩ := Set.mem_iUnion₂.mp (ht (show (u, g • u) ∈ K ×ˢ L from ⟨hu, hgu⟩))
  exact Set.mem_iUnion₂.mpr ⟨z, hz, ⟨g • u, ⟨u, huz.1, rfl⟩, huz.2⟩⟩

theorem covering_deck_discontinuous [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [T2Space X] (hp : IsCoveringMap
      p) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous (deck p) E :=
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul (deck p)
    E).mpr
    (covering_deck_properlyDiscontinuous hp)

/-- The actual deck quotient inherits the complex surface structure through its proved
homeomorphism to the base. -/
def coveringDeckQuotientRiemannSurface [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (A : RiemannSurface X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    RiemannSurface (Quotient (MulAction.orbitRel (deck p) E)) where
  toRiemannAtlas := A.toRiemannAtlas.liftLocalHomeomorph (coveringDeckQuotientHomeomorph hp hsurj)
    (coveringDeckQuotientHomeomorph hp hsurj).isLocalHomeomorph
  t2Space := by
    let := A.t2Space
    exact (coveringDeckQuotientHomeomorph hp hsurj).symm.t2Space
  connectedSpace := inferInstance

theorem coveringDeckQuotientHomeomorph_analytic [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (A : RiemannSurface X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    RiemannAnalyticMap (coveringDeckQuotientRiemannSurface A hp hsurj).toRiemannAtlas A.toRiemannAtlas
      (coveringDeckQuotientHomeomorph hp hsurj) :=
  A.toRiemannAtlas.liftLocalHomeomorph_projection_analytic _
    (coveringDeckQuotientHomeomorph hp hsurj).isLocalHomeomorph

theorem coveringDeckQuotient_conformallyEquivalent [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (A : RiemannSurface X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    RiemannConformallyEquivalent (coveringDeckQuotientRiemannSurface A hp hsurj) A :=
  ⟨coveringDeckQuotientHomeomorph hp hsurj, coveringDeckQuotientHomeomorph_analytic A hp hsurj,
    (coveringDeckQuotientHomeomorph hp hsurj).bijective⟩

end LowDimensionalTopology.Geometry.Surfaces
