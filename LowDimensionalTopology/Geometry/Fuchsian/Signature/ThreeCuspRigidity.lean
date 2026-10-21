/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSignaturePatterns
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.MarkedGenusZeroSurfaces
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures

/-!
# Three-cusp rigidity through the actual original quotients

Actual elliptic maximal-cyclic conjugacy classes embed in the old orbit
quotient. Together with the genuine added cusp points, these give distinct
physical marks on the unique cusp completion. A genus-zero signature with
three total marks therefore has a conjugation reflection fixing every mark.
The three-cusp case has no elliptic branching: its actual quotient equivalence lifts through the proved simply connected unramified covers and yields whole-group Mobius conjugacy. No lift through an elliptically branched quotient is assumed or asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- A genuine elliptic center belongs to the original physical invariant disc. -/
def fuchsianEllipticFixedPointInDisc {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : fuchsianCyclicFixedPoints D .elliptic ↪ D.domain.carrier where
  toFun p := ⟨p.val, p.property.1 rfl⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : D.domain.carrier => z.val) h

/-- The inclusion of actual elliptic centers intertwines the actual whole-group actions. -/
theorem fuchsianEllipticFixedPointInDisc_smul
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (g : H) (p : fuchsianCyclicFixedPoints D .elliptic) :
    fuchsianEllipticFixedPointInDisc D (g • p) =
      g • fuchsianEllipticFixedPointInDisc D p := rfl

/-- True maximal elliptic cyclic classes give distinct points of the original orbit quotient. -/
def fuchsianEllipticClassQuotientPoint {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    FuchsianCyclicConjugacyClasses D .elliptic ↪ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain :=
  (fuchsianCyclicConjugacyClassesEquiv D .elliptic).toEmbedding.trans
    (orbitQuotientEmbedding (fuchsianEllipticFixedPointInDisc D)
      (fuchsianEllipticFixedPointInDisc D).injective
      (fuchsianEllipticFixedPointInDisc_smul D))

/-- The physical elliptic mark in the unique all-cusp completion. -/
def fuchsianCuspCompletionEllipticPoint {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .elliptic) :
    FuchsianCuspCompletion D :=
  fuchsianCuspCompletionOld D (fuchsianEllipticClassQuotientPoint D c)

/-- Distinct actual elliptic classes give distinct physical completion points. -/
theorem fuchsianCuspCompletionEllipticPoint_injective
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Function.Injective (fuchsianCuspCompletionEllipticPoint D) :=
  (fuchsianCuspCompletionOld_isOpenEmbedding D).injective.comp
    (fuchsianEllipticClassQuotientPoint D).injective

/-- A true elliptic mark and a true cusp mark are different physical points. -/
theorem fuchsianCuspCompletionEllipticPoint_ne_cusp
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (e : FuchsianCyclicConjugacyClasses D .elliptic)
    (p : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCuspCompletionEllipticPoint D e ≠ fuchsianCuspCompletionPoint D p := by
  intro h
  exact fuchsianCuspCompletionPoint_not_mem_old D p
    ⟨fuchsianEllipticClassQuotientPoint D e, h⟩

/-- Actual elliptic and parabolic classes label the physical special points. -/
def fuchsianCuspCompletionMarkedPoint {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    FuchsianCyclicConjugacyClasses D .elliptic ⊕
      FuchsianCyclicConjugacyClasses D .parabolic → FuchsianCuspCompletion D :=
  Sum.elim (fuchsianCuspCompletionEllipticPoint D) (fuchsianCuspCompletionPoint D)

/-- All labels are distinct as physical completion points, including equal-order elliptic classes. -/
theorem fuchsianCuspCompletionMarkedPoint_injective
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Function.Injective (fuchsianCuspCompletionMarkedPoint D) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (fuchsianCuspCompletionEllipticPoint_injective D h)
    | inr b => exact (fuchsianCuspCompletionEllipticPoint_ne_cusp D a b h).elim
  | inr a =>
    cases b with
    | inl b => exact (fuchsianCuspCompletionEllipticPoint_ne_cusp D b a h.symm).elim
    | inr b => exact congrArg Sum.inr (fuchsianCuspCompletionPoint_injective D h)

/-- The total mark count is read from the independently defined actual signature. -/
theorem HasCofiniteFuchsianSignature.marked_card
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) :
    Nat.card (FuchsianCyclicConjugacyClasses D .elliptic ⊕
      FuchsianCyclicConjugacyClasses D .parabolic) = orders.length + p := by
  let := h.ellipticClassesFinite
  let := h.parabolicClassesFinite
  rw [Nat.card_sum, ← h.orders_length, ← h.cuspCount]

/-- A genuine genus-zero signature with three special classes has a physical
involutive reflection fixing every actual elliptic and cusp point. In the
constructed analytic sphere coordinate it is exactly complex conjugation. -/
theorem HasCofiniteFuchsianSignature.three_point_reflection
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {p : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D 0 orders p) (hthree : orders.length + p = 3) :
    ∃ (e : FuchsianCuspCompletion D ≃ₜ OnePoint ℂ)
      (r : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion D),
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas
        _root_.LowDimensionalTopology.Geometry.Surfaces.sphereRiemannAtlas e ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap _root_.LowDimensionalTopology.Geometry.Surfaces.sphereRiemannAtlas
        (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas e.symm ∧
      Function.Involutive r ∧
      (∀ m, r (fuchsianCuspCompletionMarkedPoint D m) =
        fuchsianCuspCompletionMarkedPoint D m) ∧
      (∀ x, e (r x) = _root_.LowDimensionalTopology.Geometry.Surfaces.sphereConjugationHomeomorph (e x)) ∧
      ∃ x, r x ≠ x := by
  classical
  let := h.ellipticClassesFinite
  let := h.parabolicClassesFinite
  let L := FuchsianCyclicConjugacyClasses D .elliptic ⊕
    FuchsianCyclicConjugacyClasses D .parabolic
  let := Fintype.ofFinite L
  have hcard : Fintype.card L = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact h.marked_card.trans hthree
  let q : Fin 3 ≃ L := (Fintype.equivFinOfCardEq hcard).symm
  let m : Fin 3 → FuchsianCuspCompletion D := fun i => fuchsianCuspCompletionMarkedPoint D (q i)
  have hi : Function.Injective m := (fuchsianCuspCompletionMarkedPoint_injective D).comp q.injective
  obtain ⟨e, r, he, hei, _ha, _hb, _hc, hr, h0, h1, h2, hcoord⟩ :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.genus_zero_exists_three_point_reflection (fuchsianCuspCompletionRiemannSurface D)
      h.topologicalGenus (m 0) (m 1) (m 2)
      (fun h => by have := hi h; norm_num at this)
      (fun h => by have := hi h; norm_num at this)
      (fun h => by have := hi h; norm_num at this)
  refine ⟨e, r, he, hei, hr, ?_, hcoord, ?_⟩
  · intro a
    have ha : a = q (q.symm a) := (q.apply_symm_apply a).symm
    rw [ha]
    change r (m (q.symm a)) = m (q.symm a)
    have hm (i : Fin 3) : r (m i) = m i := by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    exact hm (q.symm a)
  · have heq : r = _root_.LowDimensionalTopology.Geometry.Surfaces.sphereCoordinateReflection e := by
      apply Homeomorph.ext
      intro x
      apply e.injective
      rw [hcoord, _root_.LowDimensionalTopology.Geometry.Surfaces.sphereCoordinateReflection_coordinate]
    rw [heq]
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.sphereCoordinateReflection_exists_moved e

/-- Two genuine genus-zero three-cusp quotients are analytically equivalent after
filling their actual cusps, with precisely the actual added points matched. -/
theorem three_cusp_completions_exists_analytic_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3)
    (hE : HasCofiniteFuchsianSignature E 0 [] 3) :
    ∃ f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E,
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas
        (fuchsianCuspCompletionRiemannSurface E).toRiemannAtlas f ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface E).toRiemannAtlas
        (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas f.symm ∧
      f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E) := by
  classical
  let := hD.parabolicClassesFinite
  let := hE.parabolicClassesFinite
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .parabolic)
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses E .parabolic)
  let qD : Fin 3 ≃ FuchsianCyclicConjugacyClasses D .parabolic :=
    (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hD.cuspCount.symm)).symm
  let qE : Fin 3 ≃ FuchsianCyclicConjugacyClasses E .parabolic :=
    (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hE.cuspCount.symm)).symm
  let mD : Fin 3 → FuchsianCuspCompletion D := fun i => fuchsianCuspCompletionPoint D (qD i)
  let mE : Fin 3 → FuchsianCuspCompletion E := fun i => fuchsianCuspCompletionPoint E (qE i)
  have hiD : Function.Injective mD := (fuchsianCuspCompletionPoint_injective D).comp qD.injective
  have hiE : Function.Injective mE := (fuchsianCuspCompletionPoint_injective E).comp qE.injective
  obtain ⟨d, hd, hd0, hd1, hd2⟩ :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.genus_zero_exists_normalized_analytic_coordinate (fuchsianCuspCompletionRiemannSurface D)
      hD.topologicalGenus (mD 0) (mD 1) (mD 2)
      (fun h => by have := hiD h; norm_num at this)
      (fun h => by have := hiD h; norm_num at this)
      (fun h => by have := hiD h; norm_num at this)
  obtain ⟨e, he, he0, he1, he2⟩ :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.genus_zero_exists_normalized_analytic_coordinate (fuchsianCuspCompletionRiemannSurface E)
      hE.topologicalGenus (mE 0) (mE 1) (mE 2)
      (fun h => by have := hiE h; norm_num at this)
      (fun h => by have := hiE h; norm_num at this)
      (fun h => by have := hiE h; norm_num at this)
  let f := d.trans e.symm
  have hf : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas
      (fuchsianCuspCompletionRiemannSurface E).toRiemannAtlas f :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.riemannAnalyticMap_homeomorph_symm e he).comp hd
  have hm (i : Fin 3) : f (mD i) = mE i := by
    apply e.injective
    change e (e.symm (d (mD i))) = e (mE i)
    rw [e.apply_symm_apply]
    fin_cases i
    · exact hd0.trans he0.symm
    · exact hd1.trans he1.symm
    · exact hd2.trans he2.symm
  refine ⟨f, hf, _root_.LowDimensionalTopology.Geometry.Surfaces.riemannAnalyticMap_homeomorph_symm f hf, ?_⟩
  apply subset_antisymm
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨qE (qD.symm c), ?_⟩
    have hh := hm (qD.symm c)
    simpa only [mD, mE, qD.apply_symm_apply] using hh.symm
  · rintro _ ⟨c, rfl⟩
    refine ⟨fuchsianCuspCompletionPoint D (qD (qE.symm c)), mem_range_self _, ?_⟩
    have hh := hm (qE.symm c)
    simpa only [mD, mE, qE.apply_symm_apply] using hh

/-- The actual added cusp marks are precisely the complement of the original quotient. -/
theorem fuchsianCuspCompletion_old_range_eq_cusp_compl
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : range (fuchsianCuspCompletionOld D) =
      (range (fuchsianCuspCompletionPoint D))ᶜ := by
  ext x
  constructor
  · rintro hx ⟨c, rfl⟩
    exact fuchsianCuspCompletionPoint_not_mem_old D c hx
  · intro hx
    obtain h | ⟨c, rfl⟩ := fuchsianCuspCompletion_old_or_cusp D x
    · exact h
    · exact (hx (mem_range_self c)).elim

/-- A genuine filled homeomorphism matching all actual cusps preserves exactly the old quotients. -/
theorem fuchsianCuspCompletionHomeomorph_old_range
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (E : FuchsianDisc K)
    (f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E)
    (hcusps : f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E)) :
    f '' range (fuchsianCuspCompletionOld D) = range (fuchsianCuspCompletionOld E) := by
  rw [fuchsianCuspCompletion_old_range_eq_cusp_compl,
    fuchsianCuspCompletion_old_range_eq_cusp_compl, f.image_compl, hcusps]

/-- The restriction is a homeomorphism of the actual original whole-group orbit quotients. -/
def fuchsianCuspCompletionHomeomorph_oldRestriction
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (E : FuchsianDisc K)
    (f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E)
    (hcusps : f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain :=
  (fuchsianCuspCompletionOld_isOpenEmbedding D).isEmbedding.toHomeomorph.trans
    (((f.image (range (fuchsianCuspCompletionOld D))).trans
      (Homeomorph.setCongr (fuchsianCuspCompletionHomeomorph_old_range D E f hcusps))).trans
      (fuchsianCuspCompletionOld_isOpenEmbedding E).isEmbedding.toHomeomorph.symm)

/-- The restricted homeomorphism agrees with the unchanged original open embeddings. -/
theorem fuchsianCuspCompletionHomeomorph_oldRestriction_comm
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E)
    (hcusps : f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E))
    (x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) :
    fuchsianCuspCompletionOld E (fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps x) =
      f (fuchsianCuspCompletionOld D x) := by
  exact congrArg Subtype.val
    ((fuchsianCuspCompletionOld_isOpenEmbedding E).isEmbedding.toHomeomorph.apply_symm_apply _)

/-- Restricting an analytic filled homeomorphism preserves the original quotient complex structures. -/
theorem fuchsianCuspCompletionHomeomorph_oldRestriction_analytic
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E)
    (hcusps : f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E))
    (hf : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas
      (fuchsianCuspCompletionRiemannSurface E).toRiemannAtlas f) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas
      (fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps) := by
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph (fuchsianCuspCompletionOld_analytic E)
    (fuchsianCuspCompletionOld_isOpenEmbedding E).isLocalHomeomorph
    (fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps).continuous
  have hfun : fuchsianCuspCompletionOld E ∘
      fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps =
      f ∘ fuchsianCuspCompletionOld D :=
    funext (fuchsianCuspCompletionHomeomorph_oldRestriction_comm D E f hcusps)
  rw [hfun]
  exact hf.comp (fuchsianCuspCompletionOld_analytic D)

/-- The original three-cusp quotients, not just their compactifications, are analytically equivalent. -/
theorem three_cusp_quotients_exists_analytic_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3)
    (hE : HasCofiniteFuchsianSignature E 0 [] 3) :
    ∃ f : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain,
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas f ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas f.symm := by
  obtain ⟨f, hf, _hfi, hcusps⟩ := three_cusp_completions_exists_analytic_homeomorph D E hD hE
  let e := fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps
  have he := fuchsianCuspCompletionHomeomorph_oldRestriction_analytic D E f hcusps hf
  exact ⟨e, he, _root_.LowDimensionalTopology.Geometry.Surfaces.riemannAnalyticMap_homeomorph_symm e he⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A homeomorphism of bases lifts to a homeomorphism of simply connected covers,
with the chosen physical base-point lift. Both inverses follow from uniqueness of lifts. -/
theorem simplyConnectedCover_exists_homeomorph_over
    {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace F]
    {p : E → X} {q : F → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (B : X ≃ₜ Y) (a : E) (b : F) (hab : q b = B (p a)) :
    ∃ e : E ≃ₜ F, e a = b ∧ ∀ z, q (e z) = B (p z) := by
  obtain ⟨f, ⟨hfa, hqf⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    ⟨B ∘ p, B.continuous.comp hp.continuous⟩ a b hab
  obtain ⟨g, ⟨hgb, hpg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨B.symm ∘ q, B.symm.continuous.comp hq.continuous⟩ b a
      (by change p a = B.symm (q b); rw [hab, B.symm_apply_apply])
  have hqf' (z : E) : q (f z) = B (p z) := congrFun hqf z
  have hpg' (z : F) : p (g z) = B.symm (q z) := congrFun hpg z
  have hgf : (g ∘ f : E → E) = id := by
    apply hp.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id _ a
      (by simp [hfa, hgb])
    funext z
    change p (g (f z)) = p z
    rw [hpg', hqf', B.symm_apply_apply]
  have hfg : (f ∘ g : F → F) = id := by
    apply hq.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id _ b
      (by simp [hfa, hgb])
    funext z
    change q (f (g z)) = q z
    rw [hqf', hpg', B.apply_symm_apply]
  let e : E ≃ₜ F :=
    { toFun := f
      invFun := g
      left_inv := fun z => congrFun hgf z
      right_inv := fun z => congrFun hfg z
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact ⟨e, hfa, fun z => congrFun hqf z⟩

/-- For genuine analytic covering projections, the lifted homeomorphism is
analytic in the original atlases and its actual inverse is analytic too. -/
theorem analytic_simplyConnectedCover_exists_homeomorph_over
    {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace F]
    (A : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas E)
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas F)
    (U : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas X)
    (V : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas Y)
    {p : E → X} {q : F → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hap : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap A U p)
    (haq : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap C V q)
    (B : X ≃ₜ Y) (hB : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap U V B)
    (a : E) (b : F) (hab : q b = B (p a)) :
    ∃ e : E ≃ₜ F, e a = b ∧ (∀ z, q (e z) = B (p z)) ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap A C e ∧ _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap C A e.symm := by
  obtain ⟨e, he, hcomm⟩ := simplyConnectedCover_exists_homeomorph_over hp hq B a b hab
  have hea : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap A C e := by
    apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph haq hq.isLocalHomeomorph e.continuous
    have hfun : q ∘ e = B ∘ p := funext hcomm
    rw [hfun]
    exact hB.comp hap
  exact ⟨e, he, hcomm, hea, _root_.LowDimensionalTopology.Geometry.Surfaces.riemannAnalyticMap_homeomorph_symm e hea⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The physical invariant disc, not an auxiliary path-space model, is simply connected. -/
theorem fuchsianDisc_domain_simplyConnected
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : SimplyConnectedSpace D.domain.carrier := by
  obtain ⟨q, hq⟩ := D.isDisc.normalize
  let e : D.domain.carrier ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
    ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image D.carrier).trans (Homeomorph.setCongr hq)
  exact e.toHomotopyEquiv.simplyConnectedSpace_iff.mpr _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface_simplyConnected

/-- An empty actual elliptic order list forces the actual original group to be elliptic-free. -/
theorem HasCofiniteFuchsianSignature.no_elliptic_of_nil
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H} {g p : ℕ}
    (h : HasCofiniteFuchsianSignature D g [] p) : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  let := h.ellipticClassesFinite
  have hnil : fuchsianEllipticOrderList D = [] :=
    List.eq_nil_of_length_eq_zero (by rw [← h.ellipticOrders.length_eq]; rfl)
  exact (fuchsianEllipticOrderList_eq_nil_iff D).mp hnil

/-- The genuine analytic equivalence of three-cusp quotients lifts all the way to
an analytic homeomorphism of the original physical invariant discs. -/
theorem three_cusp_domains_exists_analytic_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3)
    (hE : HasCofiniteFuchsianSignature E 0 [] 3) :
    ∃ (b : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain)
      (e : D.domain.carrier ≃ₜ E.domain.carrier),
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas e ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas e.symm ∧
      ∀ z, _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain (e z) = b (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z) := by
  let RD := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain
  let RE := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface E.domain
  let := fuchsianDisc_domain_simplyConnected D
  let := fuchsianDisc_domain_simplyConnected E
  let := RD.toRiemannAtlas.locallyPathConnectedSpace
  let := RE.toRiemannAtlas.locallyPathConnectedSpace
  let := RD.connectedSpace
  let a : D.domain.carrier := Classical.choice inferInstance
  obtain ⟨b, hb, _⟩ := three_cusp_quotients_exists_analytic_homeomorph D E hD hE
  obtain ⟨c, hc⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_surjective E.domain (b (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain a))
  have hpD := (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering D.domain D.discontinuous
    (fun f hf _ => hD.no_elliptic_of_nil f hf)).isCoveringMap
  have hpE := (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering E.domain E.discontinuous
    (fun f hf _ => hE.no_elliptic_of_nil f hf)).isCoveringMap
  obtain ⟨e, _he, hcomm, hea, hei⟩ := analytic_simplyConnectedCover_exists_homeomorph_over
    RD.toRiemannAtlas RE.toRiemannAtlas
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas hpD hpE
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_analytic D.domain D.discontinuous)
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_analytic E.domain E.discontinuous) b hb a c hc
  exact ⟨b, e, hea, hei, hcomm⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An actual normalizer gives a physical analytic coordinate on the invariant disc. -/
def fuchsianDiscUnitHomeomorph
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    D.domain.carrier ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
  ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image D.carrier).trans (Homeomorph.setCongr hq)

theorem fuchsianDiscUnitHomeomorph_coe
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (z : D.domain.carrier) :
    (fuchsianDiscUnitHomeomorph D q hq z).val = q.val z.val := rfl

theorem fuchsianDiscUnitHomeomorph_analytic
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
      _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface.toRiemannAtlas (fuchsianDiscUnitHomeomorph D q hq) := by
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph Subtype.val Subtype.val
    D.isDisc.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    _root_.LowDimensionalTopology.Geometry.Mobius.isOpen_extendedUnitDisc.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    q.val (fuchsianDiscUnitHomeomorph D q hq) (_root_.LowDimensionalTopology.Geometry.Surfaces.mobius_riemannSphere_analytic q)
    (fuchsianDiscUnitHomeomorph D q hq).continuous (fun _ => rfl)

/-- Agreement on an arbitrary physical invariant disc determines an actual Mobius map. -/
theorem mobius_eq_of_agree_fuchsianDisc {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (M N : Mobius.complexMobiusGroup)
    (h : ∀ z : D.domain.carrier, M.val z.val = N.val z.val) : M = N := by
  obtain ⟨q, hq⟩ := D.isDisc.normalize
  let d := fuchsianDiscUnitHomeomorph D q hq
  have hpre (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : q.val.symm z.val = (d.symm z).val := by
    apply q.val.injective
    rw [Equiv.apply_symm_apply]
    change z.val = q.val (d.symm z).val
    exact (congrArg (fun w : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc => w.val) (d.apply_symm_apply z)).symm
  have hmul : M * q⁻¹ = N * q⁻¹ := by
    apply _root_.LowDimensionalTopology.Geometry.Surfaces.mobius_eq_of_agree_extendedUnitDisc
    intro z
    change M.val (q.val.symm z.val) = N.val (q.val.symm z.val)
    rw [hpre]
    exact h (d.symm z)
  exact mul_right_cancel hmul

/-- An analytic homeomorphism of two actual invariant discs is the restriction of
one genuine whole-sphere Mobius map, with the whole-disc image equality. -/
theorem analytic_fuchsianDisc_homeomorph_exists_mobius
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (f : D.domain.carrier ≃ₜ E.domain.carrier)
    (hf : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas f) :
    ∃ M : Mobius.complexMobiusGroup, M.val '' D.carrier = E.carrier ∧
      ∀ z : D.domain.carrier, M.val z.val = (f z).val := by
  obtain ⟨qD, hD⟩ := D.isDisc.normalize
  obtain ⟨qE, hE⟩ := E.isDisc.normalize
  let d := fuchsianDiscUnitHomeomorph D qD hD
  let e := fuchsianDiscUnitHomeomorph E qE hE
  have hd := fuchsianDiscUnitHomeomorph_analytic D qD hD
  have he := fuchsianDiscUnitHomeomorph_analytic E qE hE
  let g := d.symm.trans (f.trans e)
  have hg : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface.toRiemannAtlas
      _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface.toRiemannAtlas g :=
    he.comp (hf.comp (_root_.LowDimensionalTopology.Geometry.Surfaces.riemannAnalyticMap_homeomorph_symm d hd))
  obtain ⟨N, _hNpres, hN⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface_automorphism_exists_mobius g hg
  let M := qE⁻¹ * N * qD
  have hM (z : D.domain.carrier) : M.val z.val = (f z).val := by
    calc
      M.val z.val = qE.val.symm (N.val (d z).val) := rfl
      _ = qE.val.symm (e (f z)).val := by
        rw [hN]
        simp only [g, Homeomorph.trans_apply, d.symm_apply_apply]
      _ = (f z).val := by
        change qE.val.symm (qE.val (f z).val) = (f z).val
        exact Equiv.symm_apply_apply _ _
  refine ⟨M, ?_, hM⟩
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [hM ⟨z, hz⟩]
    exact (f ⟨z, hz⟩).property
  · intro z hz
    refine ⟨(f.symm ⟨z, hz⟩).val, (f.symm ⟨z, hz⟩).property, ?_⟩
    rw [hM, f.apply_symm_apply]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A physical Mobius self-map which is a deck map of an elliptic-free original
disc quotient belongs to the original whole group. -/
theorem mobius_mem_of_original_quotient_action
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hno : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (M : Mobius.complexMobiusGroup) (f : D.domain.carrier → D.domain.carrier)
    (hf : Continuous f) (hM : ∀ z, M.val z.val = (f z).val)
    (hproj : ∀ z, _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (f z) = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z) :
    M ∈ H := by
  let RD := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainRiemannSurface D.domain
  let := RD.connectedSpace
  let a : D.domain.carrier := Classical.choice inferInstance
  obtain ⟨g, hg⟩ := Quotient.exact (hproj a)
  have hp := (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering D.domain D.discontinuous
    (fun f hf _ => hno f hf)).isCoveringMap
  have heq : f = (fun z => g • z) := by
    apply hp.eq_of_comp_eq hf (continuous_const_smul g) _ a hg.symm
    funext z
    exact (hproj z).trans (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_smul D.domain g z).symm
  have hMg : M = g.val := by
    apply mobius_eq_of_agree_fuchsianDisc D
    intro z
    exact (hM z).trans (congrArg Subtype.val (congrFun heq z))
  exact hMg.symm ▸ g.property

/-- A quotient-intertwining physical Mobius map carries every whole-group
element into the whole target group, without choosing a deck representation as a hypothesis. -/
theorem original_quotient_mobius_conjugate_mem
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hnoE : ∀ f ∈ K, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (e : D.domain.carrier ≃ₜ E.domain.carrier)
    (B : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain)
    (M : Mobius.complexMobiusGroup)
    (hM : ∀ z : D.domain.carrier, M.val z.val = (e z).val)
    (hcomm : ∀ z, _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain (e z) = B (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z))
    (g : H) : M * g.val * M⁻¹ ∈ K := by
  have hMi (z : E.domain.carrier) : M.val.symm z.val = (e.symm z).val := by
    apply M.val.injective
    rw [Equiv.apply_symm_apply, hM, e.apply_symm_apply]
  let f : E.domain.carrier → E.domain.carrier := fun z => e (g • e.symm z)
  apply mobius_mem_of_original_quotient_action E hnoE (M * g.val * M⁻¹) f
    (e.continuous.comp ((continuous_const_smul g).comp e.symm.continuous))
  · intro z
    change M.val (g.val.val (M.val.symm z.val)) = (e (g • e.symm z)).val
    rw [hMi]
    exact hM (g • e.symm z)
  · intro z
    change _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain (e (g • e.symm z)) = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain z
    rw [hcomm, _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_smul, ← hcomm, e.apply_symm_apply]

/-- A physical Mobius equivalence over the actual elliptic-free quotients
conjugates the entire original groups, not merely a selected generating pair. -/
theorem original_quotient_mobius_group_conjugacy
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hnoD : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (hnoE : ∀ f ∈ K, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (e : D.domain.carrier ≃ₜ E.domain.carrier)
    (B : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain)
    (M : Mobius.complexMobiusGroup)
    (hM : ∀ z : D.domain.carrier, M.val z.val = (e z).val)
    (hcomm : ∀ z, _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain (e z) = B (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = K := by
  have hMi (z : E.domain.carrier) : (M⁻¹).val z.val = (e.symm z).val := by
    apply M.val.injective
    change M.val (M.val.symm z.val) = M.val (e.symm z).val
    rw [Equiv.apply_symm_apply, hM, e.apply_symm_apply]
  have hback (z : E.domain.carrier) :
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (e.symm z) = B.symm (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain z) := by
    apply B.injective
    rw [B.apply_symm_apply, ← hcomm, e.apply_symm_apply]
  apply le_antisymm
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M H f).mp hf
    exact original_quotient_mobius_conjugate_mem D E hnoE e B M hM hcomm ⟨g, hg⟩
  · intro f hf
    have hin := original_quotient_mobius_conjugate_mem E D hnoD e.symm B.symm M⁻¹ hMi hback ⟨f, hf⟩
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M H f).mpr
      ⟨M⁻¹ * f * M, by simpa only [inv_inv] using hin, by group⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped UpperHalfPlane

/-- Any two original three-cusp genus-zero groups are conjugate by a genuine
whole Mobius map which also carries the entire original invariant discs onto each other. -/
theorem three_cusp_actual_groups_mobius_conjugate
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3)
    (hE : HasCofiniteFuchsianSignature E 0 [] 3) :
    ∃ M : Mobius.complexMobiusGroup, M.val '' D.carrier = E.carrier ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = K := by
  obtain ⟨B, e, he, _hei, hcomm⟩ := three_cusp_domains_exists_analytic_homeomorph D E hD hE
  obtain ⟨M, hMD, hM⟩ := analytic_fuchsianDisc_homeomorph_exists_mobius D E e he
  exact ⟨M, hMD, original_quotient_mobius_group_conjugacy D E
    hD.no_elliptic_of_nil hE.no_elliptic_of_nil e B M hM hcomm⟩

/-- The reverse triangle characterization for the genuine three-cusp signature:
the original whole group is conjugate to the actual three-ideal-triangle group. -/
theorem three_cusp_signature_conjugate_three_ideal_triangle
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3) :
    ∃ M : Mobius.complexMobiusGroup,
      M.val '' D.carrier = (closedTriangleMobiusData threeIdealStandardTriangle
        (Or.inl threeIdealStandardTriangle_angles.1)
        (Or.inl threeIdealStandardTriangle_angles.2.1)
        (Or.inl threeIdealStandardTriangle_angles.2.2)).asFuchsianDisc.carrier ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = closedTriangleMobiusGroup threeIdealStandardTriangle := by
  let P := closedTriangleMobiusData threeIdealStandardTriangle
    (Or.inl threeIdealStandardTriangle_angles.1)
    (Or.inl threeIdealStandardTriangle_angles.2.1)
    (Or.inl threeIdealStandardTriangle_angles.2.2)
  have hP := closedTriangle_actual_signature_three_ideal threeIdealStandardTriangle
    threeIdealStandardTriangle_angles.1 threeIdealStandardTriangle_angles.2.1
    threeIdealStandardTriangle_angles.2.2 P
  exact three_cusp_actual_groups_mobius_conjugate D P.asFuchsianDisc hD hP

/-- The original actual group with genuine signature `(0:infinity,infinity,infinity)`
is a geometric Mobius triangle group; no geometric model is supplied as a hypothesis. -/
theorem three_cusp_signature_isMobiusTriangleGroup
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hD : HasCofiniteFuchsianSignature D 0 [] 3) : IsMobiusTriangleGroup H := by
  obtain ⟨M, _hD, hM⟩ := three_cusp_signature_conjugate_three_ideal_triangle D hD
  refine ⟨triangleConformalGroup threeIdealStandardTriangle, inf_le_right, ?_, M, hM⟩
  refine ⟨⊤, ⊤, ⊤, by simp, by simp, by simp, threeIdealStandardTriangle, ?_, ?_, ?_, rfl⟩
  · rw [triangleOrderAngle_top]
    exact threeIdealStandardTriangle_angles.1
  · rw [triangleOrderAngle_top]
    exact threeIdealStandardTriangle_angles.2.1
  · rw [triangleOrderAngle_top]
    exact threeIdealStandardTriangle_angles.2.2

end LowDimensionalTopology.Geometry.Fuchsian
