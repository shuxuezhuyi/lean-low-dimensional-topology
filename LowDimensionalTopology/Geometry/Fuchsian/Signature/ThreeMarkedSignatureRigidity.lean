/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ActualOrbifoldRigidity
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeCuspRigidity
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.MarkedGenusZeroSurfaces
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Multiplicity in the actual order list counts actual elliptic classes
of exactly that order; equal-order classes remain separate. -/
theorem fuchsianEllipticOrderList_count_eq_fiber_card
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] (m : ℕ) :
    (fuchsianEllipticOrderList D).count m =
      Nat.card {c : FuchsianCyclicConjugacyClasses D .elliptic | fuchsianEllipticClassOrder D c = m} := by
  classical
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  let e := (Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)).symm
  let f := fuchsianEllipticClassOrder D ∘ e
  have hc : (List.ofFn f).count m = Fintype.card {i | f i = m} := by
    rw [Fintype.card_subtype]
    simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn, Set.mem_ofPred_eq] using
      (Fin.card_filter_univ_eq_vector_get_eq_count m (List.Vector.ofFn f)).symm
  change (List.ofFn f).count m = _
  rw [Nat.card_eq_fintype_card]
  exact hc.trans (Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)))

/-- Equal genuine elliptic order multisets give an actual bijection of
elliptic conjugacy classes preserving each true order, with multiplicities. -/
theorem cofinite_signature_elliptic_order_equiv
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {g h p q : ℕ} {orders : List ℕ}
    (hD : HasCofiniteFuchsianSignature D g orders p)
    (hE : HasCofiniteFuchsianSignature E h orders q) :
    ∃ e : FuchsianCyclicConjugacyClasses D .elliptic ≃
        FuchsianCyclicConjugacyClasses E .elliptic,
      ∀ c, fuchsianEllipticClassOrder E (e c) = fuchsianEllipticClassOrder D c := by
  classical
  let := hD.ellipticClassesFinite
  let := hE.ellipticClassesFinite
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses E .elliptic)
  have hp : (fuchsianEllipticOrderList D).Perm (fuchsianEllipticOrderList E) :=
    hD.ellipticOrders.symm.trans hE.ellipticOrders
  have hc (m : ℕ) :
      Nat.card {c | fuchsianEllipticClassOrder D c = m} =
        Nat.card {c | fuchsianEllipticClassOrder E c = m} := by
    rw [← fuchsianEllipticOrderList_count_eq_fiber_card D m,
      ← fuchsianEllipticOrderList_count_eq_fiber_card E m]
    exact hp.count_eq m
  let ef (m : ℕ) : {c | fuchsianEllipticClassOrder D c = m} ≃
      {c | fuchsianEllipticClassOrder E c = m} :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hc m)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

/-- The actual cusp labels of equal genuine signatures are bijective. -/
theorem cofinite_signature_parabolic_class_equiv
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {g h p : ℕ} {ordersD ordersE : List ℕ}
    (hD : HasCofiniteFuchsianSignature D g ordersD p)
    (hE : HasCofiniteFuchsianSignature E h ordersE p) :
    Nonempty (FuchsianCyclicConjugacyClasses D .parabolic ≃
      FuchsianCyclicConjugacyClasses E .parabolic) := by
  classical
  let := hD.parabolicClassesFinite
  let := hE.parabolicClassesFinite
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .parabolic)
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses E .parabolic)
  exact ⟨Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← hD.cuspCount, ← hE.cuspCount])⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
open scoped OnePoint

/-- Three actual elliptic-or-cusp marks on genuine genus-zero completions
can be matched analytically, preserving an explicitly chosen bijection of
the actual classes. The analytic sphere coordinate comes from genuine
uniformization, not from the bare topological sphere homeomorphism. -/
theorem three_marked_completions_exists_analytic_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {ordersD ordersE : List ℕ} {p q : ℕ}
    (hD : HasCofiniteFuchsianSignature D 0 ordersD p)
    (hE : HasCofiniteFuchsianSignature E 0 ordersE q)
    (hthree : ordersD.length + p = 3)
    (eEll : FuchsianCyclicConjugacyClasses D .elliptic ≃ FuchsianCyclicConjugacyClasses E .elliptic)
    (ePar : FuchsianCyclicConjugacyClasses D .parabolic ≃ FuchsianCyclicConjugacyClasses E .parabolic) :
    ∃ f : FuchsianCuspCompletion D ≃ₜ FuchsianCuspCompletion E,
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas
        (fuchsianCuspCompletionRiemannSurface E).toRiemannAtlas f ∧
      ∀ m, f (fuchsianCuspCompletionMarkedPoint D m) =
        fuchsianCuspCompletionMarkedPoint E ((Equiv.sumCongr eEll ePar) m) := by
  classical
  let := hD.ellipticClassesFinite
  let := hD.parabolicClassesFinite
  let := hE.ellipticClassesFinite
  let := hE.parabolicClassesFinite
  let L := FuchsianCyclicConjugacyClasses D .elliptic ⊕ FuchsianCyclicConjugacyClasses D .parabolic
  let := Fintype.ofFinite L
  have hcard : Fintype.card L = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hD.marked_card.trans hthree
  let labels : Fin 3 ≃ L := (Fintype.equivFinOfCardEq hcard).symm
  let e := Equiv.sumCongr eEll ePar
  let mD : Fin 3 → FuchsianCuspCompletion D := fun i => fuchsianCuspCompletionMarkedPoint D (labels i)
  let mE : Fin 3 → FuchsianCuspCompletion E := fun i => fuchsianCuspCompletionMarkedPoint E (e (labels i))
  have hiD : Function.Injective mD := (fuchsianCuspCompletionMarkedPoint_injective D).comp labels.injective
  have hiE : Function.Injective mE :=
    (fuchsianCuspCompletionMarkedPoint_injective E).comp (e.injective.comp labels.injective)
  obtain ⟨d, hd, hd0, hd1, hd2⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.genus_zero_exists_normalized_analytic_coordinate
    (fuchsianCuspCompletionRiemannSurface D) hD.topologicalGenus (mD 0) (mD 1) (mD 2)
    (fun h => by have := hiD h; norm_num at this)
    (fun h => by have := hiD h; norm_num at this)
    (fun h => by have := hiD h; norm_num at this)
  obtain ⟨e, he, he0, he1, he2⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.genus_zero_exists_normalized_analytic_coordinate
    (fuchsianCuspCompletionRiemannSurface E) hE.topologicalGenus (mE 0) (mE 1) (mE 2)
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
  refine ⟨f, hf, ?_⟩
  intro m
  have hh := hm (labels.symm m)
  simpa only [mD, mE, labels.apply_symm_apply] using hh

/-- A filled analytic map matching actual elliptic and cusp labels gives
an analytic homeomorphism of the unchanged old quotients, with exactly the
same actual elliptic label correspondence. -/
theorem three_marked_old_quotients_exists_analytic_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {ordersD ordersE : List ℕ} {p q : ℕ}
    (hD : HasCofiniteFuchsianSignature D 0 ordersD p)
    (hE : HasCofiniteFuchsianSignature E 0 ordersE q)
    (hthree : ordersD.length + p = 3)
    (eEll : FuchsianCyclicConjugacyClasses D .elliptic ≃ FuchsianCyclicConjugacyClasses E .elliptic)
    (ePar : FuchsianCyclicConjugacyClasses D .parabolic ≃ FuchsianCyclicConjugacyClasses E .parabolic) :
    ∃ B : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain,
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B ∧
      ∀ c, B (fuchsianEllipticClassQuotientPoint D c) = fuchsianEllipticClassQuotientPoint E (eEll c) := by
  obtain ⟨f, hf, hmarks⟩ := three_marked_completions_exists_analytic_homeomorph
    D E hD hE hthree eEll ePar
  have hcusps : f '' range (fuchsianCuspCompletionPoint D) = range (fuchsianCuspCompletionPoint E) := by
    apply subset_antisymm
    · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨ePar c, (hmarks (Sum.inr c)).symm⟩
    · rintro _ ⟨c, rfl⟩
      refine ⟨fuchsianCuspCompletionPoint D (ePar.symm c), mem_range_self _, ?_⟩
      have he := hmarks (Sum.inr (ePar.symm c))
      change f (fuchsianCuspCompletionPoint D (ePar.symm c)) =
        fuchsianCuspCompletionPoint E (ePar (ePar.symm c)) at he
      simpa only [ePar.apply_symm_apply] using he
  let B := fuchsianCuspCompletionHomeomorph_oldRestriction D E f hcusps
  refine ⟨B, fuchsianCuspCompletionHomeomorph_oldRestriction_analytic D E f hcusps hf, ?_⟩
  intro c
  apply (fuchsianCuspCompletionOld_isOpenEmbedding E).injective
  rw [fuchsianCuspCompletionHomeomorph_oldRestriction_comm]
  exact hmarks (Sum.inl c)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- The order of an actual elliptic class is the full original stabilizer
order at every point of its actual quotient fiber. -/
theorem elliptic_quotient_mark_stabilizer_card
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (c : FuchsianCyclicConjugacyClasses D .elliptic) (z : D.domain.carrier)
    (hz : fuchsianEllipticClassQuotientPoint D c = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) = fuchsianEllipticClassOrder D c := by
  induction c using Quotient.inductionOn with
  | _ K =>
    let p := (fuchsianCyclicPointStabilizerEquiv D .elliptic).symm K
    have hK : fuchsianCyclicPointStabilizer D .elliptic p = K :=
      (fuchsianCyclicPointStabilizerEquiv D .elliptic).apply_symm_apply K
    have hp : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (fuchsianEllipticFixedPointInDisc D p) =
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z := by
      rw [← fuchsianEllipticClassQuotientPoint_of_fixed_point D p, hK]
      exact hz
    have hs : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val = K.val := congrArg Subtype.val hK
    calc
      Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val) :=
        (original_quotient_point_stabilizer_card_eq D (fuchsianEllipticFixedPointInDisc D p) z hp).symm
      _ = Nat.card K.val := congrArg (fun L : Subgroup Mobius.complexMobiusGroup => Nat.card L) hs
      _ = fuchsianEllipticClassOrder D (Quotient.mk _ K) := rfl

/-- Every unmarked old quotient value has the true full stabilizer order one. -/
theorem regular_quotient_stabilizer_card_one
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (z : D.domain.carrier)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z ∉ range (fuchsianEllipticClassQuotientPoint D)) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) = 1 := by
  have hbot : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val = ⊥ := by
    apply le_antisymm
    · intro f hf
      obtain ⟨hfH, hfix⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val f).mp hf
      change f = 1
      by_contra hfn
      apply hz
      exact (original_projection_mem_elliptic_marks_iff D z).mpr
        ⟨⟨f, hfH⟩, (fun he => hfn (congrArg Subtype.val he)), Subtype.ext hfix⟩
    · exact bot_le
  rw [hbot]
  exact Subgroup.card_bot

/-- An actual analytic marked-quotient correspondence preserving the true
elliptic class orders matches the full physical stabilizer orders at all
points, including the regular fibers. -/
theorem actual_marked_quotient_stabilizer_orders_match
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain)
    (e : FuchsianCyclicConjugacyClasses D .elliptic ≃ FuchsianCyclicConjugacyClasses E .elliptic)
    (he : ∀ c, fuchsianEllipticClassOrder E (e c) = fuchsianEllipticClassOrder D c)
    (hB : ∀ c, B (fuchsianEllipticClassQuotientPoint D c) = fuchsianEllipticClassQuotientPoint E (e c))
    (z : D.domain.carrier) (w : E.domain.carrier)
    (hzw : B (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z) = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain w) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer K w.val) := by
  by_cases hz : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z ∈ range (fuchsianEllipticClassQuotientPoint D)
  · obtain ⟨c, hc⟩ := hz
    have hw : fuchsianEllipticClassQuotientPoint E (e c) = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain w :=
      (hB c).symm.trans ((congrArg B hc).trans hzw)
    rw [elliptic_quotient_mark_stabilizer_card D c z hc,
      elliptic_quotient_mark_stabilizer_card E (e c) w hw, he c]
  · have hw : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain w ∉ range (fuchsianEllipticClassQuotientPoint E) := by
      rintro ⟨c, hc⟩
      apply hz
      refine ⟨e.symm c, B.injective ?_⟩
      rw [hB, e.apply_symm_apply, hc, hzw]
    rw [regular_quotient_stabilizer_card_one D z hz, regular_quotient_stabilizer_card_one E w hw]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- The same actual genus-zero signature with three special classes gives
an analytic equivalence of the original quotients matching the true full
ramification orders. Both the analytic map and the matching are constructed. -/
theorem same_three_marked_signature_quotient_order_equivalence
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {orders : List ℕ} {p : ℕ}
    (hD : HasCofiniteFuchsianSignature D 0 orders p)
    (hE : HasCofiniteFuchsianSignature E 0 orders p) (hthree : orders.length + p = 3) :
    ∃ B : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient E.domain,
      _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B ∧
      ∀ (z : D.domain.carrier) (w : E.domain.carrier),
        B (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z) = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection E.domain w →
          Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer K w.val) := by
  obtain ⟨e, he⟩ := cofinite_signature_elliptic_order_equiv D E hD hE
  obtain ⟨q⟩ := cofinite_signature_parabolic_class_equiv D E hD hE
  obtain ⟨B, hB, hm⟩ := three_marked_old_quotients_exists_analytic_homeomorph
    D E hD hE hthree e q
  exact ⟨B, hB, actual_marked_quotient_stabilizer_orders_match D E B e he hm⟩

/-- Genuine genus-zero three-mark signatures determine the whole original
Mobius group together with its original invariant disc, even with elliptics. -/
theorem same_three_marked_signature_mobius_conjugate
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    {orders : List ℕ} {p : ℕ}
    (hD : HasCofiniteFuchsianSignature D 0 orders p)
    (hE : HasCofiniteFuchsianSignature E 0 orders p) (hthree : orders.length + p = 3) :
    ∃ M : Mobius.complexMobiusGroup, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = K ∧ M.val '' D.carrier = E.carrier := by
  obtain ⟨B, hB, hDegree⟩ := same_three_marked_signature_quotient_order_equivalence D E hD hE hthree
  exact actual_order_preserving_quotient_equivalence_mobius_conjugate D E B hB hDegree

end LowDimensionalTopology.Geometry.Fuchsian
