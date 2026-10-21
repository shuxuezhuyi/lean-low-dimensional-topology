/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspConjugacyPaths
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.MatchedPuncturePaths
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem fuchsianCuspCompletion_old_complement_finite {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .parabolic)] :
    (range (fuchsianCuspCompletionOld D))ᶜ.Finite := by
  apply (finite_range (fuchsianCuspCompletionPoint D)).subset
  intro y hy
  obtain h|⟨c,hc⟩:=fuchsianCuspCompletion_old_or_cusp D y
  · exact False.elim (hy h)
  · exact ⟨c,hc.symm⟩

/-- Actual original Mobius quotient conjugacy extends over every true cusp of the unchanged completion. Only compactness and finitely many original cusp classes are needed. -/
theorem fuchsianCuspCompletion_conjugacy_homeomorph_exists {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [CompactSpace (FuchsianCuspCompletion D)] [Finite (FuchsianCyclicConjugacyClasses D .parabolic)] :
    ∃E:FuchsianCuspCompletion D≃ₜFuchsianCuspCompletion (D.nielsenConjugate q),
      ∀o,E (fuchsianCuspCompletionOld D o)=fuchsianCuspCompletionOld (D.nielsenConjugate q)
        (D.domain.conjugateQuotientHomeomorph q o) := by
  let F:=D.nielsenConjugate q
  let Q:=D.domain.conjugateQuotientHomeomorph q
  let I:=fuchsianCuspCompletionOld D
  let J:=fuchsianCuspCompletionOld F ∘ Q
  let :Finite (FuchsianCyclicConjugacyClasses F .parabolic):=
    fuchsianCyclicClassConjugacyEquiv_finite D .parabolic q
  let :T2Space (FuchsianCuspCompletion D):=fuchsianCuspCompletion_t2Space D
  let :T2Space (FuchsianCuspCompletion F):=fuchsianCuspCompletion_t2Space F
  let :ConnectedSpace (FuchsianCuspCompletion D):=fuchsianCuspCompletion_connectedSpace D
  let :ChartedSpace ℂ (FuchsianCuspCompletion D):=
    (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas.toChartedSpace
  let :ChartedSpace ℂ (FuchsianCuspCompletion F):=
    (fuchsianCuspCompletionRiemannSurface F).toRiemannAtlas.toChartedSpace
  have hr:range J=range (fuchsianCuspCompletionOld F):=by
    ext y
    constructor
    · rintro ⟨o,rfl⟩
      exact mem_range_self _
    · rintro ⟨o,rfl⟩
      exact ⟨Q.symm o,congrArg (fuchsianCuspCompletionOld F) (Q.apply_symm_apply o)⟩
  have hJ:Topology.IsOpenEmbedding J:=
    (fuchsianCuspCompletionOld_isOpenEmbedding F).comp Q.isOpenEmbedding
  have hB:(range J)ᶜ.Finite:=hr.symm ▸ fuchsianCuspCompletion_old_complement_finite F
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.homeomorph_of_matching_puncture_paths I J (fuchsianCuspCompletionOld_isOpenEmbedding D) hJ
    (fuchsianCuspCompletion_old_complement_finite D) hB
  intro a ha
  obtain hOld|⟨c,rfl⟩:=fuchsianCuspCompletion_old_or_cusp D a
  · exact False.elim (ha hOld)
  · obtain ⟨b,p,hp,hq⟩:=fuchsianCuspCompletion_conjugacy_matching_path D q c
    refine ⟨fuchsianCuspCompletionPoint F b,?_,fun
      n=>_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (p n),hp,?_⟩
    · rw [hr]
      exact fuchsianCuspCompletionPoint_not_mem_old F b
    · change Tendsto (fun n=>fuchsianCuspCompletionOld F
        (Q (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (p n)))) atTop (𝓝
          (fuchsianCuspCompletionPoint F b))
      apply hq.congr'
      filter_upwards [] with n
      rfl

/-- A genuine whole-group conjugacy homeomorphism of the actual all-cusp completions. -/
def fuchsianCuspCompletionConjugacyHomeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [CompactSpace (FuchsianCuspCompletion D)] [Finite (FuchsianCyclicConjugacyClasses D .parabolic)] :
    FuchsianCuspCompletion D≃ₜFuchsianCuspCompletion (D.nielsenConjugate q) :=
  (fuchsianCuspCompletion_conjugacy_homeomorph_exists D q).choose

theorem fuchsianCuspCompletionConjugacyHomeomorph_old {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [CompactSpace (FuchsianCuspCompletion D)] [Finite (FuchsianCyclicConjugacyClasses D .parabolic)]
    (o:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) :
    fuchsianCuspCompletionConjugacyHomeomorph D q (fuchsianCuspCompletionOld D o)=
      fuchsianCuspCompletionOld (D.nielsenConjugate q) (D.domain.conjugateQuotientHomeomorph q o) :=
  (fuchsianCuspCompletion_conjugacy_homeomorph_exists D q).choose_spec o

theorem fuchsianCuspCompletion_genus_global_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    [CompactSpace (FuchsianCuspCompletion D)] [Finite (FuchsianCyclicConjugacyClasses D .parabolic)]
    (g:ℕ) (h:_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D) g) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion (D.nielsenConjugate q)) g := by
  obtain ⟨E⟩:=h
  exact ⟨(fuchsianCuspCompletionConjugacyHomeomorph D q).symm.trans E⟩

/-- The whole actual cofinite signature is invariant under original global Mobius conjugacy: actual filled topology, genus, all elliptic orders with repetitions, and actual cusp count. -/
theorem cofinite_signature_global_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g p:ℕ) (orders:List ℕ)
    (h:HasCofiniteFuchsianSignature D g orders p) :
    HasCofiniteFuchsianSignature (D.nielsenConjugate q) g orders p := by
  let :Finite (FuchsianCyclicConjugacyClasses D .elliptic):=h.ellipticClassesFinite
  let :Finite (FuchsianCyclicConjugacyClasses D .parabolic):=h.parabolicClassesFinite
  let :CompactSpace (FuchsianCuspCompletion D):=h.compact
  let :Finite (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .elliptic):=
    fuchsianCyclicClassConjugacyEquiv_finite D .elliptic q
  let :Finite (FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .parabolic):=
    fuchsianCyclicClassConjugacyEquiv_finite D .parabolic q
  exact {
    ellipticClassesFinite:=inferInstance
    parabolicClassesFinite:=inferInstance
    compact:=(fuchsianCuspCompletionConjugacyHomeomorph D q).compactSpace
    topologicalGenus:=fuchsianCuspCompletion_genus_global_conjugation D q g h.topologicalGenus
    ellipticOrders:=h.ellipticOrders.trans (fuchsianEllipticOrderList_global_conjugation D q)
    cuspCount:=h.cuspCount.trans (fuchsianCyclicClassConjugacyEquiv_natCard D .parabolic q).symm
  }



/-- Original Fuchsian-disc data with the same literal carrier differ only in proofs. -/
theorem FuchsianDisc.eq_of_carrier_eq {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D E:FuchsianDisc H) (h:D.carrier=E.carrier) : D=E := by
  cases D
  cases E
  cases h
  rfl

theorem cofinite_signature_conjugation_of_carrier_eq {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (E:FuchsianDisc (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hE:E.carrier=q.val '' D.carrier) (g p:ℕ) (orders:List ℕ)
    (h:HasCofiniteFuchsianSignature D g orders p) : HasCofiniteFuchsianSignature E g orders p := by
  have he:E=D.nielsenConjugate q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.eq_of_carrier_eq E (D.nielsenConjugate q) hE
  rw [he]
  exact cofinite_signature_global_conjugation D q g p orders h

/-- A genuine group equality and the literal whole-disc image suffice to transport the original actual cofinite signature. -/
theorem cofinite_signature_of_conjugate_group {H K:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (E:FuchsianDisc K) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=K) (hE:q.val ''
      D.carrier=E.carrier)
    (g p:ℕ) (orders:List ℕ) (h:HasCofiniteFuchsianSignature D g orders p) :
    HasCofiniteFuchsianSignature E g orders p := by
  subst K
  exact cofinite_signature_conjugation_of_carrier_eq D q E hE.symm g p orders h

end LowDimensionalTopology.Geometry.Fuchsian
