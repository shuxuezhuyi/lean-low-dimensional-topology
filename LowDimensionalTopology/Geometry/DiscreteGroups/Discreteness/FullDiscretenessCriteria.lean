/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.Full.FullIsometryGroups
public import LowDimensionalTopology.Geometry.Mobius.Dynamics.EllipticFixedPoints
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- Elliptic means the actual positive-Jacobian elliptic type inside the full group.
Geodesic reflections retain their orientation-reversing type. -/
def FullMobiusElliptic (f : Mobius.complexGeneralMobiusGroup) : Prop:=
  ∃g : Mobius.complexMobiusGroup,Mobius.complexMobiusToFull g=f ∧ Mobius.MobiusElliptic g

def fullEllipticFixedPointSet (H : Subgroup Mobius.complexGeneralMobiusGroup) : Set Mobius.ExtendedComplex:=
  {z | ∃g : H,FullMobiusElliptic g.val ∧ g.val.val z=z}

def FullEllipticFixedPointsNonaccumulating (H : Subgroup Mobius.complexGeneralMobiusGroup) (D : Set
    Mobius.ExtendedComplex) : Prop:=
  ∀z∈D,¬AccPt z (𝓟 (fullEllipticFixedPointSet H))

def FullEllipticsNonaccumulatingAtIdentity (H : Subgroup Mobius.complexGeneralMobiusGroup) : Prop:=
  ∀ᶠf in 𝓝 (1 : Mobius.complexGeneralMobiusGroup),f∈H → ¬FullMobiusElliptic f

def FullEllipticsFiniteOrder (H : Subgroup Mobius.complexGeneralMobiusGroup) : Prop:=
  ∀g∈H,FullMobiusElliptic g → IsOfFinOrder g

def FullAllCyclicSubgroupsDiscrete (H : Subgroup Mobius.complexGeneralMobiusGroup) : Prop:=
  ∀g∈H,DiscreteTopology (Subgroup.zpowers g)

def IsFullMobiusDiscontinuousOn (H : Subgroup Mobius.complexGeneralMobiusGroup) (D : Set Mobius.ExtendedComplex) :
    Prop:=
  ∀K : Set Mobius.ExtendedComplex,IsCompact K → K⊆D →
    {g : H | ((g.val.val '' K)∩K).Nonempty}.Finite

/-- Both group models use exactly the same genuine ambient topology on the actual positive part. -/
theorem full_discrete_iff_positivePart (H : Subgroup Mobius.complexGeneralMobiusGroup) :
    DiscreteTopology H ↔ Mobius.IsDiscreteMobiusSubgroup (Mobius.fullGroupPositivePart H) := by
  exact (Subgroup.discreteTopology_iff_of_finiteIndex (H:=Mobius.fullGroupPositiveKernel H)).symm.trans
    (Mobius.fullGroupPositivePartHomeomorph H).discreteTopology_iff.symm

theorem full_positivePart_invariantDisc (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D)
    (hinv : ∀f : H,f.val.val '' D=D) : Mobius.HasInvariantComplexDisc (Mobius.fullGroupPositivePart H):=
  ⟨D,hD,fun f=>hinv ⟨Mobius.complexMobiusToFull f.val,f.property⟩⟩

theorem full_ellipticsFiniteOrder_iff_positivePart (H : Subgroup Mobius.complexGeneralMobiusGroup) :
    FullEllipticsFiniteOrder H ↔ EllipticsFiniteOrder (Mobius.fullGroupPositivePart H) := by
  constructor
  · intro h g hg he
    have hf:=h (Mobius.complexMobiusToFull g) hg ⟨g,rfl,he⟩
    have ho:=orderOf_injective Mobius.complexMobiusToFull Mobius.complexMobiusToFull_isometry.injective g
    apply orderOf_pos_iff.mp
    simpa only [ho] using hf.orderOf_pos
  · intro h f hf he
    obtain ⟨g,rfl,hge⟩:=he
    exact Mobius.complexMobiusToFull.isOfFinOrder (h g hf hge)

/-- The full group's true elliptic fixed set is exactly that of its actual conformal part. -/
theorem fullEllipticFixedPointSet_eq_positivePart (H : Subgroup Mobius.complexGeneralMobiusGroup) :
    fullEllipticFixedPointSet H=ellipticFixedPointSet (Mobius.fullGroupPositivePart H) := by
  ext z
  constructor
  · rintro ⟨f,⟨g,hgf,he⟩,hfz⟩
    have hg : g∈Mobius.fullGroupPositivePart H:=by change Mobius.complexMobiusToFull g∈H;rw [hgf];exact f.property
    refine ⟨⟨g,hg⟩,he,?_⟩
    have hgv:=congrArg (fun u : Mobius.complexGeneralMobiusGroup=>u.val z) hgf
    exact hgv.trans hfz
  · rintro ⟨g,he,hgz⟩
    exact ⟨⟨Mobius.complexMobiusToFull g.val,g.property⟩,⟨g.val,rfl,he⟩,hgz⟩

theorem full_fixedPointsNonaccumulating_iff_positivePart (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (D : Set Mobius.ExtendedComplex) :
    FullEllipticFixedPointsNonaccumulating H D ↔
      EllipticFixedPointsNonaccumulating (Mobius.fullGroupPositivePart H) D := by
  unfold FullEllipticFixedPointsNonaccumulating EllipticFixedPointsNonaccumulating
  rw [fullEllipticFixedPointSet_eq_positivePart]

/-- The actual finite-index adapter proves (5) to (1) for the full geometric group. -/
theorem FullEllipticsFiniteOrder.discrete {H : Subgroup Mobius.complexGeneralMobiusGroup}
    (hE : FullEllipticsFiniteOrder H) (hH : Mobius.IsFullNonElementary H)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D) (hinv : ∀f : H,f.val.val '' D=D) :
    DiscreteTopology H := by
  apply (full_discrete_iff_positivePart H).mpr
  exact ((full_ellipticsFiniteOrder_iff_positivePart H).mp hE).discrete hH.positivePart
    (full_positivePart_invariantDisc H D hD hinv)

theorem full_discrete_ellipticsFiniteOrder (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (hd : DiscreteTopology H) : FullEllipticsFiniteOrder H := by
  apply (full_ellipticsFiniteOrder_iff_positivePart H).mpr
  exact discrete_elliptic_finiteOrder _ ((full_discrete_iff_positivePart H).mp hd)

theorem FullEllipticFixedPointsNonaccumulating.ellipticsFiniteOrder
    {H : Subgroup Mobius.complexGeneralMobiusGroup} (hH : Mobius.IsFullNonElementary H)
    {D : Set Mobius.ExtendedComplex} (hD : Mobius.IsComplexOpenDisc D) (hinv : ∀f : H,f.val.val '' D=D)
    (h : FullEllipticFixedPointsNonaccumulating H D) : FullEllipticsFiniteOrder H := by
  apply (full_ellipticsFiniteOrder_iff_positivePart H).mpr
  exact DiscreteGroups.EllipticFixedPointsNonaccumulating.ellipticsFiniteOrder hH.positivePart hD
    (fun f=>hinv ⟨Mobius.complexMobiusToFull f.val,f.property⟩)
    ((full_fixedPointsNonaccumulating_iff_positivePart H D).mp h)

theorem FullEllipticsNonaccumulatingAtIdentity.positivePart {H : Subgroup Mobius.complexGeneralMobiusGroup}
    (h : FullEllipticsNonaccumulatingAtIdentity H) :
    EllipticsNonaccumulatingAtIdentity (Mobius.fullGroupPositivePart H) := by
  have ht : Tendsto Mobius.complexMobiusToFull (𝓝 1) (𝓝 1):=by
    simpa only [map_one] using Mobius.complexMobiusToFull_isometry.continuous.continuousAt.tendsto (x:=1)
  filter_upwards [ht.eventually h] with g hg hgH hge
  exact hg hgH ⟨g,rfl,hge⟩

theorem FullEllipticsNonaccumulatingAtIdentity.ellipticsFiniteOrder {H : Subgroup Mobius.complexGeneralMobiusGroup}
    (h : FullEllipticsNonaccumulatingAtIdentity H) : FullEllipticsFiniteOrder H :=
  (full_ellipticsFiniteOrder_iff_positivePart H).mpr h.positivePart.ellipticsFiniteOrder

theorem full_discrete_ellipticsNonaccumulatingAtIdentity (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (hd : DiscreteTopology H) : FullEllipticsNonaccumulatingAtIdentity H := by
  obtain ⟨U,hU,hUH⟩:=(isDiscrete_iff_forall_mem_exists_isOpen.mp
    (isDiscrete_iff_discreteTopology.mpr hd)) 1 H.one_mem
  have h1 : (1 : Mobius.complexGeneralMobiusGroup)∈U:=((hUH.symm ▸ (mem_singleton 1))).1
  filter_upwards [hU.mem_nhds h1] with f hf hfH hfe
  have he : f=1:=Set.mem_singleton_iff.mp (hUH ▸ ⟨hf,hfH⟩)
  obtain ⟨g,hgf,hge⟩:=hfe
  have hg1 : g=1:=Mobius.complexMobiusToFull_isometry.injective (hgf.trans (he.trans
    Mobius.complexMobiusToFull.map_one.symm))
  exact hge.1 hg1

theorem full_positivePart_zpowers (g : Mobius.complexMobiusGroup) :
    Mobius.fullGroupPositivePart (Subgroup.zpowers (Mobius.complexMobiusToFull g))=Subgroup.zpowers g := by
  ext f
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,Mobius.complexMobiusToFull_isometry.injective (by rw [map_zpow];exact hn)⟩
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    change Mobius.complexMobiusToFull g^n=Mobius.complexMobiusToFull f
    have hn' : g^n=f:=hn
    rw [←map_zpow,hn']

theorem FullAllCyclicSubgroupsDiscrete.ellipticsFiniteOrder {H : Subgroup Mobius.complexGeneralMobiusGroup}
    (h : FullAllCyclicSubgroupsDiscrete H) : FullEllipticsFiniteOrder H := by
  intro f hf hfe
  obtain ⟨g,rfl,hge⟩:=hfe
  have hd :=(full_discrete_iff_positivePart (Subgroup.zpowers (Mobius.complexMobiusToFull g))).mp (h _ hf)
  rw [full_positivePart_zpowers] at hd
  exact Mobius.complexMobiusToFull.isOfFinOrder
    (discrete_elliptic_finiteOrder (Subgroup.zpowers g) hd g (Subgroup.mem_zpowers g) hge)

theorem full_discrete_allCyclicSubgroupsDiscrete (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (hd : DiscreteTopology H) : FullAllCyclicSubgroupsDiscrete H := by
  intro g hg
  apply isDiscrete_iff_discreteTopology.mp
  exact (isDiscrete_iff_discreteTopology.mpr hd).mono (Subgroup.zpowers_le.mpr hg)

/-- A genuinely discontinuous finite-index action stays discontinuous in the full group.
All compact sets are enlarged by the actual inverse translates of genuine coset representatives. -/
theorem discontinuous_of_finiteIndex {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (K : Subgroup G) [K.FiniteIndex] (hcont : ∀g : G,Continuous (fun x : X=>g • x))
    (hK : DiscreteGroups.Action.IsDiscontinuous K X) : DiscreteGroups.Action.IsDiscontinuous G X := by
  intro B hB
  let T : G ⧸ K → Set X:=fun q=>B∪(fun x=>q.out⁻¹ • x) '' B
  have hT (q : G ⧸ K) : IsCompact (T q):=hB.union (hB.image (hcont q.out⁻¹))
  have hfinite : (⋃q : G ⧸ K,(fun k : K=>q.out*k.val) ''
      {k : K | (((k • · : X → X) '' T q)∩T q).Nonempty}).Finite:=
    Set.finite_iUnion fun q=>(hK (T q) (hT q)).image _
  apply hfinite.subset
  rintro g ⟨_,⟨x,hx,rfl⟩,hgx⟩
  let q : G ⧸ K:=QuotientGroup.mk g
  have hk : q.out⁻¹*g∈K:=QuotientGroup.eq.mp (Quotient.out_eq' q)
  let k : K:=⟨q.out⁻¹*g,hk⟩
  refine mem_iUnion.mpr ⟨q,⟨k,?_,?_⟩⟩
  · refine ⟨k • x,⟨x,Or.inl hx,rfl⟩,Or.inr ⟨g • x,hgx,?_⟩⟩
    change q.out⁻¹ • (g • x)=(q.out⁻¹*g) • x
    exact (mul_smul _ _ _).symm
  · change q.out*(q.out⁻¹*g)=g
    simp only [mul_inv_cancel_left]

/-- The genuine ambient compact-hit condition is exactly discontinuity of the actual restricted action. -/
theorem isFullMobiusDiscontinuousOn_iff_subtype (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : ∀(g : H) x,x∈S → g • x∈S) :
    IsFullMobiusDiscontinuousOn H S ↔
      @DiscreteGroups.Action.IsDiscontinuous H S _ _ (DiscreteGroups.Action.invariantSubsetMulAction S hS) := by
  let fullInvariantAction : MulAction H S:=DiscreteGroups.Action.invariantSubsetMulAction S hS
  constructor
  · intro h K hK
    refine (h (Subtype.val '' K) (hK.image continuous_subtype_val) (by
      rintro _ ⟨x,_,rfl⟩;exact x.property)).subset ?_
    rintro g ⟨_,⟨x,hx,rfl⟩,hgx⟩
    exact ⟨g • x.val,⟨x.val,⟨x,hx,rfl⟩,rfl⟩,g • x,hgx,rfl⟩
  · intro h K hK hKS
    have hkr : K⊆range (Subtype.val : S → Mobius.ExtendedComplex):=by
      simpa only [Subtype.range_coe] using hKS
    have hL : IsCompact (Subtype.val ⁻¹' K : Set S):=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hkr
    refine (h (Subtype.val ⁻¹' K) hL).subset ?_
    rintro g ⟨_,⟨x,hx,rfl⟩,hgx⟩
    exact ⟨g • (⟨x,hKS hx⟩ : S),⟨⟨x,hKS hx⟩,hx,rfl⟩,hgx⟩

theorem IsFullMobiusDiscontinuousOn.positivePart {H : Subgroup Mobius.complexGeneralMobiusGroup}
    {D : Set Mobius.ExtendedComplex} (h : IsFullMobiusDiscontinuousOn H D) :
    IsMobiusDiscontinuousOn (Mobius.fullGroupPositivePart H) D := by
  intro K hK hKD
  let ι : Mobius.fullGroupPositivePart H → H:=fun f=>(Mobius.fullGroupPositivePartEquiv H f).val
  have hι : Function.Injective ι:=by
    intro f g he
    apply (Mobius.fullGroupPositivePartEquiv H).injective
    exact Subtype.ext he
  have hf:=(h K hK hKD).preimage hι.injOn
  apply hf.subset
  intro f hf
  exact hf

theorem full_discontinuous_discrete (H : Subgroup Mobius.complexGeneralMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D)
    (hinv : ∀f : H,f.val.val '' D=D) (h : IsFullMobiusDiscontinuousOn H D) : DiscreteTopology H := by
  apply (full_discrete_iff_positivePart H).mpr
  have hpos:=DiscreteGroups.IsFullMobiusDiscontinuousOn.positivePart h
  apply isMobiusDiscontinuousOn_invariant_discrete (Mobius.fullGroupPositivePart H) D _
    hD.isConnected.nonempty hpos
  intro g z hz
  rw [←hinv ⟨Mobius.complexMobiusToFull g.val,g.property⟩]
  exact mem_image_of_mem _ hz

/-- Full discreteness gives the actual compact-hit action, including all orientation-reversing elements. -/
theorem full_discrete_discontinuous (H : Subgroup Mobius.complexGeneralMobiusGroup) (hH : Mobius.IsFullNonElementary H)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D) (hinv : ∀f : H,f.val.val '' D=D)
    (hd : DiscreteTopology H) : IsFullMobiusDiscontinuousOn H D := by
  have hi : ∀(g : H) x,x∈D → g • x∈D:=by
    intro g x hx
    rw [←hinv g]
    exact mem_image_of_mem _ hx
  have hip : ∀(g : Mobius.fullGroupPositivePart H) x,x∈D → g • x∈D:=by
    intro g x hx
    exact hi ⟨Mobius.complexMobiusToFull g.val,g.property⟩ x hx
  let fullInvariantAction : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hi
  let positiveInvariantAction : MulAction (Mobius.fullGroupPositivePart H)
    D:=DiscreteGroups.Action.invariantSubsetMulAction D hip
  have hpos : IsMobiusDiscontinuousOn (Mobius.fullGroupPositivePart H) D:=
    (discrete_iff_discDiscontinuous _ hH.positivePart D hD
      (fun g=>hinv ⟨Mobius.complexMobiusToFull g.val,g.property⟩)).mp ((full_discrete_iff_positivePart H).mp hd)
  have hposD : DiscreteGroups.Action.IsDiscontinuous (Mobius.fullGroupPositivePart H) D:=
    (isMobiusDiscontinuousOn_iff_subtype _ D hip).mp hpos
  have hkernel : DiscreteGroups.Action.IsDiscontinuous (Mobius.fullGroupPositiveKernel H) D:=
    hposD.transport (Mobius.fullGroupPositivePartEquiv H).toEquiv (Homeomorph.refl D) (fun _ _=>rfl)
  have hc (g : H) : Continuous (fun x : D=>g • x):=by
    apply Continuous.subtype_mk
    exact (Mobius.fullMobiusContinuousMap g.val).continuous.comp continuous_subtype_val
  exact (isFullMobiusDiscontinuousOn_iff_subtype H D hi).mpr
    (discontinuous_of_finiteIndex (Mobius.fullGroupPositiveKernel H) hc hkernel)

theorem full_discontinuous_fixedPointsNonaccumulating {H : Subgroup Mobius.complexGeneralMobiusGroup}
    {D : Set Mobius.ExtendedComplex} (hD : IsOpen D) (h : IsFullMobiusDiscontinuousOn H D) :
    FullEllipticFixedPointsNonaccumulating H D := by
  apply (full_fixedPointsNonaccumulating_iff_positivePart H D).mpr
  exact DiscreteGroups.IsMobiusDiscontinuousOn.ellipticFixedPointsNonaccumulating
    (DiscreteGroups.IsFullMobiusDiscontinuousOn.positivePart h) hD

/-- Six equivalent discreteness criteria for the full geometric isometry group preserving the model,
with the genuine Poincare finite-orbit definition of non-elementarity. -/
theorem full_discreteness_elliptic_and_cyclic_criteria_tfae (H : Subgroup Mobius.complexGeneralMobiusGroup) (hH :
    Mobius.IsFullNonElementary H)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D) (hinv : ∀f : H,f.val.val '' D=D) :
    List.TFAE [DiscreteTopology H,IsFullMobiusDiscontinuousOn H D,
      FullEllipticFixedPointsNonaccumulating H D,FullEllipticsNonaccumulatingAtIdentity H,
      FullEllipticsFiniteOrder H,FullAllCyclicSubgroupsDiscrete H] := by
  tfae_have 1 → 2:=full_discrete_discontinuous H hH D hD hinv
  tfae_have 2 → 1:=full_discontinuous_discrete H D hD hinv
  tfae_have 2 → 3:=full_discontinuous_fixedPointsNonaccumulating hD.isOpen
  tfae_have 3 → 5:=DiscreteGroups.FullEllipticFixedPointsNonaccumulating.ellipticsFiniteOrder hH hD hinv
  tfae_have 1 → 4:=full_discrete_ellipticsNonaccumulatingAtIdentity H
  tfae_have 4 → 5:=DiscreteGroups.FullEllipticsNonaccumulatingAtIdentity.ellipticsFiniteOrder
  tfae_have 1 → 5:=full_discrete_ellipticsFiniteOrder H
  tfae_have 5 → 1:=fun h=>h.discrete hH D hD hinv
  tfae_have 1 → 6:=full_discrete_allCyclicSubgroupsDiscrete H
  tfae_have 6 → 5:=DiscreteGroups.FullAllCyclicSubgroupsDiscrete.ellipticsFiniteOrder
  tfae_finish

end
end LowDimensionalTopology.Geometry.DiscreteGroups
