/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.DiscretenessCriteria
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

/-- Finite-index extension preserves the existence of a genuine finite orbit. -/
theorem hasFiniteOrbit_of_finiteIndex {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) [K.FiniteIndex] (h : DiscreteGroups.Action.HasFiniteOrbit K X) :
      DiscreteGroups.Action.HasFiniteOrbit G X := by
  obtain ⟨x,hx⟩:=h
  have hfinite : (⋃q : G ⧸ K,(fun z : X=>q.out • z) '' MulAction.orbit K x).Finite :=
    Set.finite_iUnion fun q=>hx.image _
  refine ⟨x,hfinite.subset ?_⟩
  rintro y ⟨g,rfl⟩
  let q : G ⧸ K:=QuotientGroup.mk g
  have hk : q.out⁻¹*g∈K:=QuotientGroup.eq.mp (Quotient.out_eq' q)
  refine mem_iUnion.mpr ⟨q,⟨(q.out⁻¹*g) • x,?_,?_⟩⟩
  · exact ⟨⟨q.out⁻¹*g,hk⟩,rfl⟩
  · simp only [mul_smul,smul_inv_smul]

/-- The subgroup-of-subgroup and its actual ambient image have the same actual orbit. -/
theorem orbit_map_subtype {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (K : Subgroup H) (x : X) :
    MulAction.orbit (K.map H.subtype) x=MulAction.orbit K x := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨h,hh,he⟩:=g.property
    exact ⟨⟨h,hh⟩,congrArg (fun a : G=>a • x) he⟩
  · rintro ⟨g,rfl⟩
    exact ⟨⟨g.val.val,⟨g.val,g.property,rfl⟩⟩,rfl⟩

/-- Non-elementarity survives passage to every genuine finite-index subgroup. -/
theorem nonElementary_finiteIndex (H : Subgroup Mobius.complexMobiusGroup) (K : Subgroup H)
    [K.FiniteIndex] (hH : IsNonElementary H) : IsNonElementary (K.map H.subtype) := by
  intro hK
  apply hH
  obtain ⟨x,hx⟩:=hK
  rw [orbit_map_subtype] at hx
  exact hasFiniteOrbit_of_finiteIndex K ⟨x,hx⟩

/-- Finite generation lifts along a surjective actual homomorphism using finitely many chosen lifts. -/
theorem fg_lift_of_surjective {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    (hsurj : Function.Surjective φ) (H : Subgroup Q) (hH : H.FG) :
    ∃L : Subgroup G,L.FG ∧ L.map φ=H := by
  classical
  obtain ⟨S,hS,hfin⟩:=(Subgroup.fg_iff H).mp hH
  let f : Q → G:=fun q=>(hsurj q).choose
  have hf (q : Q) : φ (f q)=q:=(hsurj q).choose_spec
  refine ⟨Subgroup.closure (f '' S),(Subgroup.fg_iff _).mpr ⟨f '' S,rfl,hfin.image f⟩,?_⟩
  rw [MonoidHom.map_closure,Set.image_image]
  have he : (fun q=>φ (f q)) '' S=S:=by simp only [hf,image_id']
  rw [he,hS]

/-- A finite actual kernel prevents an infinite-order element from having finite-order image. -/
theorem isOfFinOrder_of_finite_kernel {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) [Finite φ.ker] {g : G} (h : IsOfFinOrder (φ g)) : IsOfFinOrder g := by
  obtain ⟨n,hn,he⟩:=h.exists_pow_eq_one
  let a : φ.ker:=⟨g^n,by change φ (g^n)=1;rw [map_pow,he]⟩
  have ha : IsOfFinOrder (g^n):=φ.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite a)
  exact ha.of_pow hn.ne'

/-- The genuine SL2 projection has the actual finite two-element kernel. -/
theorem mobiusProjection_kernel_finite : Finite Mobius.mobiusSpecialLinearProjection.ker := by
  obtain ⟨A,B,_,he⟩:=Mobius.mobiusProjection_fiber_pair 1
  have hf : (Mobius.mobiusSpecialLinearProjection.ker : Set Auxiliary.Algebra.SpecialLinear2).Finite:=by
    change (Mobius.mobiusSpecialLinearProjection ⁻¹' {1}).Finite
    rw [he]
    exact (Set.finite_singleton B).insert A
  exact hf.to_subtype

theorem specialLinear_finiteOrder_of_projection {A : Auxiliary.Algebra.SpecialLinear2}
    (h : IsOfFinOrder (Mobius.mobiusSpecialLinearProjection A)) : IsOfFinOrder A := by
  let : Finite Mobius.mobiusSpecialLinearProjection.ker:=mobiusProjection_kernel_finite
  exact isOfFinOrder_of_finite_kernel Mobius.mobiusSpecialLinearProjection h

/-- A genuine finitely generated Mobius group with only finite-order elliptics has an actual
finite-index elliptic-free subgroup; the finite central SL2 kernel is handled explicitly. -/
theorem fg_exists_finiteIndex_ellipticFree (H : Subgroup Mobius.complexMobiusGroup) (hH : H.FG)
    (hE : EllipticsFiniteOrder H) :
    ∃K : Subgroup H,K.FiniteIndex ∧ IsEllipticFree (K.map H.subtype) := by
  obtain ⟨L,hL,hLH⟩:=fg_lift_of_surjective Mobius.mobiusSpecialLinearProjection
    Mobius.mobiusSpecialLinearProjection_surjective H hH
  let p : L →* H:=
    { toFun:=fun A=>⟨Mobius.mobiusSpecialLinearProjection A.val,hLH ▸ ⟨A.val,A.property,rfl⟩⟩
      map_one':=Subtype.ext Mobius.mobiusSpecialLinearProjection.map_one
      map_mul':=fun A B=>Subtype.ext (Mobius.mobiusSpecialLinearProjection.map_mul A.val B.val) }
  have hp : Function.Surjective p:=by
    intro g
    have hg : g.val∈L.map Mobius.mobiusSpecialLinearProjection:=hLH ▸ g.property
    obtain ⟨A,hA,he⟩:=hg
    exact ⟨⟨A,hA⟩,Subtype.ext he⟩
  let : Group.FG L:=(Group.fg_iff_subgroup_fg L).mpr hL
  let ρ : L →* Matrix.GeneralLinearGroup (Fin 2) ℂ:=
    Matrix.SpecialLinearGroup.toGL.comp L.subtype
  have hρ : Function.Injective ρ:=Matrix.SpecialLinearGroup.toGL_injective.comp L.subtype_injective
  obtain ⟨N,hN⟩:=selberg_lemma_linear ρ hρ
  let K : Subgroup H:=N.toSubgroup.map p
  let : N.toSubgroup.FiniteIndex:=inferInstance
  have hK : K.FiniteIndex:=Subgroup.FiniteIndex.map_of_surjective N.toSubgroup hp
  refine ⟨K,hK,?_⟩
  intro g hge
  obtain ⟨k,hk,hkg⟩:=g.property
  have hgek : Mobius.MobiusElliptic k.val:=by
    have hkg' : k.val=g.val:=hkg
    rw [hkg']
    exact hge
  obtain ⟨A,hA,hAk⟩:=hk
  have hproj : Mobius.mobiusSpecialLinearProjection A.val=k.val:=congrArg Subtype.val hAk
  have hf : IsOfFinOrder A.val:=specialLinear_finiteOrder_of_projection
    (by rw [hproj];exact hE k.val k.property hgek)
  have hAL : IsOfFinOrder A:=L.subtype_injective.isOfFinOrder_iff.mp hf
  let a : N.toSubgroup:=⟨A,hA⟩
  have hAN : IsOfFinOrder a:=N.toSubgroup.subtype_injective.isOfFinOrder_iff.mp hAL
  let : IsMulTorsionFree N.toSubgroup:=hN
  have ha : a=1:=(isOfFinOrder_iff_eq_one a).mp hAN
  have hAone : A=1:=congrArg Subtype.val ha
  have hkone : k=1:=by rw [←hAk,hAone,p.map_one]
  exact hgek.1 (congrArg Subtype.val hkone)

/-- Discreteness of the actual ambient image transfers back to a finite-index subgroup and its parent. -/
theorem finiteIndex_discrete_of_image (H : Subgroup Mobius.complexMobiusGroup) (K : Subgroup H)
    [K.FiniteIndex] (hd : Mobius.IsDiscreteMobiusSubgroup (K.map H.subtype)) : Mobius.IsDiscreteMobiusSubgroup H := by
  let J:=K.map H.subtype
  let f : K → J:=fun x=>⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
  let : DiscreteTopology J:=hd
  have hcomp : Topology.IsEmbedding ((Subtype.val : J → Mobius.complexMobiusGroup) ∘ f):=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : H → Mobius.complexMobiusGroup)).comp
      (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : K → H))
  have hf : Topology.IsEmbedding f:=(Topology.IsEmbedding.of_comp_iff
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : J → Mobius.complexMobiusGroup))).mp hcomp
  have hK : DiscreteTopology K:=hf.discreteTopology
  exact (Subgroup.discreteTopology_iff_of_finiteIndex (H:=K)).mp hK

/-- A finitely generated non-elementary disc group with finite-order elliptics is discrete. -/
theorem fg_finiteEllipticOrder_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (hfg : H.FG) (hH : IsNonElementary H) (hD : Mobius.HasInvariantComplexDisc H)
    (hE : EllipticsFiniteOrder H) : Mobius.IsDiscreteMobiusSubgroup H := by
  obtain ⟨K,hK,hKE⟩:=fg_exists_finiteIndex_ellipticFree H hfg hE
  let : K.FiniteIndex:=hK
  have hJD : Mobius.HasInvariantComplexDisc (K.map H.subtype):=by
    obtain ⟨D,hD,hi⟩:=hD
    refine ⟨D,hD,?_⟩
    intro g
    obtain ⟨k,hk,hkg⟩:=g.property
    rw [←hkg]
    exact hi k
  exact finiteIndex_discrete_of_image H K
    (discrete_of_ellipticFree_nonElementary_invariant_disc (K.map H.subtype) hJD hKE (nonElementary_finiteIndex H K hH))

/-- Two actual loxodromics with disjoint full compactified fixed sets rule out every elementary orbit. -/
theorem nonElementary_of_disjoint_loxodromics (H : Subgroup Mobius.complexMobiusGroup)
    (f g : Mobius.complexMobiusGroup) (hfH : f∈H) (hgH : g∈H)
    (hf : Mobius.MobiusLoxodromic f) (hg : Mobius.MobiusLoxodromic g)
    (hdis : Disjoint (Mobius.mobiusExtendedFixedPoints f) (Mobius.mobiusExtendedFixedPoints g)) : IsNonElementary
      H := by
  intro hE
  obtain ⟨z,hz⟩:=elementary_loxodromic_boundary_finite_orbit H hE f hfH hf
  have hfz:=finite_boundary_orbit_fixed_by_loxodromic H f hfH hf z hz
  have hgz:=finite_boundary_orbit_fixed_by_loxodromic H g hgH hg z hz
  exact Set.disjoint_left.mp hdis ((Mobius.mobiusExtendedFixedPoints_boundary_iff f z).mpr hfz)
    ((Mobius.mobiusExtendedFixedPoints_boundary_iff g z).mpr hgz)

/-- Each finite subset of a genuine non-elementary group lies in a genuine finitely generated
non-elementary subgroup of the same actual ambient group. -/
theorem exists_fg_nonElementary_subgroup (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (S : Set Mobius.complexMobiusGroup) (hS : S.Finite) (hSH : S⊆H) :
    ∃K : Subgroup Mobius.complexMobiusGroup,K.FG ∧ K≤H ∧ S⊆K ∧ IsNonElementary K := by
  obtain ⟨v,_,hv,hd⟩:=exists_injective_loxodromic_sequence_pairwise_disjoint_fixedPoints H hH
  let T:=insert (v 0).val (insert (v 1).val S)
  let K:=Subgroup.closure T
  have hKfg : K.FG:=(Subgroup.fg_iff K).mpr ⟨T,rfl,(hS.insert _).insert _⟩
  have hKH : K≤H:=(Subgroup.closure_le _).mpr (by
    intro x hx
    rcases hx with h | h | h
    · exact h ▸ (v 0).property
    · exact h ▸ (v 1).property
    · exact hSH h)
  have h0 : (v 0).val∈K:=Subgroup.subset_closure (mem_insert _ _)
  have h1 : (v 1).val∈K:=Subgroup.subset_closure (mem_insert_of_mem _ (mem_insert _ _))
  refine ⟨K,hKfg,hKH,?_,nonElementary_of_disjoint_loxodromics K _ _ h0 h1 (hv 0) (hv 1) (hd (by decide))⟩
  intro x hx
  exact Subgroup.subset_closure (mem_insert_of_mem _ (mem_insert_of_mem _ hx))

/-- Condition (5) implies (1) for every genuine non-elementary invariant-disc Mobius group,
with no prior discreteness, finite generation, or uniform order bound assumed. -/
theorem EllipticsFiniteOrder.discrete {H : Subgroup Mobius.complexMobiusGroup}
    (hE : EllipticsFiniteOrder H) (hH : IsNonElementary H) (hD : Mobius.HasInvariantComplexDisc H) :
    Mobius.IsDiscreteMobiusSubgroup H := by
  apply (discrete_iff_all_two_generated_subgroups_discrete H hH).mpr
  intro f g
  have hpair : ({f.val,g.val} : Set Mobius.complexMobiusGroup)⊆H:=by
    intro x hx
    rcases hx with h | h
    · exact h ▸ f.property
    · exact (mem_singleton_iff.mp h) ▸ g.property
  obtain ⟨K,hKfg,hKH,hfg,hKN⟩:=exists_fg_nonElementary_subgroup H hH {f.val,g.val}
    ((Set.finite_singleton _).insert _) hpair
  have hKD : Mobius.HasInvariantComplexDisc K:=by
    obtain ⟨D,hD,hi⟩:=hD
    exact ⟨D,hD,fun k=>hi ⟨k.val,hKH k.property⟩⟩
  have hKE : EllipticsFiniteOrder K:=fun x hx=>hE x (hKH hx)
  have hdisc:=fg_finiteEllipticOrder_discrete K hKfg hKN hKD hKE
  exact Fuchsian.discreteMobius_subgroup_of_le K _ hdisc ((Subgroup.closure_le _).mpr hfg)

/-- Actual conformal conditions (1) and (5), without finite generation or an order bound. -/
theorem discrete_iff_ellipticsFiniteOrder (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hD : Mobius.HasInvariantComplexDisc H) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ EllipticsFiniteOrder H :=
  ⟨discrete_elliptic_finiteOrder H,fun h=>h.discrete hH hD⟩

/-- A non-elementary disc group is discrete exactly when elliptics avoid an identity neighborhood. -/
theorem discrete_iff_ellipticsNonaccumulatingAtIdentity (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hD : Mobius.HasInvariantComplexDisc H) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ EllipticsNonaccumulatingAtIdentity H :=
  ⟨discrete_ellipticsNonaccumulatingAtIdentity H,fun h=>h.ellipticsFiniteOrder.discrete hH hD⟩

/-- A non-elementary disc group is discrete exactly when all of its cyclic subgroups are discrete. -/
theorem discrete_iff_allCyclicSubgroupsDiscrete (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hD : Mobius.HasInvariantComplexDisc H) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ AllCyclicSubgroupsDiscrete H :=
  ⟨discrete_allCyclicSubgroupsDiscrete H,fun h=>h.ellipticsFiniteOrder.discrete hH hD⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
