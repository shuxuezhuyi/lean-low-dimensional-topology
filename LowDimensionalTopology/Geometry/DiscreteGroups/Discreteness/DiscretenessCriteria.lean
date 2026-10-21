/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.EllipticFreeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianFiniteGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.MobiusPackings
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenApplications
public import LowDimensionalTopology.Geometry.DiscreteGroups.Linear.Selberg
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
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

/-- The actual fixed points of genuine elliptic group elements in the compactified complex plane. -/
def ellipticFixedPointSet (H : Subgroup Mobius.complexMobiusGroup) : Set Mobius.ExtendedComplex :=
  {z | ∃g : H,Mobius.MobiusElliptic g.val ∧ g.val.val z=z}

/-- The literal nonaccumulation condition, restricted to the actual open hyperbolic model. -/
def EllipticFixedPointsNonaccumulating (H : Subgroup Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex) :
    Prop :=
  ∀z∈D,¬AccPt z (𝓟 (ellipticFixedPointSet H))

/-- An actual ambient neighborhood of the identity contains no elliptic group member. -/
def EllipticsNonaccumulatingAtIdentity (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀ᶠf in 𝓝 (1 : Mobius.complexMobiusGroup),f∈H → ¬Mobius.MobiusElliptic f

/-- Every genuine elliptic member has finite group-theoretic order. -/
def EllipticsFiniteOrder (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀g∈H,Mobius.MobiusElliptic g → IsOfFinOrder g

/-- All actual cyclic subgroups inherit the discrete topology from the actual Mobius group. -/
def AllCyclicSubgroupsDiscrete (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀g∈H,Mobius.IsDiscreteMobiusSubgroup (Subgroup.zpowers g)

/-- Condition (1) implies condition (4) in the actual group topology. -/
theorem discrete_ellipticsNonaccumulatingAtIdentity (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) : EllipticsNonaccumulatingAtIdentity H := by
  let : DiscreteTopology H:=hd
  obtain ⟨U,hU,hUH⟩:=(isDiscrete_iff_forall_mem_exists_isOpen.mp
    (isDiscrete_iff_discreteTopology.mpr hd)) 1 H.one_mem
  have h1 : (1 : Mobius.complexMobiusGroup)∈U:=((hUH.symm ▸ (mem_singleton 1))).1
  filter_upwards [hU.mem_nhds h1] with f hf hfH hfe
  have he : f=1:=Set.mem_singleton_iff.mp (hUH ▸ ⟨hf,hfH⟩)
  exact hfe.1 he

/-- A discrete subgroup has discrete actual cyclic subgroups, including the trivial subgroup. -/
theorem discrete_allCyclicSubgroupsDiscrete (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) : AllCyclicSubgroupsDiscrete H := by
  intro g hg
  exact Fuchsian.discreteMobius_subgroup_of_le H (Subgroup.zpowers g) hd
    ((Subgroup.zpowers_le).mpr hg)

/-- A discrete actual elliptic cyclic group has finite order, via its actual H3 fixed point. -/
theorem discrete_elliptic_finiteOrder (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) : EllipticsFiniteOrder H := by
  intro f hf hfe
  obtain ⟨q,hq⟩:=hfe.axis_nonempty
  have hdis:=discreteMobius_isDiscontinuous_H3 H hd
  have hfin:=isOfFinOrder_of_finite_stabilizer (⟨f,hf⟩ : H) q (hdis.finite_stabilizer q) hq
  obtain ⟨n,hn,he⟩:=hfin.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩

/-- Discreteness of cyclic subgroups forces elliptic elements to have finite order. -/
theorem AllCyclicSubgroupsDiscrete.ellipticsFiniteOrder {H : Subgroup Mobius.complexMobiusGroup}
    (h : AllCyclicSubgroupsDiscrete H) : EllipticsFiniteOrder H := by
  intro g hg hge
  exact discrete_elliptic_finiteOrder (Subgroup.zpowers g) (h g hg) g (Subgroup.mem_zpowers g) hge

/-- Absence of elliptics near the identity makes every elliptic cyclic subgroup discrete. -/
theorem EllipticsNonaccumulatingAtIdentity.elliptic_cyclic_discrete {H : Subgroup Mobius.complexMobiusGroup}
    (h : EllipticsNonaccumulatingAtIdentity H) {g : Mobius.complexMobiusGroup} (hg : g∈H)
    (he : Mobius.MobiusElliptic g) : Mobius.IsDiscreteMobiusSubgroup (Subgroup.zpowers g) := by
  obtain ⟨q,hq⟩:=he.axis_nonempty
  have hfix : ∀f∈Subgroup.zpowers g,f • q=q := by
    intro f hf
    exact (Subgroup.zpowers_le.mpr (show g∈MulAction.stabilizer Mobius.complexMobiusGroup q from hq)) hf
  have hall:=Mobius.mobius_common_H3_fixed_all_elliptic (Subgroup.zpowers g) ⟨q,hfix⟩
  apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences (Subgroup.zpowers g)).mpr
  intro u hu
  filter_upwards [hu.eventually h] with n hn
  apply Subtype.ext
  by_contra hne
  exact hn ((Subgroup.zpowers_le.mpr hg) (u n).property)
    (hall (u n).val (u n).property hne)

/-- Condition (4) implies condition (5) without assuming discreteness in advance. -/
theorem EllipticsNonaccumulatingAtIdentity.ellipticsFiniteOrder {H : Subgroup Mobius.complexMobiusGroup}
    (h : EllipticsNonaccumulatingAtIdentity H) : EllipticsFiniteOrder H := by
  intro g hg he
  exact discrete_elliptic_finiteOrder (Subgroup.zpowers g) (h.elliptic_cyclic_discrete hg he)
    g (Subgroup.mem_zpowers g) he

/-- A genuine compact set in a discontinuity domain contains only finitely many actual elliptic fixed points. -/
theorem IsMobiusDiscontinuousOn.finite_ellipticFixedPoints {H : Subgroup Mobius.complexMobiusGroup}
    {D : Set Mobius.ExtendedComplex} (h : IsMobiusDiscontinuousOn H D) (K : Set Mobius.ExtendedComplex)
    (hK : IsCompact K) (hKD : K⊆D) : (K∩ellipticFixedPointSet H).Finite := by
  classical
  let F : Set H:={g | ((g.val.val '' K)∩K).Nonempty}
  have hF : F.Finite:=h K hK hKD
  have hfinite : (⋃g∈F,if Mobius.MobiusElliptic g.val then {z : Mobius.ExtendedComplex | g.val.val z=z} else
    ∅).Finite := by
    apply hF.biUnion
    intro g hg
    split_ifs with he
    · exact mobius_boundary_fixedPoints_finite g.val he.1
    · exact Set.finite_empty
  apply hfinite.subset
  rintro z ⟨hzK,g,hg,hgz⟩
  have hgF : g∈F:=⟨z,⟨z,hzK,hgz⟩,hzK⟩
  exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨hgF,by simp only [ite_eq_left hg];exact hgz⟩⟩

/-- Condition (2) implies the literal condition (3) for every actual open domain. -/
theorem IsMobiusDiscontinuousOn.ellipticFixedPointsNonaccumulating {H : Subgroup Mobius.complexMobiusGroup}
    {D : Set Mobius.ExtendedComplex} (h : IsMobiusDiscontinuousOn H D) (hD : IsOpen D) :
    EllipticFixedPointsNonaccumulating H D := by
  intro z hz hacc
  obtain ⟨K,hK,hzK,hKD⟩:=exists_compact_subset hD hz
  exact (Set.Infinite.of_accPt (hacc.nhds_inter (mem_interior_iff_mem_nhds.mp hzK)))
    (DiscreteGroups.IsMobiusDiscontinuousOn.finite_ellipticFixedPoints h K hK hKD)

/-- The literal nonaccumulation condition is equivalent to finite intersection with every genuine compact subset. -/
theorem ellipticFixedPointsNonaccumulating_iff_compact (H : Subgroup Mobius.complexMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) :
    EllipticFixedPointsNonaccumulating H D ↔
      ∀K : Set Mobius.ExtendedComplex,IsCompact K → K⊆D → (K∩ellipticFixedPointSet H).Finite := by
  constructor
  · intro h K hK hKD
    by_contra hn
    obtain ⟨z,hz,hacc⟩:=Set.Infinite.exists_accPt_of_subset_isCompact hn hK inter_subset_left
    exact h z (hKD hz) (hacc.mono (Filter.principal_mono.mpr inter_subset_right))
  · intro h z hz hacc
    obtain ⟨K,hK,hzK,hKD⟩:=exists_compact_subset hD hz
    exact (Set.Infinite.of_accPt (hacc.nhds_inter (mem_interior_iff_mem_nhds.mp hzK))) (h K hK hKD)

/-- A non-elementary subgroup preserving a disc is discrete exactly when its disc action is discontinuous. -/
theorem discrete_iff_discDiscontinuous (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D)
    (hinv : ∀g : H,g.val.val '' D=D) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ IsMobiusDiscontinuousOn H D := by
  have hi : ∀(g : H) z,z∈D → g • z∈D:=by
    intro g z hz
    rw [←hinv g]
    exact mem_image_of_mem _ hz
  have hproper : D≠univ:=by
    obtain ⟨q,hq⟩:=Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hD
    intro he
    have hh : (∞ : Mobius.ExtendedComplex)∈q.val '' D:=by
      rw [he]
      exact ⟨q.val.symm ∞,mem_univ _,q.val.apply_symm_apply ∞⟩
    rw [hq] at hh
    simp [Hyperbolic.openHalfPlaneSet] at hh
  constructor
  · intro hd
    exact discontinuous_on_proper_open_invariant_set H hH hd D hD.isOpen hproper hi
  · exact isMobiusDiscontinuousOn_invariant_discrete H D hi hD.isConnected.nonempty

end
end LowDimensionalTopology.Geometry.DiscreteGroups
