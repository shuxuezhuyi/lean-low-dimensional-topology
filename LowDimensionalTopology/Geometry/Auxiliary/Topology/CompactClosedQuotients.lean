/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
universe u
variable {X:Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Saturating a closed set by a closed equivalence relation on a compact Hausdorff space gives a closed set. -/
theorem closedSetoid_saturation_isClosed (R:Setoid X)
    (hR:IsClosed {p:X×X|R p.1 p.2}) (S:Set X) (hS:IsClosed S) :
    IsClosed ((Quotient.mk R) ⁻¹' ((Quotient.mk R) '' S)) := by
  have he:(Quotient.mk R) ⁻¹' ((Quotient.mk R) '' S)=
      Prod.snd '' ((S×ˢ(univ:Set X))∩{p:X×X|R p.1 p.2}):=by
    ext x
    constructor
    · rintro ⟨s,hs,hq⟩
      exact ⟨(s,x),⟨⟨hs,trivial⟩,Quotient.exact hq⟩,rfl⟩
    · rintro ⟨⟨s,t⟩,⟨⟨hs,_ht⟩,hst⟩,rfl⟩
      exact ⟨s,hs,Quotient.sound hst⟩
  rw [he]
  exact (((hS.prod isClosed_univ).inter hR).isCompact.image continuous_snd).isClosed

/-- The actual quotient projection of a compact Hausdorff closed setoid is a closed map. -/
theorem closedSetoid_quotient_isClosedMap (R:Setoid X)
    (hR:IsClosed {p:X×X|R p.1 p.2}) : IsClosedMap (Quotient.mk R) := by
  intro S hS
  exact isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
    (closedSetoid_saturation_isClosed R hR S hS)

omit [T2Space X] in
/-- Every literal equivalence class is compact, without presupposing that the quotient is Hausdorff. -/
theorem closedSetoid_quotient_fiber_isCompact (R:Setoid X)
    (hR:IsClosed {p:X×X|R p.1 p.2}) (y:Quotient R) :
    IsCompact ((Quotient.mk R) ⁻¹' {y}) := by
  induction y using Quotient.inductionOn with
  | h a =>
    have hc:IsClosed ((Quotient.mk R) ⁻¹' {Quotient.mk R a}):=by
      have he:(Quotient.mk R) ⁻¹' {Quotient.mk R a}={x:X|R x a}:=by
        ext x
        exact Quotient.eq
      rw [he]
      exact hR.preimage (continuous_id.prodMk continuous_const)
    exact hc.isCompact

theorem closedSetoid_quotient_isProperMap (R:Setoid X)
    (hR:IsClosed {p:X×X|R p.1 p.2}) : IsProperMap (Quotient.mk R) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_quotient_mk',closedSetoid_quotient_isClosedMap R hR,
      closedSetoid_quotient_fiber_isCompact R hR⟩

/-- A closed equivalence relation on a compact Hausdorff space has a genuine Hausdorff quotient. -/
theorem closedSetoid_quotient_t2Space (R:Setoid X)
    (hR:IsClosed {p:X×X|R p.1 p.2}) : T2Space (Quotient R) := by
  have hp:=closedSetoid_quotient_isProperMap R hR
  have he:diagonal (Quotient R)=
      (Prod.map (Quotient.mk R) (Quotient.mk R)) '' {p:X×X|R p.1 p.2}:=by
    ext ⟨y,z⟩
    constructor
    · intro hyz
      change y=z at hyz
      subst z
      obtain ⟨a,rfl⟩:=Quotient.exists_rep y
      exact ⟨(a,a),R.refl a,rfl⟩
    · rintro ⟨⟨a,b⟩,hab,hpair⟩
      rw [←hpair]
      exact Quotient.sound hab
  apply t2_iff_isClosed_diagonal.mpr
  rw [he]
  exact (hp.prodMap hp).isClosedMap _ hR

end LowDimensionalTopology.Geometry.Auxiliary.Topology
