/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCompactDevelopment
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- One literal pairing of original boundary points; no ambient orbit relation is used in this definition. -/
def PointStep (p q : P.Point) : Prop:=
  ∃s:P.Side,p.val∈s.val ∧ q.val=S.generator s • p.val

/-- Actual transitive gluing of original polygon points along the given side pairings. -/
def pointGluingSetoid : Setoid P.Point:=Relation.EqvGen.setoid S.PointStep

/-- The original polygon with its genuine boundary point identifications. -/
def PointQuotient:=Quotient S.pointGluingSetoid

def pointProjection (p : P.Point) : S.PointQuotient:=Quotient.mk S.pointGluingSetoid p

theorem pointStep_orbitProjection {p q : P.Point} (h : S.PointStep p q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X q.val := by
  obtain ⟨s,hp,hq⟩:=h
  rw [hq,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul]

theorem pointGluing_orbitProjection {p q : P.Point} (h : Relation.EqvGen S.PointStep p q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X q.val := by
  induction h with
  | rel p q h => exact S.pointStep_orbitProjection h
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih1 ih2 => exact ih1.trans ih2

/-- Forgetting the original copy index sends every development gluing to an actual point gluing. -/
theorem gluing_forget_index {a b : S.Copy} (h : Relation.EqvGen S.Step a b) :
    Relation.EqvGen S.PointStep a.2 b.2 := by
  induction h with
  | rel a b h =>
    rcases h with rfl|⟨s,hp,hq,_hg⟩
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ ⟨s,hp,hq⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The canonical continuous candidate forgets only the original copy label. -/
def forgetIndex : S.Development→S.PointQuotient:=
  Quotient.lift (fun a:S.Copy=>S.pointProjection a.2)
    (fun _ _ h=>Quotient.sound (S.gluing_forget_index h))

@[simp] theorem forgetIndex_project (a : S.Copy) : S.forgetIndex (S.project a)=S.pointProjection a.2:=rfl

theorem forgetIndex_smul (g : S.Generated) (q : S.Development) : S.forgetIndex (g • q)=S.forgetIndex q:=by
  induction q using Quotient.inductionOn with
  | h a => rfl

/-- Actual original point gluing implies equality in the original group orbit quotient. -/
def pointToOrbit : S.PointQuotient→ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated X:=
  Quotient.lift (fun p:P.Point=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated
    X p.val)
    (fun _ _ h=>S.pointGluing_orbitProjection h)

@[simp] theorem pointToOrbit_projection (p : P.Point) :
    S.pointToOrbit (S.pointProjection
      p)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X p.val:=rfl

theorem pointToOrbit_forgetIndex (q : S.Development) :
    S.pointToOrbit (S.forgetIndex q)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X (S.evaluation q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X a.2.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X (a.1 • a.2.val)
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul _ _ a.1 a.2.val).symm

/-- Injectivity of the actual developing map rules out any extra original orbit identifications. -/
theorem pointGluing_iff_orbitProjection (he : Function.Injective S.evaluation) (p q : P.Point) :
    Relation.EqvGen S.PointStep p q ↔
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X q.val := by
  constructor
  · exact S.pointGluing_orbitProjection
  · intro h
    obtain ⟨g,hg⟩:=(Quotient.exact h : MulAction.orbitRel S.Generated X p.val q.val)
    have hh : S.project (1,p)=S.project (g,q):=he (by
      change (1:S.Generated) • p.val=g • q.val
      simpa only [one_smul] using hg.symm)
    exact S.gluing_forget_index ((S.project_eq_iff _ _).mp hh)

theorem pointToOrbit_injective (he : Function.Injective S.evaluation) : Function.Injective S.pointToOrbit := by
  intro p q
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      intro hpq
      exact Quotient.sound ((S.pointGluing_iff_orbitProjection he p q).mpr hpq)

theorem pointToOrbit_surjective (he : Function.Surjective S.evaluation) : Function.Surjective S.pointToOrbit := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨p,hp⟩:=he x
    exact ⟨S.forgetIndex p,by rw [S.pointToOrbit_forgetIndex,hp];rfl⟩

section Topology
variable [TopologicalSpace X]
local instance pointQuotientGeneratedTopology : TopologicalSpace S.Generated:=⊥
local instance pointQuotientGeneratedDiscrete : DiscreteTopology S.Generated:=⟨rfl⟩

instance pointQuotientTopology : TopologicalSpace S.PointQuotient:=
  inferInstanceAs (TopologicalSpace (Quotient S.pointGluingSetoid))

theorem continuous_pointProjection : Continuous S.pointProjection:=continuous_quot_mk

theorem continuous_forgetIndex : Continuous S.forgetIndex := by
  apply continuous_quot_lift
  exact S.continuous_pointProjection.comp continuous_snd

theorem continuous_pointToOrbit : Continuous S.pointToOrbit :=
  continuous_quot_lift _ ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_continuous
    S.Generated X).comp continuous_subtype_val)


/-- A genuine global developing homeomorphism supplies the inverse point-gluing map. -/
def orbitToPoint (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated X→S.PointQuotient:=
  Quotient.lift (fun x:X=>S.forgetIndex (E.symm x)) (by
    intro x y h
    obtain ⟨g,hg⟩:=h
    have hh : E.symm x=g • E.symm y:=by
      apply E.injective
      rw [E.apply_symm_apply,he,S.evaluation_smul,←he,E.apply_symm_apply]
      exact hg.symm
    rw [hh,S.forgetIndex_smul])

theorem pointToOrbit_orbitToPoint (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q)
    (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated X) : S.pointToOrbit (S.orbitToPoint E he q)=q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change S.pointToOrbit (S.forgetIndex (E.symm
      x))=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X x
    rw [S.pointToOrbit_forgetIndex,←he,E.apply_symm_apply]

theorem orbitToPoint_pointToOrbit (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q)
    (q : S.PointQuotient) : S.orbitToPoint E he (S.pointToOrbit q)=q := by
  induction q using Quotient.inductionOn with
  | h p =>
    have hh : E.symm p.val=S.project (1,p):=by
      apply E.injective
      rw [E.apply_symm_apply,he,S.evaluation_project]
      change p.val=(1:S.Generated) • p.val
      rw [one_smul]
    change S.forgetIndex (E.symm p.val)=S.pointProjection p
    rw [hh,S.forgetIndex_project]

theorem continuous_orbitToPoint (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    Continuous (S.orbitToPoint E he) :=
  continuous_quot_lift _ (S.continuous_forgetIndex.comp E.symm.continuous)

/-- The true polygon boundary-gluing quotient is homeomorphic to the original group orbit space;
no orbit relation occurs in the definition of the source gluing. -/
def pointOrbitHomeomorph (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    S.PointQuotient≃ₜ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated X where
  toEquiv := {
    toFun := S.pointToOrbit
    invFun := S.orbitToPoint E he
    left_inv := S.orbitToPoint_pointToOrbit E he
    right_inv := S.pointToOrbit_orbitToPoint E he }
  continuous_toFun:=S.continuous_pointToOrbit
  continuous_invFun:=S.continuous_orbitToPoint E he

@[simp] theorem pointOrbitHomeomorph_projection (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q)
    (p : P.Point) : S.pointOrbitHomeomorph E he (S.pointProjection
      p)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated X p.val:=rfl

end Topology
end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open scoped UpperHalfPlane
variable {Γ : Type*} [Group Γ] [MulAction Γ ℍ]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- In the genuine compact native polygon case, actual local tessellation and compactness alone
construct the global original side-gluing/orbit homeomorphism. This does not apply to ideal cusps. -/
def FiniteFiberLocalTessellationCondition.compactPointOrbitHomeomorph
    (h : S.FiniteFiberLocalTessellationCondition) (hm : S.MetricPolygonAssumptions)
    (hcl : P.carrier⊆closure P.interior) (hc : IsCompact P.carrier) :
    S.PointQuotient≃ₜ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ := by
  let E: S.Development≃ₜℍ:=(h.covering_homeomorph_of_compact S hm hcl hc).2.homeomorph
  exact S.pointOrbitHomeomorph E (fun _=>rfl)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
