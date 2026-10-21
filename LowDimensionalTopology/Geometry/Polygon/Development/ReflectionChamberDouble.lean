/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePointQuotient
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Double.DoubleClosedDisc
public import Mathlib.GroupTheory.Index
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P) (H : Subgroup S.Generated)

def chamberIndexLabel (g : S.Generated) : Bool:=by
  classical
  exact decide (g∈H)

theorem chamberIndexLabel_eq_true (g : S.Generated) : S.chamberIndexLabel H g=true ↔ g∈H:=by
  classical
  simp [chamberIndexLabel]

theorem chamberIndexLabel_mul_mem (k : H) (g : S.Generated) :
    S.chamberIndexLabel H (k.val*g)=S.chamberIndexLabel H g := by
  classical
  simp only [chamberIndexLabel,H.mul_mem_cancel_left k.property]

theorem chamberIndexLabel_eq_iff (hH : H.index=2) (g h : S.Generated) :
    S.chamberIndexLabel H g=S.chamberIndexLabel H h ↔ g*h⁻¹∈H := by
  classical
  rw [H.mul_mem_iff_of_index_two hH,H.inv_mem_iff]
  simp [chamberIndexLabel]

def chamberRepresentative (a : S.Generated) (b : Bool) : S.Generated:=if b then 1 else a

theorem chamberRepresentative_label (a : S.Generated) (ha : a∉H) (b : Bool) :
    S.chamberIndexLabel H (S.chamberRepresentative a b)=b := by
  classical
  cases b <;> simp [chamberRepresentative,chamberIndexLabel,ha]

def ChamberDouble (_S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ
  P):=_root_.LowDimensionalTopology.Geometry.Surfaces.BoundaryDouble P.Point {p|p.val∈P.boundary}

def chamberDoublePoint (a : Bool×P.Point) : S.ChamberDouble:=
  Quotient.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleSetoid P.Point {p|p.val∈P.boundary}) a

def chamberDoubleCopy (a : S.Copy) : S.ChamberDouble:=
  S.chamberDoublePoint (S.chamberIndexLabel H a.1,a.2)

theorem step_chamberDoubleCopy
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    {a b : S.Copy} (h : S.Step a b) : S.chamberDoubleCopy H a=S.chamberDoubleCopy H b := by
  rcases h with rfl|⟨s,hp,hq,_hi⟩
  · rfl
  · apply Quotient.sound
    change a.2=b.2 ∧ (S.chamberIndexLabel H a.1=S.chamberIndexLabel H b.1 ∨ a.2.val∈P.boundary)
    exact ⟨Subtype.ext (hq.trans (hfix s a.2.val hp)).symm,Or.inr (P.side_subset_boundary s hp)⟩

theorem gluing_chamberDoubleCopy
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    {a b : S.Copy} (h : Relation.EqvGen S.Step a b) : S.chamberDoubleCopy H a=S.chamberDoubleCopy H b := by
  induction h with
  | rel a b h => exact S.step_chamberDoubleCopy H hfix h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

def chamberDoubleForget (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x) :
    S.Development→S.ChamberDouble:=
  Quotient.lift (S.chamberDoubleCopy H) (fun _ _ h=>S.gluing_chamberDoubleCopy H hfix h)

@[simp] theorem chamberDoubleForget_project
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x) (a : S.Copy) :
    S.chamberDoubleForget H hfix (S.project a)=S.chamberDoubleCopy H a:=rfl

theorem chamberDoubleForget_smul
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x) (k : H) (q : S.Development) :
    S.chamberDoubleForget H hfix (k.val • q)=S.chamberDoubleForget H hfix q := by
  induction q using Quotient.inductionOn with
  | h a =>
    change S.chamberDoublePoint (S.chamberIndexLabel H (k.val*a.1),a.2)=
      S.chamberDoublePoint (S.chamberIndexLabel H a.1,a.2)
    rw [S.chamberIndexLabel_mul_mem]

/-- Every actual boundary point has equal subgroup-orbit images in the two genuine coset copies. -/
theorem boundary_chamber_orbit_eq (hH : H.index=2)
    (hodd : ∀s:P.Side,S.generator s∉H) (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H) (p : P.Point) (hp : p.val∈P.boundary) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X (a • p.val) := by
  obtain ⟨s,hs,hps⟩:=mem_sUnion.mp hp
  let t:P.Side:=⟨s,hs⟩
  have hmul : a*S.generator t∈H:=(H.mul_mem_iff_of_index_two hH).mpr (by simp [ha,hodd t])
  let k:H:=⟨a*S.generator t,hmul⟩
  have he : k • p.val=a • p.val:=by
    change (a*S.generator t) • p.val=_
    rw [mul_smul,hfix t p.val hps]
  rw [←he,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul]

def chamberDoubleToOrbit (hH : H.index=2)
    (hodd : ∀s:P.Side,S.generator s∉H) (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha :
      a∉H) : S.ChamberDouble→ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H X :=
  Quotient.lift (fun p:Bool×P.Point=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X (S.chamberRepresentative a p.1 • p.2.val)) (by
    intro p q h
    rcases h with ⟨hp,hb|hBoundary⟩
    · cases Prod.ext hb hp
      rfl
    · have he:=S.boundary_chamber_orbit_eq H hH hodd hfix a ha p.2 hBoundary
      rw [←hp]
      cases p.1 <;> cases q.1
      · rfl
      · simpa only [chamberRepresentative,Bool.false_eq_true,ite_false,ite_true,one_smul] using he.symm
      · simpa only [chamberRepresentative,Bool.false_eq_true,ite_false,ite_true,one_smul] using he
      · rfl)

theorem chamberDoubleToOrbit_forget
    (hH : H.index=2) (hodd : ∀s:P.Side,S.generator s∉H)
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H) (q : S.Development) :
    S.chamberDoubleToOrbit H hH hodd hfix a ha (S.chamberDoubleForget H hfix q)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X (S.evaluation q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    let b:=S.chamberIndexLabel H p.1
    let ρ:=S.chamberRepresentative a b
    have he : S.chamberIndexLabel H p.1=S.chamberIndexLabel H ρ:=
      (S.chamberRepresentative_label H a ha b).symm
    have hk : p.1*ρ⁻¹∈H:=(S.chamberIndexLabel_eq_iff H hH p.1 ρ).mp he
    let k:H:=⟨p.1*ρ⁻¹,hk⟩
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X (ρ •
      p.2.val)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X (p.1 • p.2.val)
    have hh : p.1 • p.2.val=k • (ρ • p.2.val):=by
      change _=(p.1*ρ⁻¹) • (ρ • p.2.val)
      simp only [mul_smul,inv_smul_smul]
    rw [hh,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul]

section Topology
variable [TopologicalSpace X] [ContinuousConstSMul Γ X]
local instance reflectionDoubleGeneratedTopology : TopologicalSpace S.Generated:=⊥
local instance reflectionDoubleGeneratedDiscrete : DiscreteTopology S.Generated:=⟨rfl⟩

instance chamberDoubleTopology : TopologicalSpace S.ChamberDouble:=
  inferInstanceAs (TopologicalSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.BoundaryDouble P.Point
    {p|p.val∈P.boundary}))

omit [ContinuousConstSMul Γ X] in
theorem continuous_chamberDoublePoint : Continuous S.chamberDoublePoint:=continuous_quot_mk

omit [ContinuousConstSMul Γ X] in
theorem continuous_chamberDoubleForget
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x) :
    Continuous (S.chamberDoubleForget H hfix) := by
  apply continuous_quot_lift
  apply continuous_prod_of_discrete_left.mpr
  intro g
  change Continuous (fun x:P.Point=>S.chamberDoublePoint (S.chamberIndexLabel H g,x))
  exact S.continuous_chamberDoublePoint.comp (continuous_const.prodMk continuous_id)

theorem continuous_chamberDoubleToOrbit
    (hH : H.index=2) (hodd : ∀s:P.Side,S.generator s∉H)
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H) :
    Continuous (S.chamberDoubleToOrbit H hH hodd hfix a ha) := by
  apply continuous_quot_lift
  apply continuous_prod_of_discrete_left.mpr
  intro b
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_continuous H X).comp
    ((continuous_const_smul (S.chamberRepresentative a b : Γ)).comp continuous_subtype_val)

/-- The actual subgroup-orbit inverse is obtained from the genuine global development, not from an assigned quotient relation. -/
def orbitToChamberDouble
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H X → S.ChamberDouble:=
  Quotient.lift (fun x:X=>S.chamberDoubleForget H hfix (E.symm x)) (by
    intro x y h
    obtain ⟨g,hg⟩:=h
    have hh : E.symm x=g.val • E.symm y:=by
      apply E.injective
      rw [E.apply_symm_apply,he,S.evaluation_smul,←he,E.apply_symm_apply]
      exact hg.symm
    rw [hh,S.chamberDoubleForget_smul])

omit [ContinuousConstSMul Γ X] in
theorem chamberDoubleToOrbit_orbitToChamberDouble
    (hH : H.index=2) (hodd : ∀s:P.Side,S.generator s∉H)
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H)
    (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q)
    (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H X) :
    S.chamberDoubleToOrbit H hH hodd hfix a ha (S.orbitToChamberDouble H hfix E he q)=q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change S.chamberDoubleToOrbit H hH hodd hfix a ha
      (S.chamberDoubleForget H hfix (E.symm
        x))=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H X x
    rw [S.chamberDoubleToOrbit_forget,←he,E.apply_symm_apply]

omit [ContinuousConstSMul Γ X] in
theorem orbitToChamberDouble_chamberDoubleToOrbit
    (hH : H.index=2) (hodd : ∀s:P.Side,S.generator s∉H)
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H)
    (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q)
    (q : S.ChamberDouble) :
    S.orbitToChamberDouble H hfix E he (S.chamberDoubleToOrbit H hH hodd hfix a ha q)=q := by
  induction q using Quotient.inductionOn with
  | h p =>
    have hh : E.symm (S.chamberRepresentative a p.1 • p.2.val)=
        S.project (S.chamberRepresentative a p.1,p.2):=by
      apply E.injective
      rw [E.apply_symm_apply,he,S.evaluation_project]
      rfl
    change S.chamberDoubleForget H hfix
      (E.symm (S.chamberRepresentative a p.1 • p.2.val))=S.chamberDoublePoint p
    rw [hh,S.chamberDoubleForget_project]
    change S.chamberDoublePoint (S.chamberIndexLabel H (S.chamberRepresentative a p.1),p.2)=_
    rw [S.chamberRepresentative_label H a ha]

omit [ContinuousConstSMul Γ X] in
theorem continuous_orbitToChamberDouble
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    Continuous (S.orbitToChamberDouble H hfix E he) :=
  continuous_quot_lift _ ((S.continuous_chamberDoubleForget H hfix).comp E.symm.continuous)

/-- The actual index-two chamber subgroup orbit space is homeomorphic to the literal boundary double.
All generating side maps are genuine pointwise-fixed reflections, and the global evaluation is supplied explicitly. -/
def reflectionChamberOrbitHomeomorph
    (hH : H.index=2) (hodd : ∀s:P.Side,S.generator s∉H)
    (hfix : ∀s:P.Side,∀x∈s.val,S.generator s • x=x)
    (a : S.Generated) (ha : a∉H)
    (E : S.Development≃ₜX) (he : ∀q,E q=S.evaluation q) :
    S.ChamberDouble≃ₜ_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H X where
  toEquiv:={
    toFun:=S.chamberDoubleToOrbit H hH hodd hfix a ha
    invFun:=S.orbitToChamberDouble H hfix E he
    left_inv:=S.orbitToChamberDouble_chamberDoubleToOrbit H hH hodd hfix a ha E he
    right_inv:=S.chamberDoubleToOrbit_orbitToChamberDouble H hH hodd hfix a ha E he }
  continuous_toFun:=S.continuous_chamberDoubleToOrbit H hH hodd hfix a ha
  continuous_invFun:=S.continuous_orbitToChamberDouble H hfix E he

end Topology
end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
