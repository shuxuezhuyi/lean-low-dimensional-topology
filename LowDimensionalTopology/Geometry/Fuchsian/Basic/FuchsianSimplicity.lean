/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
@[expose] public section
noncomputable section
open Set
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Simplicity uses the entire actual hyperbolic axis and the actual Poincare action. -/
def IsSimple (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  f ∈ H ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f ∧ ∀ g ∈ H,
    (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f ∨
    Disjoint ((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • x) ''
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis
      f) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f)

/-- The equivalent formulation refers to the genuine axes of the actual conjugates. -/
theorem isSimple_iff_conjugate_axes (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    IsSimple H f ↔ f ∈ H ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f ∧ ∀ g ∈ H,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (g*f*g⁻¹)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f ∨
      Disjoint (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (g*f*g⁻¹)) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f) := by
  simp only [IsSimple,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_conjugation]

/-- A nonsimple hyperbolic has a genuine crossing translate, with an actual point on both axes. -/
theorem not_isSimple_iff_crossing (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f ∈ H) (hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    ¬IsSimple H f ↔ ∃ g ∈ H,
      (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g•x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f ≠ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f ∧
      ∃ x ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f, g•x ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f := by
  constructor
  · intro hn
    have he : ∃ g ∈ H, ¬((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace
      => g•x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f ∨
      Disjoint ((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g•x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f)) := by
      by_contra hc
      push Not at hc
      exact hn ⟨hf,hh,hc⟩
    rcases he with ⟨g,hg,h⟩
    have hne := (not_or.mp h).1
    have hi := (Set.not_disjoint_iff.mp (not_or.mp h).2)
    rcases hi with ⟨y,⟨x,hx,rfl⟩,hy⟩
    exact ⟨g,hg,hne,x,hx,hy⟩
  · rintro ⟨g,hg,hne,x,hx,hgx⟩ hs
    rcases hs.2.2 g hg with he | hd
    · exact hne he
    · exact Set.disjoint_left.mp hd ⟨x,hx,rfl⟩ hgx


/-- The actual subgroup preserving the entire geometric axis. -/
def axisSetStabilizer (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := H ⊓ MulAction.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f)

/-- The genuine native stabilizer-orbit quotient of the entire actual axis. -/
abbrev AxisQuotient (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  _root_.Quotient ((MulAction.orbitRel
    (axisSetStabilizer H f) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace).comap
      (Subtype.val : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f →
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace))

/-- The canonical map into the full actual Poincare orbit quotient. -/
def axisOrbitMap (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    AxisQuotient H f → _root_.Quotient (MulAction.orbitRel H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :=
  _root_.Quotient.lift (fun x : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f =>
    _root_.Quotient.mk _ x.val)
    (by
      intro x y h
      rcases h with ⟨g,hg⟩
      exact _root_.Quotient.sound ⟨⟨g.val,g.property.1⟩,hg⟩)

/-- Simplicity makes the actual stabilizer-orbit map injective. -/
theorem IsSimple.axisOrbitMap_injective {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hs : IsSimple H f) : Function.Injective (axisOrbitMap H f) := by
  intro a b hab
  induction a using _root_.Quotient.inductionOn with
  | h x =>
    induction b using _root_.Quotient.inductionOn with
    | h y =>
      obtain ⟨g,hg⟩ := _root_.Quotient.exact hab
      have hgy : g.val • y.val = x.val := hg
      have hst : (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g.val•p) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f := by
        rcases hs.2.2 g.val g.property with he | hd
        · exact he
        · exact False.elim (Set.disjoint_left.mp hd ⟨y.val,y.property,hgy⟩ x.property)
      apply _root_.Quotient.sound
      exact ⟨⟨g.val,⟨g.property,hst⟩⟩,hgy⟩

/-- Without elliptics the actual Poincare action is free at every interior point. -/
theorem noElliptics_H3_free (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) (g : H) (x :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hx : g.val•x=x) : g.val=1 := by
  by_contra hn
  exact hno g.val g.property ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_iff_H3_fixed g.val hn).mpr
    ⟨x,hx⟩)

/-- Injectivity of the actual orbit map forces simplicity for every elliptic-free group. -/
theorem isSimple_of_axisOrbitMap_injective (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ H) (hh :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f)
    (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) (hinj : Function.Injective
      (axisOrbitMap H f)) :
    IsSimple H f := by
  refine ⟨hf,hh,?_⟩
  intro g hg
  by_cases he : (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g•p) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f
  · exact Or.inl he
  · right
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hgx
    let a : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f := ⟨g•x,hgx⟩
    let b : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f := ⟨x,hx⟩
    have hab : axisOrbitMap H f (_root_.Quotient.mk _ a)=
        axisOrbitMap H f (_root_.Quotient.mk _ b) := _root_.Quotient.sound ⟨⟨g,hg⟩,rfl⟩
    obtain ⟨k,hk⟩ := _root_.Quotient.exact (hinj hab)
    have hkx : k.val•x=g•x := hk
    have hfree : k.val⁻¹*g=1 := noElliptics_H3_free H hno
      ⟨k.val⁻¹*g,H.mul_mem (H.inv_mem k.property.1) hg⟩ x (by rw [mul_smul,←hkx,inv_smul_smul])
    have hkg : g=k.val := by
      calc
        g=k.val*(k.val⁻¹*g) := by group
        _=k.val := by rw [hfree,mul_one]
    exact he (hkg.symm ▸ k.property.2)

/-- The actual native quotient map detects exactly the simple/non-simple dichotomy. -/
theorem isSimple_iff_axisOrbitMap_injective (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ H) (hh :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f)
    (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    IsSimple H f ↔ Function.Injective (axisOrbitMap H f) :=
  ⟨fun h => h.axisOrbitMap_injective,isSimple_of_axisOrbitMap_injective H f hf hh hno⟩


/-- Transport an actual subset by the actual conjugate action. -/
theorem H3_conjugate_image (q g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      (q*g*q⁻¹)•x) '' ((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      q•x) '' S)=
    (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q•x) '' ((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g•x) '' S) := by
  rw [image_image,image_image]
  congr 1
  funext x
  simp only [mul_smul,inv_smul_smul]

/-- Simplicity is preserved by actual simultaneous conjugation of the group and element. -/
theorem IsSimple.conjugate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hs : IsSimple H f) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    IsSimple (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q*f*q⁻¹) := by
  refine ⟨(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
    ⟨f,hs.1,rfl⟩,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f q hs.2.1,?_⟩
  intro a ha
  obtain ⟨g,hg,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
    H a).mp ha
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_conjugation,H3_conjugate_image]
  rcases hs.2.2 g hg with he | hd
  · exact Or.inl (congrArg (fun S : Set
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (fun x :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q•x) '' S) he)
  · exact Or.inr ((Set.disjoint_image_iff (MulAction.injective q)).mpr hd)

/-- A simple element remains simple in every intermediate subgroup containing it. -/
theorem IsSimple.subgroup {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hs : IsSimple H f) (hKH : K ≤ H) (hf : f ∈ K) : IsSimple K f :=
  ⟨hf,hs.2.1,fun g hg => hs.2.2 g (hKH hg)⟩

/-- Nonsimplicity persists under enlargement of the acting group. -/
theorem not_isSimple_of_subgroup {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hKH : K ≤ H) (hf : f ∈ K) (hn : ¬IsSimple K f) : ¬IsSimple H f := by
  intro hs
  exact hn (hs.subgroup hKH hf)

/-- Every hyperbolic axis is nonempty and has a genuine complete metric parametrization. -/
theorem IsSimple.axis_nonempty {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hs : IsSimple H f) : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis f).Nonempty := by
  obtain ⟨γ,hγ,_⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_metric_param f hs.2.1.1.1 hs.2.1.1.not_parabolic
  rw [←hγ]
  exact Set.range_nonempty γ

end LowDimensionalTopology.Geometry.Fuchsian
