module

public import LowDimensionalTopology.Geometry.Teichmuller.MappingClass
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Action.End

/-!
# The mapping class group of a closed Riemann surface

Orientation-preserving real smooth automorphisms form a genuine group. The
automorphisms freely homotopic to the identity form a normal subgroup. Its
quotient acts on marked complex structures by inverse precomposition.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- Differentiating an existing local inverse preserves the positive Jacobian sign. -/
theorem openPartialHomeomorph_realJacobian_symm_pos
    (F : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z ∈ F.target)
    (hpos : 0 < realJacobian F (F.symm z)) : 0 < realJacobian F.symm z := by
  let D := fderiv ℝ F (F.symm z)
  have hdet : D.det ≠ 0 := hpos.ne'
  let E := D.toContinuousLinearEquivOfDetNeZero hdet
  have hE : (E : ℂ →L[ℝ] ℂ) = D :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero D hdet
  have hF : HasFDerivAt F (E : ℂ →L[ℝ] ℂ) (F.symm z) := by
    rw [hE]
    exact (differentiableAt_of_realJacobian_pos hpos).hasFDerivAt
  have hInv : HasFDerivAt F.symm (E.symm : ℂ →L[ℝ] ℂ) z :=
    HasFDerivAt.of_local_left_inverse (F.symm.continuousAt hz) hF
      (F.eventually_right_inverse hz)
  have hcancel : (E : ℂ →L[ℝ] ℂ).toLinearMap.comp
      (E.symm : ℂ →L[ℝ] ℂ).toLinearMap = LinearMap.id := by
    ext w
    exact E.apply_symm_apply w
  have hmul : realJacobian F (F.symm z) * realJacobian F.symm z = 1 := by
    unfold realJacobian
    rw [hInv.fderiv]
    change D.toLinearMap.det * (E.symm : ℂ →L[ℝ] ℂ).toLinearMap.det = 1
    rw [← hE, ← LinearMap.det_comp, hcancel, LinearMap.det_id]
  exact pos_of_mul_pos_right (hmul.symm ▸ zero_lt_one) hpos.le

/-- A homeomorphism preserving the complex orientations has orientation-preserving inverse. -/
theorem PreservesComplexOrientation.homeomorph_symm
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} (h : X ≃ₜ Y)
    (hh : PreservesComplexOrientation A B h) :
    PreservesComplexOrientation B A h.symm := by
  intro e he c hc z hz
  let F := riemannHomeomorphChart c h e
  have hzF : z ∈ F.target := by
    change z ∈ (riemannHomeomorphChart c h e).target
    rwa [riemannHomeomorphChart_target]
  have hxF : F.symm z ∈ riemannChartMapDomain c h e := by
    rw [← riemannHomeomorphChart_source]
    exact F.map_target hzF
  have hpos : 0 < realJacobian F (F.symm z) := hh c hc e he (F.symm z) hxF
  change 0 < realJacobian F.symm z
  exact openPartialHomeomorph_realJacobian_symm_pos F z hzF hpos

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : RiemannSurface X} {B : RiemannSurface Y}

/-- The actual inverse real smooth diffeomorphism. -/
def symm (f : SmoothSurfaceEquiv A B) : SmoothSurfaceEquiv B A := by
  letI := A.toRiemannAtlas.toChartedSpace
  letI := B.toRiemannAtlas.toChartedSpace
  exact Diffeomorph.symm f

@[simp]
theorem symm_toHomeomorph (f : SmoothSurfaceEquiv A B) :
    (symm f).toHomeomorph = f.toHomeomorph.symm := rfl

end SmoothSurfaceEquiv

/-- An orientation-preserving smooth automorphism of a closed reference surface. -/
structure OrientedSurfaceAut {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) where
  smooth : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface
  orientation_preserving :
    PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas smooth.toHomeomorph

namespace OrientedSurfaceAut

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The underlying homeomorphism, with its original topology. -/
def toHomeomorph (f : OrientedSurfaceAut R) : X ≃ₜ X := f.smooth.toHomeomorph

/-- The underlying continuous self-map. -/
def continuousMap (f : OrientedSurfaceAut R) : C(X, X) :=
  _root_.toContinuousMap f.toHomeomorph

@[ext]
theorem ext {f g : OrientedSurfaceAut R} (h : ∀ x, f.toHomeomorph x = g.toHomeomorph x) :
    f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfg : f = g := by
            let := R.toRiemannAtlas.toChartedSpace
            apply Diffeomorph.ext
            exact h
          subst g
          rfl

instance (R : ClosedRiemannSurface X) : Group (OrientedSurfaceAut R) where
  one :=
    ⟨SmoothSurfaceEquiv.refl R.toRiemannSurface,
      preservesComplexOrientation_id R.toRiemannAtlas⟩
  mul f g :=
    ⟨SmoothSurfaceEquiv.trans g.smooth f.smooth,
      f.orientation_preserving.comp g.orientation_preserving g.toHomeomorph.continuous⟩
  inv f :=
    ⟨SmoothSurfaceEquiv.symm f.smooth,
      PreservesComplexOrientation.homeomorph_symm f.toHomeomorph f.orientation_preserving⟩
  mul_assoc f g h := by
    apply ext
    intro x
    rfl
  one_mul f := by
    apply ext
    intro x
    rfl
  mul_one f := by
    apply ext
    intro x
    rfl
  inv_mul_cancel f := by
    apply ext
    intro x
    exact f.toHomeomorph.symm_apply_apply x

@[simp]
theorem toHomeomorph_one : (1 : OrientedSurfaceAut R).toHomeomorph = Homeomorph.refl X := rfl

@[simp]
theorem toHomeomorph_mul (f g : OrientedSurfaceAut R) :
    (f * g).toHomeomorph = f.toHomeomorph * g.toHomeomorph := rfl

@[simp]
theorem toHomeomorph_inv (f : OrientedSurfaceAut R) :
    (f⁻¹).toHomeomorph = f.toHomeomorph.symm := rfl

@[simp]
theorem continuousMap_one : (1 : OrientedSurfaceAut R).continuousMap = ContinuousMap.id X := rfl

@[simp]
theorem continuousMap_mul (f g : OrientedSurfaceAut R) :
    (f * g).continuousMap = f.continuousMap.comp g.continuousMap := rfl

/-- Forgetting smoothness and the orientation proof is a group homomorphism. -/
def toHomeomorphHom (R : ClosedRiemannSurface X) : OrientedSurfaceAut R →* (X ≃ₜ X) where
  toFun := toHomeomorph
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The subgroup of reference automorphisms freely homotopic to the identity. -/
def homotopyIdentitySubgroup (R : ClosedRiemannSurface X) : Subgroup (OrientedSurfaceAut R) where
  carrier := {f | ContinuousMap.Homotopic f.continuousMap (ContinuousMap.id X)}
  one_mem' := ContinuousMap.Homotopic.refl (ContinuousMap.id X)
  mul_mem' := by
    intro f g hf hg
    exact hf.comp hg
  inv_mem' := by
    intro f hf
    have hc := (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap f.toHomeomorph.symm)).comp hf
    have hcancel : (_root_.toContinuousMap f.toHomeomorph.symm).comp f.continuousMap =
        ContinuousMap.id X := by
      ext x
      exact f.toHomeomorph.symm_apply_apply x
    rw [hcancel] at hc
    exact hc.symm

instance (R : ClosedRiemannSurface X) : (homotopyIdentitySubgroup R).Normal where
  conj_mem := by
    intro n hn g
    change ContinuousMap.Homotopic n.continuousMap (ContinuousMap.id X) at hn
    have hc := (ContinuousMap.Homotopic.refl g.continuousMap).comp
      (hn.comp (ContinuousMap.Homotopic.refl
        (_root_.toContinuousMap g.toHomeomorph.symm)))
    have hcancel : g.continuousMap.comp
        ((ContinuousMap.id X).comp (_root_.toContinuousMap g.toHomeomorph.symm)) =
        ContinuousMap.id X := by
      ext x
      exact g.toHomeomorph.apply_symm_apply x
    rw [hcancel] at hc
    exact hc

/-- Left action on marked complex structures, using inverse precomposition. -/
instance (R : ClosedRiemannSurface X) :
    MulAction (OrientedSurfaceAut R) (TeichmullerSpace.{u, v} R) where
  smul f p := TeichmullerSpace.precompose (f⁻¹).smooth (f⁻¹).orientation_preserving p
  one_smul p := by
    change TeichmullerSpace.precompose (SmoothSurfaceEquiv.refl R.toRiemannSurface)
      (preservesComplexOrientation_id R.toRiemannAtlas) p = p
    exact TeichmullerSpace.precompose_refl p
  mul_smul f g p := by
    symm
    exact TeichmullerSpace.precompose_trans (f⁻¹).smooth (g⁻¹).smooth
      (f⁻¹).orientation_preserving (g⁻¹).orientation_preserving p

/-- The homotopy identity subgroup acts trivially on Teichmüller points. -/
theorem homotopyIdentity_le_actionKer (R : ClosedRiemannSurface X) :
    homotopyIdentitySubgroup R ≤
      (MulAction.toPermHom (OrientedSurfaceAut R) (TeichmullerSpace.{u, v} R)).ker := by
  intro f hf
  change (MulAction.toPermHom (OrientedSurfaceAut R)
    (TeichmullerSpace.{u, v} R)) f = 1
  apply Equiv.ext
  intro p
  change TeichmullerSpace.precompose (f⁻¹).smooth (f⁻¹).orientation_preserving p = p
  have hinv : ContinuousMap.Homotopic (f⁻¹).continuousMap (ContinuousMap.id X) :=
    (homotopyIdentitySubgroup R).inv_mem hf
  exact (TeichmullerSpace.precompose_eq_of_homotopic (f⁻¹).smooth
    (SmoothSurfaceEquiv.refl R.toRiemannSurface) (f⁻¹).orientation_preserving
    (preservesComplexOrientation_id R.toRiemannAtlas) hinv p).trans
      (TeichmullerSpace.precompose_refl p)

end OrientedSurfaceAut

/-- The mapping class group, defined using the actual homotopy identity subgroup. -/
abbrev MappingClassGroup {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :=
  OrientedSurfaceAut R ⧸ OrientedSurfaceAut.homotopyIdentitySubgroup R

namespace MappingClassGroup

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The class of an orientation-preserving smooth reference automorphism. -/
def mk (f : OrientedSurfaceAut R) : MappingClassGroup R := QuotientGroup.mk f

/-- Equality of mapping classes is exactly free homotopy of the representatives. -/
theorem mk_eq_mk_iff_homotopic (f g : OrientedSurfaceAut R) :
    mk f = mk g ↔ ContinuousMap.Homotopic f.continuousMap g.continuousMap := by
  constructor
  · intro h
    have hrel := QuotientGroup.eq_iff_div_mem.mp h
    change ContinuousMap.Homotopic (f / g).continuousMap (ContinuousMap.id X) at hrel
    have hc := hrel.comp (ContinuousMap.Homotopic.refl g.continuousMap)
    have hcancel : (f / g).continuousMap.comp g.continuousMap = f.continuousMap := by
      ext x
      change f.toHomeomorph (g.toHomeomorph.symm (g.toHomeomorph x)) = f.toHomeomorph x
      rw [g.toHomeomorph.symm_apply_apply]
    rw [hcancel] at hc
    exact hc
  · intro h
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ContinuousMap.Homotopic (f / g).continuousMap (ContinuousMap.id X)
    have hc := h.comp (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap g.toHomeomorph.symm))
    have hcancel : g.continuousMap.comp (_root_.toContinuousMap g.toHomeomorph.symm) =
        ContinuousMap.id X := by
      ext x
      exact g.toHomeomorph.apply_symm_apply x
    rw [hcancel] at hc
    exact hc

/-- The permutation representation descended from changing smooth markings. -/
def representation (R : ClosedRiemannSurface X) :
    MappingClassGroup R →* Equiv.Perm (TeichmullerSpace.{u, v} R) :=
  QuotientGroup.lift (OrientedSurfaceAut.homotopyIdentitySubgroup R)
    (MulAction.toPermHom (OrientedSurfaceAut R) (TeichmullerSpace.{u, v} R))
    (OrientedSurfaceAut.homotopyIdentity_le_actionKer R)

/-- The mapping class group acts on the original marked-surface quotient. -/
instance (R : ClosedRiemannSurface X) :
    MulAction (MappingClassGroup R) (TeichmullerSpace.{u, v} R) :=
  MulAction.compHom (TeichmullerSpace.{u, v} R) (representation R)

@[simp]
theorem mk_smul (f : OrientedSurfaceAut R) (p : TeichmullerSpace.{u, v} R) :
    mk f • p = TeichmullerSpace.precompose (f⁻¹).smooth (f⁻¹).orientation_preserving p := rfl

end MappingClassGroup

end LowDimensionalTopology.Geometry.Teichmuller
