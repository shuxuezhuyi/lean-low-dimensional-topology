module

public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# One-path transport of genuine based generator classes

The ordered generators are elements of the actual fundamental group at an
arbitrary original basepoint. Their image classes are compared through one
actual path between the two image basepoints. This definition does not assert
that an arbitrary generating family is a geometric canonical cut system.
-/

@[expose] public section
noncomputable section

open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Both image markings agree after transport through ONE common actual path. -/
def GeneratorMapsTransported (f g : C(X, Y)) (x : X)
    (sigma : Fin 2 → FundamentalGroup X x) : Prop :=
  ∃ C : Path (f x) (g x), ∀ i,
    FundamentalGroup.fundamentalGroupMulEquivOfPath C
      (FundamentalGroup.map f x (sigma i)) = FundamentalGroup.map g x (sigma i)

/-- The group-class transport equation is exactly the corresponding actual
path homotopy square, including the order of its two concatenations. -/
theorem basedLoop_transport_iff (f g : C(X, Y)) (x : X)
    (C : Path (f x) (g x)) (l : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath C
        (FundamentalGroup.map f x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l))) =
      FundamentalGroup.map g x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l)) ↔
    Path.Homotopic ((l.map f.continuous).trans C) (C.trans (l.map g.continuous)) := by
  rw [TauCeti.FundamentalGroup.map_fromPath, TauCeti.FundamentalGroup.map_fromPath]
  constructor
  · intro h
    rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply] at h
    have hq := congrArg CategoryTheory.End.asHom h
    change (Path.Homotopic.Quotient.mk C).symm.trans
      ((Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
        (Path.Homotopic.Quotient.mk C)) = Path.Homotopic.Quotient.mk (l.map g.continuous) at hq
    have he := congrArg (fun q => (Path.Homotopic.Quotient.mk C).trans q) hq
    apply Path.Homotopic.Quotient.eq.mp
    simpa only [Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans] using he
  · intro h
    have hq := Path.Homotopic.Quotient.eq.mpr h
    simp only [Path.Homotopic.Quotient.mk_trans] at hq
    have he := congrArg (fun q => (Path.Homotopic.Quotient.mk C).symm.trans q) hq
    rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
    apply CategoryTheory.End.ext
    change (Path.Homotopic.Quotient.mk C).symm.trans
      ((Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
        (Path.Homotopic.Quotient.mk C)) = Path.Homotopic.Quotient.mk (l.map g.continuous)
    simpa only [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] using he

/-- A genuine homotopy transports every original loop class by its actual
basepoint trace; the same trace works for all generators. -/
theorem homotopy_basedLoop_transport (f g : C(X, Y)) (H : f.Homotopy g) (x : X)
    (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt x)
      (FundamentalGroup.map f x a) = FundamentalGroup.map g x a := by
  rcases a with ⟨a⟩
  induction a using Path.Homotopic.Quotient.ind with
  | mk l =>
    exact (basedLoop_transport_iff f g x (H.evalAt x) l).mpr
      (Path.Homotopic.map_trans_evalAt H l)

/-- The image relation is a consequence of genuine map homotopy, for any
ordered family of actual loop classes. -/
theorem GeneratorMapsTransported.of_homotopic {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) (x : X) (sigma : Fin 2 → FundamentalGroup X x) :
    GeneratorMapsTransported f g x sigma := by
  obtain ⟨H⟩ := h
  exact ⟨H.evalAt x, fun i => homotopy_basedLoop_transport f g H x (sigma i)⟩

/-- Agreement on a genuine generating pair implies agreement on the ENTIRE
actual fundamental group, with the same one transporting path. -/
theorem GeneratorMapsTransported.all {f g : C(X, Y)} {x : X}
    {sigma : Fin 2 → FundamentalGroup X x}
    (hgen : Subgroup.closure (Set.range sigma) = ⊤)
    (h : GeneratorMapsTransported f g x sigma) :
    ∃ C : Path (f x) (g x), ∀ a : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map f x a) =
        FundamentalGroup.map g x a := by
  obtain ⟨C, hC⟩ := h
  let A := (FundamentalGroup.fundamentalGroupMulEquivOfPath C).toMonoidHom.comp
    (FundamentalGroup.map f x)
  let B := FundamentalGroup.map g x
  have he : A = B := MonoidHom.eq_of_eqOn_dense hgen (by
    rintro _ ⟨i, rfl⟩
    exact hC i)
  exact ⟨C, fun a => DFunLike.congr_fun he a⟩

/-- Actual induced maps commute with basepoint transport through the image
of that same path. This is proved on genuine path-quotient representatives. -/
theorem fundamentalGroup_map_basepoint_natural (v : C(Y, Z)) {a b : Y}
    (C : Path a b) (gamma : FundamentalGroup Y a) :
    FundamentalGroup.map v b (FundamentalGroup.fundamentalGroupMulEquivOfPath C gamma) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (C.map v.continuous)
        (FundamentalGroup.map v a gamma) := by
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl (x := b) v,
    ← TauCeti.FundamentalGroup.mapOfEq_rfl (x := a) v]
  rcases gamma with ⟨gamma⟩
  induction gamma using Path.Homotopic.Quotient.ind with
  | mk gamma =>
    apply CategoryTheory.End.ext
    simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
      FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
      ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
      ← Path.Homotopic.Quotient.mk_map, Path.map_trans, ← Path.map_symm]

/-- Pull back the all-loop transport statement through a real continuous
map, with the basepoint equation proved rather than imposed on the caller. -/
theorem basedLoop_transport_precompose {f g : C(X, Y)} {x : X}
    (C : Path (f x) (g x))
    (h : ∀ a : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map f x a) =
        FundamentalGroup.map g x a)
    (u : C(Z, X)) (z : Z) (hz : u z = x) :
    ∃ D : Path ((f.comp u) z) ((g.comp u) z), ∀ a : FundamentalGroup Z z,
      FundamentalGroup.fundamentalGroupMulEquivOfPath D
        (FundamentalGroup.map (f.comp u) z a) = FundamentalGroup.map (g.comp u) z a := by
  cases hz
  refine ⟨C, fun a => ?_⟩
  simpa only [FundamentalGroup.map_comp, MonoidHom.comp_apply] using
    h (FundamentalGroup.map u z a)

/-- Push forward all-loop transport through an actual continuous target map. -/
theorem basedLoop_transport_postcompose {f g : C(X, Y)} {x : X}
    (C : Path (f x) (g x))
    (h : ∀ a : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map f x a) =
        FundamentalGroup.map g x a) (v : C(Y, Z)) :
    ∀ a : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath (C.map v.continuous)
        (FundamentalGroup.map (v.comp f) x a) = FundamentalGroup.map (v.comp g) x a := by
  intro a
  rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, MonoidHom.comp_apply,
    MonoidHom.comp_apply, ← fundamentalGroup_map_basepoint_natural]
  exact congrArg (FundamentalGroup.map v (g x)) (h a)

end LowDimensionalTopology.Geometry.Surfaces
