/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.HandleModels
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.LeanEval.ChallengeDeps
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces
open LeanEval.Topology.ClassificationOfSurfaces

/-- Both actual circular polygon conventions use precisely the same boundary point. -/
theorem leanPool_boundaryPoint_eq (r : ℝ) :
    Complex.ClosedUnitDisc.bdyPtOfReal r=handleBoundaryPoint r := rfl

/-- The closed orientable LeanPool relation is exactly the pre-existing actual oriented handle pairing. -/
theorem leanPool_orientableRel_zero_iff (g : ℕ)
    (z w : Metric.closedBall (0 : ℂ) 1) :
    OrientableRel g 0 z w↔CanonicalHandleIdent g z w := by
  constructor
  · intro h
    cases h with
    | a x i => simpa only [leanPool_boundaryPoint_eq,Nat.cast_zero,mul_zero,add_zero] using _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.a x i
    | b x i => simpa only [leanPool_boundaryPoint_eq,Nat.cast_zero,mul_zero,add_zero] using _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.b x i
    | c x i => exact Fin.elim0 i
  · intro h
    cases h with
    | a x i => simpa only [leanPool_boundaryPoint_eq,Nat.cast_zero,mul_zero,add_zero] using OrientableRel.a (n:=0) x i
    | b x i => simpa only [leanPool_boundaryPoint_eq,Nat.cast_zero,mul_zero,add_zero] using OrientableRel.b (n:=0) x i

/-- Identity of the actual carriers induces the genuine closed oriented polygon quotient homeomorphism. -/
def leanPoolClosedOrientableHomeomorph (g : ℕ) :
    Quot (OrientableRel g 0)≃ₜQuot (CanonicalHandleIdent g) where
  toFun:=Quot.lift (Quot.mk _) (fun z w h=>Quot.sound ((leanPool_orientableRel_zero_iff g z w).mp h))
  invFun:=Quot.lift (Quot.mk _) (fun z w h=>Quot.sound ((leanPool_orientableRel_zero_iff g z w).mpr h))
  left_inv q:=by induction q using Quot.inductionOn; rfl
  right_inv q:=by induction q using Quot.inductionOn; rfl
  continuous_toFun:=continuous_quot_lift _ continuous_quot_mk
  continuous_invFun:=continuous_quot_lift _ continuous_quot_mk

/-- A verified closed orientable positive-handle normal form has the actual project genus. -/
theorem hasTopologicalGenus_of_leanPool_closed_orientable {X : Type*} [TopologicalSpace X]
    {g : ℕ} (hg : 0<g) (e : X≃ₜQuot (OrientableRel g 0)) :
    HasTopologicalGenus X g := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  exact ⟨e.trans (leanPoolClosedOrientableHomeomorph (k+1))⟩

end LowDimensionalTopology.Geometry.Surfaces
