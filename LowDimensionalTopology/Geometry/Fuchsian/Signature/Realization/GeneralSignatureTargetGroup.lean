/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureSidePairingProfile
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- These are precisely the middle cut sides of the literal boundary triples. -/
def generalCoreIsCutSide (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) : Prop :=
  let p := (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length
  p ≤ i.val ∧ (i.val - p) % 3 = 1

/-- Each retained generator is the actual original native side-pairing isometry. -/
def generalCoreTargetGenerator (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
    (i : Fin (generalCoreAngles g orders s t).length) : ℍ ≃ᵢ ℍ :=
  cofiniteTangentPairingElement (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd hb i (generalCoreAuxPairing g orders s t i)

/-- The target group retains exactly the true sides and omits all cut half-turns.
It is not assigned a signature until its actual full class census is proved. -/
def generalCoreTargetGroup (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure (range (fun i : {i : Fin (generalCoreAngles g orders s t).length //
      ¬ generalCoreIsCutSide g orders s t i} =>
    generalCoreTargetGenerator g orders s t ho hdef d hd hb i.val))

theorem generalCoreTargetGroup_le_aux (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    generalCoreTargetGroup g orders s t ho hdef d hd hb ≤
      (generalCoreAuxSidePairing g orders s t ho hdef d hd hb).Generated := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  let θ := generalCoreTheta g orders s t
  let hθ := generalCoreTheta_mem g orders s t ho hdef
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S := generalCoreAuxSidePairing g orders s t ho hdef d hd hb
  let E := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q
  have hmem : S.element (E i.val) ∈ S.Generated := (S.generator (E i.val)).property
  change cofiniteTangentPairingElement θ d hθ hd hb (E.symm (E i.val))
    (generalCoreAuxPairing g orders s t (E.symm (E i.val))) ∈ S.Generated at hmem
  simpa only [SetLike.mem_coe, Equiv.symm_apply_apply, generalCoreTargetGenerator, θ, hθ, S] using hmem

/-- The actual retained original generators form a finite generating set. -/
theorem generalCoreTargetGroup_fg (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    (generalCoreTargetGroup g orders s t ho hdef d hd hb).FG := by
  apply (Subgroup.fg_iff _).mpr
  exact ⟨_, rfl, finite_range _⟩

/-- The actual target group inherits discreteness from the proved auxiliary
cofinite tessellation, without postulating a target fundamental domain. -/
theorem generalCoreTargetGroup_discrete (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    DiscreteTopology (generalCoreTargetGroup g orders s t ho hdef d hd hb) :=
  isDiscrete_iff_discreteTopology.mp ((isDiscrete_iff_discreteTopology.mpr
    (generalCore_auxiliary_poincare g orders s t ho hdef d hd hb).1).mono
      (generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb))

end LowDimensionalTopology.Geometry.Fuchsian
