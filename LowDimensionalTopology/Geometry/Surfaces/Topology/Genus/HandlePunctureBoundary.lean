/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandlePuncturedRetraction
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandlePunctureCover
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundaryWord
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import Mathlib.Tactic.NormNum

/-!
# The actual puncture-circle attaching class

The radius-one-quarter circle lies in the overlap of the punctured surface and
its radius-one-half disc. Radial retraction sends it pointwise to the actual
polygon boundary, with its counterclockwise orientation preserved. Its positively
oriented once-around loop generates the entire overlap fundamental group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Topology ContinuousMap Multiplicative

namespace LowDimensionalTopology.Geometry.Surfaces.HandlePunctureBoundary

open HandlePresentation

/-- Fixed honest radii make the common basepoint and all maps completely explicit. -/
def circleEquiv (g : ℕ) : HandlePuncture.overlap g (1 / 2) ≃ₕ Circle :=
  HandlePuncture.overlapCircleHomotopyEquiv g (r := 1 / 2) (ρ := 1 / 4)
    (by norm_num) (by constructor <;> norm_num)

def circleToOverlap (g : ℕ) : C(Circle, HandlePuncture.overlap g (1 / 2)) :=
  (circleEquiv g).invFun

/-- The common point is the actual image of `1` on the radius-one-quarter circle. -/
def overlapBase (g : ℕ) : HandlePuncture.overlap g (1 / 2) :=
  circleToOverlap g 1

def overlapToPunctured (g : ℕ) : C(HandlePuncture.overlap g (1 / 2), Punctured g) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual inclusion into the punctured quotient followed by its radial retraction. -/
def boundaryFromOverlap (g : ℕ) : C(HandlePuncture.overlap g (1 / 2), Boundary g) :=
  (HandlePunctured.retractionMap g).comp (overlapToPunctured g)

/-- The unit circle as the actual boundary of the original complex disc. -/
def boundaryDisc (z : Circle) : Disc :=
  ⟨(z : ℂ), mem_closedBall_zero_iff.mpr (Circle.norm_coe z).le⟩

/-- The actual quotient boundary map; no abstract attaching map is substituted. -/
def boundaryCircle (g : ℕ) : C(Circle, Boundary g) :=
  ⟨fun z => ⟨projection g (boundaryDisc z),
    ⟨boundaryDisc z, Circle.norm_coe z, rfl⟩⟩,
    ((projection_continuous g).comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

@[simp] theorem boundaryCircle_one (g : ℕ) :
    boundaryCircle g 1 = boundaryBase g := by
  apply Subtype.ext
  apply congrArg (projection g)
  apply Subtype.ext
  simp [boundaryDisc, handleBoundaryPoint]

/-- The inverse homotopy-equivalence map really is the chosen small circle. -/
theorem circleToOverlap_val (g : ℕ) (z : Circle) :
    (circleToOverlap g z).val =
      projection g ⟨(1 / 4 : ℝ) • (z : ℂ), mem_closedBall_zero_iff.mpr (by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
          Circle.norm_coe, mul_one]
        norm_num)⟩ :=
  HandlePuncture.overlapCircleHomotopyEquiv_symm_val g (r := 1 / 2) (ρ := 1 / 4)
    (by norm_num) (by constructor <;> norm_num) z

/-- The common point is literally the positive real radius-one-quarter point. -/
theorem overlapBase_punctured (g : ℕ) :
    overlapToPunctured g (overlapBase g) =
      HandlePunctured.positiveRealPoint g (1 / 4) (by norm_num) (by norm_num) := by
  apply Subtype.ext
  change (overlapBase g).val = projection g
    (HandlePunctured.positiveRealDisc (1 / 4) (by norm_num) (by norm_num))
  rw [overlapBase, circleToOverlap_val]
  apply congrArg (projection g)
  apply Subtype.ext
  change (1 / 4 : ℝ) • (1 : ℂ) = ((1 / 4 : ℝ) : ℂ)
  rw [Complex.real_smul, mul_one]

/-- Radial retraction preserves the circle coordinate exactly, not merely up to homotopy. -/
theorem boundaryFromOverlap_circleToOverlap_apply (g : ℕ) (z : Circle) :
    boundaryFromOverlap g (circleToOverlap g z) = boundaryCircle g z := by
  apply Subtype.ext
  change HandlePunctured.radial g 1 (circleToOverlap g z).val =
    projection g (boundaryDisc z)
  rw [circleToOverlap_val, HandlePunctured.radial_projection]
  apply congrArg (projection g)
  apply Subtype.ext
  change (((1 : ℝ) - 1) + 1 / ‖(1 / 4 : ℝ) • (z : ℂ)‖) •
    ((1 / 4 : ℝ) • (z : ℂ)) = (z : ℂ)
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
    Circle.norm_coe, mul_one, sub_self, zero_add, smul_smul]
  norm_num

theorem boundaryFromOverlap_comp_circleToOverlap (g : ℕ) :
    (boundaryFromOverlap g).comp (circleToOverlap g) = boundaryCircle g :=
  ContinuousMap.ext (boundaryFromOverlap_circleToOverlap_apply g)

/-- The chosen common basepoint retracts to the actual polygon vertex. -/
@[simp] theorem boundaryFromOverlap_base (g : ℕ) :
    boundaryFromOverlap g (overlapBase g) = boundaryBase g := by
  rw [overlapBase, boundaryFromOverlap_circleToOverlap_apply, boundaryCircle_one]

/-- The mapped once-around circle path is exactly the actual polygon-boundary path. -/
theorem boundaryCircle_expLoop (g : ℕ) :
    ((Circle.expLoop.map (boundaryCircle g).continuous).cast
      (boundaryCircle_one g).symm (boundaryCircle_one g).symm) = boundaryLoop g := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change projection g (boundaryDisc (Circle.expLoop t)) =
    projection g (handleBoundaryPoint t.val)
  rw [Circle.expLoop_apply]
  rfl

/-- The induced map carries the positive circle generator to the actual boundary class. -/
theorem boundaryLoop_class (g : ℕ) :
    pathClass (boundaryLoop g) =
      FundamentalGroup.mapOfEq (boundaryCircle g) (boundaryCircle_one g)
        (pathClass Circle.expLoop) := by
  rw [← boundaryCircle_expLoop g]
  simp only [pathClass, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]

/-- The actual small counterclockwise loop in the overlap. -/
def overlapLoop (g : ℕ) : Path (overlapBase g) (overlapBase g) :=
  Circle.expLoop.map (circleToOverlap g).continuous

/-- Mapping this actual loop and retracting gives the polygon-boundary loop pointwise. -/
theorem overlapLoop_boundary (g : ℕ) :
    (((overlapLoop g).map (boundaryFromOverlap g).continuous).cast
      (boundaryFromOverlap_base g).symm (boundaryFromOverlap_base g).symm) =
        boundaryLoop g := by
  apply Path.ext
  funext t
  exact (boundaryFromOverlap_circleToOverlap_apply g (Circle.expLoop t)).trans
    (congrArg (fun p : Path (boundaryBase g) (boundaryBase g) => p t)
      (boundaryCircle_expLoop g))

/-- The actual overlap generator is the small counterclockwise circle, based at its point `1`. -/
def overlapGenerator (g : ℕ) :
    FundamentalGroup (HandlePuncture.overlap g (1 / 2)) (overlapBase g) :=
  FundamentalGroup.map (circleToOverlap g) 1 (pathClass Circle.expLoop)

@[simp] theorem overlapLoop_class (g : ℕ) :
    pathClass (overlapLoop g) = overlapGenerator g := by
  exact (TauCeti.FundamentalGroup.map_fromPath (circleToOverlap g) 1 Circle.expLoop).symm

/-- The chosen loop generates the whole overlap group, by the actual homotopy equivalence.
Its circle antecedent has positive degree one, as detected by the circle group isomorphism. -/
theorem overlapGenerator_zpowers_eq_top (g : ℕ) :
    Subgroup.zpowers (overlapGenerator g) = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  obtain ⟨b, rfl⟩ := ((circleEquiv g).symm.fundamentalGroup_map_bijective 1).surjective a
  let E := Circle.fundamentalGroupMulEquiv 1
  have hb : (pathClass Circle.expLoop) ^ (E b).toAdd = b := by
    apply E.injective
    rw [map_zpow]
    have hp : E (pathClass Circle.expLoop) = Multiplicative.ofAdd (1 : ℤ) :=
      Circle.fundamentalGroupMulEquiv_expLoop
    rw [hp, ← ofAdd_zsmul, zsmul_one, Int.cast_id, ofAdd_toAdd]
  refine ⟨(E b).toAdd, ?_⟩
  change (FundamentalGroup.map (circleToOverlap g) 1 (pathClass Circle.expLoop)) ^
    (E b).toAdd = FundamentalGroup.map (circleToOverlap g) 1 b
  rw [← map_zpow, hb]

/-- The attaching class of the actual overlap generator is precisely the full boundary loop. -/
theorem overlapGenerator_boundary (g : ℕ) :
    FundamentalGroup.mapOfEq (boundaryFromOverlap g) (boundaryFromOverlap_base g)
      (overlapGenerator g) = pathClass (boundaryLoop g) := by
  have he : overlapGenerator g =
      FundamentalGroup.mapOfEq (circleToOverlap g) (y := overlapBase g)
        (rfl : circleToOverlap g 1 = overlapBase g) (pathClass Circle.expLoop) := by
    change FundamentalGroup.map (circleToOverlap g) 1 (pathClass Circle.expLoop) =
      FundamentalGroup.mapOfEq (circleToOverlap g)
        (rfl : circleToOverlap g 1 = circleToOverlap g 1) (pathClass Circle.expLoop)
    exact (DFunLike.congr_fun
      (TauCeti.FundamentalGroup.mapOfEq_rfl (x := (1 : Circle)) (circleToOverlap g))
      (pathClass Circle.expLoop)).symm
  have hc := TauCeti.FundamentalGroup.mapOfEq_comp
    (x := (1 : Circle)) (y := overlapBase g) (z := boundaryBase g)
    (boundaryFromOverlap g) (circleToOverlap g)
    (rfl : circleToOverlap g 1 = overlapBase g) (boundaryFromOverlap_base g)
    (pathClass Circle.expLoop)
  have hd := TauCeti.FundamentalGroup.mapOfEq_congr
    (x := (1 : Circle)) (y := boundaryBase g)
    (boundaryFromOverlap_comp_circleToOverlap g)
    (show ((boundaryFromOverlap g).comp (circleToOverlap g)) 1 = boundaryBase g from
      (boundaryFromOverlap_circleToOverlap_apply g 1).trans (boundaryCircle_one g))
    (boundaryCircle_one g) (pathClass Circle.expLoop)
  exact (congrArg
    (FundamentalGroup.mapOfEq (boundaryFromOverlap g) (boundaryFromOverlap_base g)) he).trans
      (hc.trans (hd.trans (boundaryLoop_class g).symm))

end LowDimensionalTopology.Geometry.Surfaces.HandlePunctureBoundary
