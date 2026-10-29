module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Natural coordinates of a quadratic differential

The ordinary analytic normalizer belongs to the original surface and differential.
At a regular point it is the flat coordinate. At a positive-order zero the
coordinate retains its logarithmic angle, with a separate exponential projection
to the flat plane. The ordinary normalizer is not the ramified flat primitive.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- An ordinary analytic normalizer and a disk in its target, for the given
quadratic differential at the given original point. -/
structure QuadraticNaturalCoordinateData
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p : X) where
  order : ℕ
  ordinaryChart : OpenPartialHomeomorph ℂ ℂ
  normal :
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.s26d_a_Data (q : X → ℂ → ℂ) p order
      (ordinaryChart : ℂ → ℂ) ordinaryChart
  radius : ℝ
  radius_pos : 0 < radius
  disk_target : Metric.ball (0 : ℂ) radius ⊆ ordinaryChart.target

/-- The existing analytic normal-form theorem supplies the data for every
nonzero original differential and every original point. -/
def chooseQuadraticNaturalCoordinateData
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) (p : X) :
    QuadraticNaturalCoordinateData R q p :=
  Classical.choice <| by
    let := R.toRiemannAtlas.toChartedSpace
    let := R.t2Space
    let := R.connectedSpace
    have hraw : (q : X → ℂ → ℂ) ≠ 0 := by
      intro h
      apply hq
      exact Subtype.ext h
    obtain ⟨m, η, Z, hD⟩ := LiZhongQC.s26d_a_data_exists q.property hraw p
    have hZ0 : Z (chartAt ℂ p p) = 0 :=
      (congrFun hD.coe (chartAt ℂ p p)).trans hD.natural.2.1
    have h0 : (0 : ℂ) ∈ Z.target := by
      simpa only [hZ0] using Z.map_source hD.center
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Z.open_target.mem_nhds h0)
    refine ⟨⟨m, Z, ?_, r, hr, hball⟩⟩
    simpa only [hD.coe] using hD

/-- Exponential with the slit corresponding to angles strictly between zero
and a full turn, built from the ordinary principal logarithm chart. -/
def quadraticSlitExponential : OpenPartialHomeomorph ℂ ℂ :=
  (((Homeomorph.addLeft (-((Real.pi : ℂ) * Complex.I))).toOpenPartialHomeomorph).trans
    Complex.expOpenPartialHomeomorph).transHomeomorph
      (Homeomorph.mulLeft₀ (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero))

namespace QuadraticNaturalCoordinateData

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}
    (D : QuadraticNaturalCoordinateData R q p)

/-- The positive exponent of the flat development in the normalizer coordinate. -/
def exponent : ℝ := ((D.order + 2 : ℕ) : ℝ) / 2

/-- The original-surface ordinary coordinate, restricted to the chosen disk. -/
def ordinaryNeighborhood : OpenPartialHomeomorph X ℂ :=
  letI := R.toRiemannAtlas.toChartedSpace
  let A := (chartAt ℂ p).trans D.ordinaryChart
  (A.symm.restr (Metric.ball (0 : ℂ) D.radius)).symm

/-- The punctured source sector with its angle retained in the logarithm plane. -/
def sourceLogStrip : Set ℂ :=
  {u | u.re < Real.log D.radius ∧ 0 < u.im ∧ u.im < 2 * Real.pi}

/-- The unwrapped flat target sector, before exponential projection. -/
def spreadTarget : Set ℂ :=
  {v | v.re < D.exponent * Real.log D.radius ∧
    0 < v.im ∧ v.im < ((D.order + 2 : ℕ) : ℝ) * Real.pi}

/-- The logarithmic source parametrizes points of the same original surface. -/
def sourceLogProjection (u : D.sourceLogStrip) : X :=
  letI := R.toRiemannAtlas.toChartedSpace
  (chartAt ℂ p).symm (D.ordinaryChart.symm (Complex.exp (u : ℂ)))

/-- The ordinary coordinate is used at a regular centre. At a zero, the angle
is retained by passing through the slit logarithm and multiplying by the exponent. -/
def retainedCoordinate : OpenPartialHomeomorph X ℂ :=
  if D.order = 0 then D.ordinaryNeighborhood
  else
    (D.ordinaryNeighborhood.trans quadraticSlitExponential.symm).transHomeomorph
      (Homeomorph.mulLeft₀ (((D.order + 2 : ℕ) : ℂ) / 2)
        (div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (D.order + 1))) two_ne_zero))

/-- The target is already the flat plane at a regular point; at a zero its
retained logarithmic angle is projected by the exponential. -/
def targetProjection : ℂ → ℂ :=
  if D.order = 0 then id else Complex.exp

/-- The flat-plane value on the source of the retained coordinate. -/
def projectedCoordinate (x : X) : ℂ :=
  D.targetProjection (D.retainedCoordinate x)

end QuadraticNaturalCoordinateData
end LowDimensionalTopology.Geometry.Teichmuller
