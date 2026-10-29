module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.PoincareDensity
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HemisphereBall
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.PoincareLineElement

/-!
# The Poincaré density in standard real and complex disk coordinates

The standard real linear isometry identifies the two-dimensional ball density
with the complex disk density. It also identifies their actual coordinate
tensors and the tangent norm induced by the ball Riemannian metric. The bundle
choice in the norm statement is local to that statement.

These comparisons are separate from the hemisphere construction, so that its
arbitrary-dimensional interface does not import the disk tensor development.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

section ComplexDiscDensity

open scoped Manifold Bundle

/-- The same real two-ball and complex disc point have identical Poincare
length density under their standard real linear isometry. -/
theorem euclideanBallComplexDiscHomeomorph_density (x : unitBallDomain 2) :
    ballDensity 2 x =
      poincareLengthDensity ((euclideanBallComplexDiscHomeomorph x : 𝔻) : ℂ) := by
  rw [ballDensity_eq_poincareLengthDensity]
  exact poincareLengthDensity_eq_of_norm_eq
    (Complex.orthonormalBasisOneI.repr.symm.norm_map x.val).symm

/-- In the standard real two-dimensional coordinates, the disc tensor is
exactly the ball density's actual Riemannian inner product. -/
theorem euclideanBallComplexDiscHomeomorph_tensor_apply
    (x : unitBallDomain 2)
    (v w : TangentSpace 𝓘(ℝ, Inversive.Euclidean 2) x) :
    discPoincareTensor ((euclideanBallComplexDiscHomeomorph x : 𝔻) : ℂ)
      (Complex.orthonormalBasisOneI.repr.symm
        ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) v))
      (Complex.orthonormalBasisOneI.repr.symm
        ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) w)) =
      (ballDensity 2).riemannianMetric.inner x v w := by
  change poincareLengthDensity ((euclideanBallComplexDiscHomeomorph x : 𝔻) : ℂ) ^ 2 *
      inner ℝ
        (Complex.orthonormalBasisOneI.repr.symm
          ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) v))
        (Complex.orthonormalBasisOneI.repr.symm
          ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) w)) =
    (ballDensity 2 x) ^ 2 *
      inner ℝ ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) v)
        ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) w)
  rw [← euclideanBallComplexDiscHomeomorph_density x,
    Complex.orthonormalBasisOneI.repr.symm.inner_map_map]

/-- The same coordinate identification also preserves the actual norm
induced by the ball Riemannian metric. The bundle choice remains local. -/
theorem euclideanBallComplexDiscHomeomorph_tangent_norm
    (x : unitBallDomain 2) (v : TangentSpace 𝓘(ℝ, Inversive.Euclidean 2) x) :
    letI : Bundle.RiemannianBundle
        (fun y : unitBallDomain 2 => TangentSpace 𝓘(ℝ, Inversive.Euclidean 2) y) :=
      ⟨(ballDensity 2).riemannianMetric.toRiemannianMetric⟩
    ‖v‖ = poincareLengthDensity ((euclideanBallComplexDiscHomeomorph x : 𝔻) : ℂ) *
      ‖Complex.orthonormalBasisOneI.repr.symm
        ((tangentSpaceCastModel 𝓘(ℝ, Inversive.Euclidean 2) x) v)‖ := by
  simpa only [Complex.orthonormalBasisOneI.repr.symm.norm_map,
    ← euclideanBallComplexDiscHomeomorph_density x] using
    Auxiliary.Analysis.Density.tangent_norm (ballDensity 2) x v

end ComplexDiscDensity

end LowDimensionalTopology.Geometry.Hyperbolic
