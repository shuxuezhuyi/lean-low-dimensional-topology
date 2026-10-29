module

public import LowDimensionalTopology.Unproved.Teichmuller.CanonicalHarmonicEichlerJets
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Full harmonic first variation of the original transported hyperbolic area density

The density is the actual Jacobian divided by the squared height of the same
canonical symmetric normalized map. Differentiation is real Fréchet
differentiation in the complete complex parameter, retaining both directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ComplexConjugate InnerProductSpace Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces LiZhongQC
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The source's literal density, with both actual spatial Wirtinger slots. -/
def transportedHyperbolicDensity
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (t : ℂ) (z : ℍ) : ℝ :=
  jacobian (canonicalFamily R p q t) z / (canonicalFamily R p q t z).im ^ 2

/-- Both complex parameter directions of every original harmonic deformation have zero first variation. -/
theorem hasFDerivAt_transportedHyperbolicDensity_zero
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{u})
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    HasFDerivAt (fun t : ℂ => transportedHyperbolicDensity R p q t z)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
  obtain ⟨ψ, _, _, _, _, _, _, _, hψ⟩ := hjets X R Γ p hp q
  obtain ⟨hpoint, hdz, hdzbar⟩ := hψ z
  have hzero := canonicalFamily_zero R p q
  have hv : canonicalFamily R p q 0 z = (z : ℂ) := congrFun hzero z
  have hz : dz (canonicalFamily R p q 0) z = 1 := by
    rw [hzero]
    norm_num [dz, fderiv_id]
  have hzb : dzbar (canonicalFamily R p q 0) z = 0 := by
    rw [hzero]
    norm_num [dzbar, fderiv_id]
  have hnum := hdz.norm_sq.sub hdzbar.norm_sq
  have hheight := Complex.imCLM.hasFDerivAt.comp 0 hpoint
  have hden := hheight.pow 2
  have hne : (canonicalFamily R p q 0 z).im ^ 2 ≠ 0 := by
    rw [hv]
    exact pow_ne_zero 2 z.im_pos.ne'
  have hinv := (hasDerivAt_inv hne).hasFDerivAt.comp 0 hden
  have h := hnum.mul hinv
  convert h using 1
  · rfl
  · ext a
    have hc := eichlerJet_im_eq ψ (z : ℂ) a
    simp [hz, hzb, hv, real_inner_eq_re_inner ℂ]
    rw [hc]
    simp only [UpperHalfPlane.im]
    field_simp [z.im_pos.ne']
    ring

/-- The literal complex and conjugate-coordinate derivatives in the full source statement. -/
theorem wirtinger_transportedHyperbolicDensity_zero
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{u})
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    dz (fun t : ℂ => (transportedHyperbolicDensity R p q t z : ℂ)) 0 = 0 ∧
      dzbar (fun t : ℂ => (transportedHyperbolicDensity R p q t z : ℂ)) 0 = 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp 0
    (hasFDerivAt_transportedHyperbolicDensity_zero R p hjets hp q z)
  have hd : fderiv ℝ
      (fun t : ℂ => (transportedHyperbolicDensity R p q t z : ℂ)) 0 = 0 := by
    simpa [Function.comp_def] using h.fderiv
  constructor <;> simp [dz, dzbar, hd]

/-- The same literal source density for the whole finite harmonic coordinate family. -/
def coordinateDensity {n : ℕ}
    (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (t : Fin n → ℂ) (z : ℍ) : ℝ :=
  jacobian (coordinateFamily R p q t) z / (coordinateFamily R p q t z).im ^ 2

/-- Every actual book coordinate and its conjugate have zero first partial derivative. -/
theorem coordinate_wirtinger_density_zero
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{u})
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {n : ℕ} (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (j : Fin n) (z : ℍ) :
    dz (fun a : ℂ => (coordinateDensity R p q (Pi.single j a) z : ℂ)) 0 = 0 ∧
      dzbar (fun a : ℂ => (coordinateDensity R p q (Pi.single j a) z : ℂ)) 0 = 0 := by
  simpa only [coordinateDensity, coordinateFamily_axis, transportedHyperbolicDensity] using
    wirtinger_transportedHyperbolicDensity_zero R p hjets hp (q j) z

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
