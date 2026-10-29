module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergmanKernel
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# The Petersson Hilbert norm on every native open fundamental region

The full original-atlas space is retained. Integrability follows from the
global weighted bound and absolute integrability on a genuine fundamental
domain. The region need not be compact or connected. Positive definiteness
uses the nonzero holomorphic lift on the nonempty open region.
The norm is exactly the square root of the full Petersson diagonal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

open Surfaces QuadraticBergman

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include P hF in
/-- Coverage by translates of the closure forces the actual open region to
be nonempty. No connectedness or compactness assumption is added. -/
theorem fundamentalRegion_nonempty : F.Nonempty := by
  let := P.nativeAction
  obtain ⟨g, y, hy, _⟩ := hF.2.2.1 UpperHalfPlane.I
  by_contra hn
  have he : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp only [he, closure_empty, mem_empty_iff_false] at hy

include hp hF in
/-- Absolute integrability of the original lift on the original open region,
with its actual Euclidean area measure. -/
theorem liftQuadratic_integrableOn_fundamental
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    IntegrableOn (liftQuadratic R.toRiemannAtlas p q) F flatArea := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hΓ : LiZhongQC.IsFuchsian Γ := LiZhongQC.utm_x_isFuchsian hp
  have hs := Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF
  have hi := LiZhongQC.h36p_integrableOn_A hs.1 hs.2.1
    (uniformizedQuadratic_integrableAutomorphic R p hΓ hp hs q)
  have hopen := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 (uniformizedQuadratic R p q)).mpr hi
  have he := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp hopen
  simpa only [UpperHalfPlane.coe_injective.preimage_image, Function.comp_def,
    flatArea, liftQuadratic, uniformizedQuadratic, LinearMap.coe_mk, AddHom.coe_mk] using he

include hp hF in
/-- The actual mixed Petersson integrand is integrable on the entire region.
The global weighted bound controls one factor by a constant times the L1 lift. -/
theorem quadratic_integrand_integrableOn_fundamental
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    IntegrableOn (fun z : ℍ => ((z.im ^ 2 : ℝ) : ℂ) *
      liftQuadratic R.toRiemannAtlas p q z *
        conj (liftQuadratic R.toRiemannAtlas p r z)) F flatArea := by
  obtain ⟨M, _, hb⟩ := uniformizedQuadratic_weightedBound R p hp r
  have hq := liftQuadratic_integrableOn_fundamental R P p hp hF q
  have hc : Continuous (fun z : ℍ => ((z.im ^ 2 : ℝ) : ℂ) *
      liftQuadratic R.toRiemannAtlas p q z *
        conj (liftQuadratic R.toRiemannAtlas p r z)) :=
    (((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.pow 2)).mul
      (liftQuadratic_continuous R p hp q)).mul
        (Complex.continuous_conj.comp (liftQuadratic_continuous R p hp r)))
  refine (hq.norm.mul_const M).mono' hc.aestronglyMeasurable ?_
  exact Eventually.of_forall fun z => by
    have hz := hb (z : ℂ) z.im_pos
    change ‖liftQuadratic R.toRiemannAtlas p r z‖ * z.im ^ 2 ≤ M at hz
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg z.im), Complex.norm_conj]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hz (norm_nonneg (liftQuadratic R.toRiemannAtlas p q z))

include hp hF in
/-- In particular the nonnegative square integrand has a finite integral. -/
theorem quadratic_square_integrableOn_fundamental
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    IntegrableOn (fun z : ℍ => z.im ^ 2 *
      ‖liftQuadratic R.toRiemannAtlas p q z‖ ^ 2) F flatArea := by
  have hi := (quadratic_integrand_integrableOn_fundamental R P p hp hF q q).norm
  apply hi.congr
  exact Eventually.of_forall fun z => by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg z.im), Complex.norm_conj]
    ring

include hp hF in
/-- Additivity in the conjugate-linear slot over the full fundamental region. -/
theorem nativeQuadraticPairing_add_right_fundamental
    (q r s : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F q (r + s) =
      nativeQuadraticPairing R.toRiemannAtlas p F q r +
        nativeQuadraticPairing R.toRiemannAtlas p F q s := by
  unfold nativeQuadraticPairing quadraticPairing
  rw [map_add]
  exact weightedPairing_add_right _ _ _ _ _
    (quadratic_integrand_integrableOn_fundamental R P p hp hF q r)
    (quadratic_integrand_integrableOn_fundamental R P p hp hF q s)

include hp hF in
/-- Every nonzero original differential has a strictly positive full
Petersson diagonal. The nonvanishing conclusion is proved holomorphically. -/
theorem nativeQuadraticPairing_self_pos_fundamental
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    0 < (nativeQuadraticPairing R.toRiemannAtlas p F q q).re := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hn : (q : X → ℂ → ℂ) ≠ 0 := fun he => hq (Subtype.ext he)
  have hd := LiZhongQC.utm_liftQD_differentiableOn q.property hp
  have hne := LiZhongQC.utm_liftQD_ne q.property hn hp
  have hFne : (interior F).Nonempty := by
    rw [hF.1.interior_eq]
    exact fundamentalRegion_nonempty P hF
  exact quadraticPairing_self_pos_of_holomorphic hd hne F hFne
    (quadratic_square_integrableOn_fundamental R P p hp hF q)

include hp hF in
/-- The full Petersson diagonal detects zero in the entire original space. -/
theorem nativeQuadraticPairing_self_eq_zero_iff_fundamental
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F q q = 0 ↔ q = 0 := by
  constructor
  · intro he
    by_contra hq
    have hpos := nativeQuadraticPairing_self_pos_fundamental R P p hp hF q hq
    rw [he] at hpos
    exact (lt_irrefl 0) hpos
  · rintro rfl
    simp [nativeQuadraticPairing, quadraticPairing, weightedPairing]

/-- The canonical full fundamental-domain Petersson inner product, with the
slot order adjusted to Mathlib's conjugate-first convention. -/
@[instance_reducible]
def fundamentalQuadraticInnerCore :
    InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) where
  inner q r := nativeQuadraticPairing R.toRiemannAtlas p F r q
  conj_inner_symm q r := nativeQuadraticPairing_conj R.toRiemannAtlas p F q r
  re_inner_nonneg q := quadraticPairing_self_nonneg F (liftQuadratic R.toRiemannAtlas p q)
  add_left q r s := nativeQuadraticPairing_add_right_fundamental R P p hp hF s q r
  smul_left q r a := nativeQuadraticPairing_smul_right R.toRiemannAtlas p F a r q
  definite q h := (nativeQuadraticPairing_self_eq_zero_iff_fundamental R P p hp hF q).1 h

/-- The norm is constructed from the actual full Petersson integral. -/
@[instance_reducible]
def fundamentalQuadraticNormedAddCommGroup :
    NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    fundamentalQuadraticInnerCore R P p hp hF
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The full Petersson inner product with its precise induced norm. -/
@[instance_reducible]
def fundamentalQuadraticInnerProductSpace :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      fundamentalQuadraticNormedAddCommGroup R P p hp hF
    InnerProductSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    fundamentalQuadraticInnerCore R P p hp hF
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    fundamentalQuadraticNormedAddCommGroup R P p hp hF
  exact InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ
      (HolomorphicQuadraticDifferential R.toRiemannAtlas))

/-- Its norm is the literal square root of the actual full-region integral. -/
theorem fundamentalQuadraticNorm_eq_sqrt
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      fundamentalQuadraticNormedAddCommGroup R P p hp hF
    ‖q‖ = Real.sqrt (∫ z in F, z.im ^ 2 *
      ‖liftQuadratic R.toRiemannAtlas p q z‖ ^ 2 ∂flatArea) := by
  change Real.sqrt (nativeQuadraticPairing R.toRiemannAtlas p F q q).re = _
  unfold nativeQuadraticPairing quadraticPairing
  rw [weightedPairing_self, Complex.ofReal_re]

/-- Completeness concerns this precise integral norm on the full native space. -/
theorem fundamentalQuadratic_completeSpace :
    @CompleteSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas)
      (fundamentalQuadraticNormedAddCommGroup R P p hp hF).toMetricSpace.toUniformSpace := by
  let G := fundamentalQuadraticNormedAddCommGroup R P p hp hF
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G
  let : MetricSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G.toMetricSpace
  let : UniformSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toMetricSpace.toUniformSpace
  let : TopologicalSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : IsUniformAddGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toSeminormedAddCommGroup.to_isUniformAddGroup
  let : InnerProductSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    fundamentalQuadraticInnerProductSpace R P p hp hF
  let : FiniteDimensional ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    R.finiteDimensional_holomorphicQuadraticDifferential
  exact FiniteDimensional.complete ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas)

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson
