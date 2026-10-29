/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through its public
free-homotopy predicate; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicPantsDecomposition
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalCuffTwistPhase
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableC1Compatibility
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeDomain
public import LowDimensionalTopology.Unproved.Surfaces.OriginalPantsReflection
public import Mathlib.Analysis.Analytic.Basic

/-!
# The prescribed geometric family of original cuff phases

Each global cuff has two intrinsic boundary copies, which may belong to the
same pants and may have the same global image. Actual shortest seam feet on
the copies are projected onto one oriented original cuff. The phase uses its
full hyperbolic BV arclength. A reference realization records the fixed source
choices; existence of an entire compatible target family, independence of all
choices and its real analyticity are left as one explicit unproved proposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped unitInterval Topology
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

/-- Each global cuff has two labelled incident boundary copies. A prescribed
different intrinsic cuff specifies the seam at each copy. -/
structure OriginalFNCuffIncidence (g : ℕ) where
  copy : (Fin (3 * g - 3) × Fin 2) ≃ (Fin (2 * g - 2) × Fin 3)
  other : (Fin (3 * g - 3) × Fin 2) → Fin 3
  other_ne : ∀ s, other s ≠ (copy s).2

/-- Three intrinsic cuffs and their actual maps to the prescribed global
cuffs. The independent pants is the given component's own Nielsen kernel.
Different intrinsic cuffs may project to the same global cuff. -/
structure OriginalFNIntrinsicPants
    {Y : Type} [TopologicalSpace Y] {S : RiemannSurface Y}
    (N : HyperbolicSurfaceModel S) (C : Set Y)
    (globalCuff : Fin 3 → OriginalClosedGeodesic N) where
  pants : IsHyperbolicPairOfPants N C
  seed : N.discCover ⁻¹' C
  model : HyperbolicSurfaceModel (pantsNielsenExtensionRiemannSurface N C seed)
  cuff : Fin 3 → OriginalClosedGeodesic model
  compact_kernel : IsCompact (closure (pantsNielsenKernel N C seed))
  simple : ∀ i, Function.Injective
    ((cuff i).periodic.lift : AddCircle (1 : ℝ) → PantsNielsenExtension N C seed)
  distinct : Function.Injective (fun i => range (cuff i).curve)
  frontier_census : range (fun i => range (cuff i).curve) =
    {T : Set (PantsNielsenExtension N C seed) | ∃ x ∈ frontier (pantsNielsenKernel N C seed),
      connectedComponentIn (frontier (pantsNielsenKernel N C seed)) x = T}
  projection : C(PantsNielsenExtension N C seed, Y)
  projection_eq : ∀ u : extendedUnitDisc,
    projection (mobiusDomainProjection (pantsNielsenExtensionDomain N C seed) u) =
      N.discCover u
  cuffMap : ∀ i, range (cuff i).curve ≃ₜ range (globalCuff i).curve
  cuffMap_val : ∀ i (x : range (cuff i).curve),
    (cuffMap i x).val = projection x.val

namespace OriginalFNIntrinsicPants

variable {Y : Type} [TopologicalSpace Y] {S : RiemannSurface Y}
variable {N : HyperbolicSurfaceModel S} {C : Set Y}
variable {globalCuff : Fin 3 → OriginalClosedGeodesic N}

/-- The same chosen-lift independent extension used by the intrinsic cuffs. -/
abbrev Extension (P : OriginalFNIntrinsicPants N C globalCuff) : Type :=
  PantsNielsenExtension N C P.seed

/-- Its actual quotient complex atlas. -/
abbrev riemannSurface (P : OriginalFNIntrinsicPants N C globalCuff) :
    RiemannSurface P.Extension :=
  pantsNielsenExtensionRiemannSurface N C P.seed

/-- The actual open kernel identified with the original component. -/
abbrev kernel (P : OriginalFNIntrinsicPants N C globalCuff) : Set P.Extension :=
  pantsNielsenKernel N C P.seed

end OriginalFNIntrinsicPants

/-- One complete finite original realization with prescribed intrinsic cuff
incidences and actual shortest orthogonal seams. Existence is not asserted. -/
structure OriginalFNRealization
    {Y : Type} [TopologicalSpace Y] {S : ClosedRiemannSurface Y}
    (N : HyperbolicSurfaceModel S.toRiemannSurface) {g : ℕ}
    (inc : OriginalFNCuffIncidence g) where
  cuff : Fin (3 * g - 3) → OriginalClosedGeodesic N
  simple : ∀ j, Function.Injective ((cuff j).periodic.lift : AddCircle (1 : ℝ) → Y)
  distinct : Function.Injective (fun j => range (cuff j).curve)
  decomposing : IsGeodesicDecomposingSystem N (range (fun j => range (cuff j).curve))
  component : Fin (2 * g - 2) ≃
    {C : Set Y // C ∈ geodesicComplementComponents (range (fun j => range (cuff j).curve))}
  pants : ∀ a, OriginalFNIntrinsicPants N (component a).val
    (fun i => cuff (inc.copy.symm (a, i)).1)
  seam : ∀ s : Fin (3 * g - 3) × Fin 2,
    HyperbolicSurfaceC1CurvePiece (pants (inc.copy s).1).model
  seam_geodesic : ∀ s, IsOriginalGeodesicArc (pants (inc.copy s).1).model (seam s).curve
  seam_closed : ∀ s, range (seam s).curve ⊆ closure (pants (inc.copy s).1).kernel
  seam_interior : ∀ s, ∀ u ∈ Ioo (0 : I) 1, (seam s).curve u ∈ (pants (inc.copy s).1).kernel
  seam_start : ∀ s, (seam s).curve 0 ∈ range ((pants (inc.copy s).1).cuff (inc.copy s).2).curve
  seam_end : ∀ s, (seam s).curve 1 ∈ range ((pants (inc.copy s).1).cuff (inc.other s)).curve
  seam_start_orthogonal : ∀ s, HasRegularOrthogonalInwardGerms
    (pants (inc.copy s).1).riemannSurface
    (range (seam s).curve ∩ (pants (inc.copy s).1).kernel)
    (range ((pants (inc.copy s).1).cuff (inc.copy s).2).curve) ((seam s).curve 0)
  seam_end_orthogonal : ∀ s, HasRegularOrthogonalInwardGerms
    (pants (inc.copy s).1).riemannSurface
    (range (seam s).curve ∩ (pants (inc.copy s).1).kernel)
    (range ((pants (inc.copy s).1).cuff (inc.other s)).curve) ((seam s).curve 1)
  seam_minimal : ∀ s
    (p : RiemannSurfaceRectifiableCurvePiece (pants (inc.copy s).1).riemannSurface),
    range p.curve ⊆ closure (pants (inc.copy s).1).kernel →
    p.curve 0 ∈ range ((pants (inc.copy s).1).cuff (inc.copy s).2).curve →
    p.curve 1 ∈ range ((pants (inc.copy s).1).cuff (inc.other s)).curve →
    ENNReal.ofReal (seam s).length ≤ (pants (inc.copy s).1).model.rectifiableCurveLength p

namespace OriginalFNRealization

variable {Y : Type} [TopologicalSpace Y] {S : ClosedRiemannSurface Y}
variable {N : HyperbolicSurfaceModel S.toRiemannSurface} {g : ℕ}
variable {inc : OriginalFNCuffIncidence g}

/-- The actual initial seam foot, projected from its own intrinsic cuff copy
onto the prescribed global cuff. The value is literally the projection. -/
def foot (D : OriginalFNRealization N inc) (s : Fin (3 * g - 3) × Fin 2) :
    range (D.cuff s.1).curve := by
  let a := inc.copy s
  let x : range ((D.pants a.1).cuff a.2).curve :=
    ⟨(D.seam s).curve 0, D.seam_start s⟩
  refine ⟨(D.pants a.1).projection ((D.seam s).curve 0), ?_⟩
  have hx := ((D.pants a.1).cuffMap a.2 x).property
  rw [(D.pants a.1).cuffMap_val a.2 x] at hx
  simpa only [a, x, Prod.eta, Equiv.symm_apply_apply] using hx

/-- The prescribed phase from the two actual feet and the SAME original
oriented full-period cuff, using its accepted finite BV prefix lengths. -/
def phase (D : OriginalFNRealization N inc) (j : Fin (3 * g - 3)) : Circle :=
  originalCuffTwistPhase (D.cuff j) (D.simple j) (D.foot (j, 0)) (D.foot (j, 1))

end OriginalFNRealization

/-- A marking-compatible correspondence between reference and target pants
and each of their intrinsic boundary copies. The closed maps are between
independent intrinsic pants, and their projections may identify cuffs. -/
structure OriginalFNMarkedTransport
    {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc) (m : MarkedRiemannSurface.{0, 0} R)
    {N : HyperbolicSurfaceModel m.surface.toRiemannSurface}
    (D : OriginalFNRealization N inc) where
  map : X ≃ₜ m.carrier
  marking_homotopy : ContinuousMap.Homotopic (_root_.toContinuousMap map) m.markingMap
  cuff_orientation : ∀ j, LiZhongQC.FreelyHomotopic
    ⟨m.markingMap (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map m.markingMap.continuous⟩
    (D.cuff j).toLoop
  component_image : ∀ a, map '' (D₀.component a).val = (D.component a).val
  closureMap : ∀ a, ↥(closure (D₀.pants a).kernel) ≃ₜ ↥(closure (D.pants a).kernel)
  closure_projection : ∀ a (x : ↥(closure (D₀.pants a).kernel)),
    (D.pants a).projection (closureMap a x).val = map ((D₀.pants a).projection x.val)
  closure_cuff : ∀ a i,
    (closureMap a) ''
      {x : ↥(closure (D₀.pants a).kernel) | x.val ∈ range ((D₀.pants a).cuff i).curve} =
      {x : ↥(closure (D.pants a).kernel) | x.val ∈ range ((D.pants a).cuff i).curve}

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}

/-- Actual geometry and marked correspondence at every original marked
target. There is no regularity or phase-independence field. -/
def OriginalFNGeometricFamily
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (D₀ : OriginalFNRealization M inc) :=
  ∀ m : MarkedRiemannSurface.{0, 0} R,
    Σ D : OriginalFNRealization (chosenCanonicalModel hA m).model inc,
      OriginalFNMarkedTransport D₀ m D

/-- The literal BV phase on the entire original Fricke image, evaluated on
one actual marked representative of its existing native inverse. -/
def originalFNFamilyPhase
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (A : OriginalFNGeometricFamily hA D₀)
    (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)) : Circle := by
  letI := nativeFrickeTopology hA
  exact (A (Quotient.out ((nativeFrickeHomeomorph hA hAlt).symm t))).1.phase j

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Surfaces.HandlePresentation Geometry.Teichmuller

/-- For the fixed actual reference pants choices there exists an entire
compatible geometric family. Its literal arclength phases are independent
of marked representative and of all admissible original-atlas models,
intrinsic copies, seams and parametrizations. The complex-valued phases are
real analytic on the entire literal original Fricke image. -/
def OriginalFNTwistPhaseAnalytic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 1 < g) (_hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc) : Prop := by
  classical
  exact ∃ A : OriginalFNGeometricFamily hA D₀,
    (∀ m n : MarkedRiemannSurface.{0, 0} R, MarkedRiemannSurface.Equivalent m n →
      ∀ j, (A m).1.phase j = (A n).1.phase j) ∧
    (∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D),
      ∀ j, (A m).1.phase j = D.phase j) ∧
    ∀ j, AnalyticOnNhd ℝ
      (fun x : Fin (6 * g - 6) → ℝ =>
        if hx : x ∈ nativeFrickeImage hA then
          (originalFNFamilyPhase hA hAlt D₀ A ⟨x, hx⟩ j : ℂ) else 0)
      (nativeFrickeImage hA)

end LowDimensionalTopology.Unproved.Teichmuller
