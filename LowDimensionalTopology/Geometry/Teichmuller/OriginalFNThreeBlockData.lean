/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalDehnTwistAboutCore
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLength
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The prescribed cuff, transverse and once-twisted geodesics

Actual positive annular embeddings identify the full-period original cuffs.
Each transverse curve is a simple original geodesic in the actual adjacent
pants union. The third block consists of simple original geodesics in the
free classes of the same literal annular full turns. The length map evaluates
these three prescribed blocks in their given order.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface}

/-- The actual period-circle map of the original cuff, expressed on Circle. -/
def originalFNCuffCircle (q : OriginalClosedGeodesic M) : Circle → X :=
  fun s => (q.periodic.lift : AddCircle (1 : ℝ) → X)
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm s)

/-- An actual closed annulus with the specified original full-period cuff
as an identified interior core. -/
structure OriginalFNCuffAnnulus (q : OriginalClosedGeodesic M) where
  map : Circle × unitInterval → X
  closedEmbedding : Topology.IsClosedEmbedding map
  openInterior : IsOpen (map '' {p : Circle × unitInterval |
    0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})
  coreHeight : unitInterval
  coreHeight_mem : 0 < (coreHeight : ℝ) ∧ (coreHeight : ℝ) < 1
  core_eq : ∀ s : Circle, map (s, coreHeight) = originalFNCuffCircle q s

/-- The same literal ambient full turn of the given annulus. -/
def OriginalFNCuffAnnulus.twist {q : OriginalClosedGeodesic M}
    (A : OriginalFNCuffAnnulus q) : X ≃ₜ X :=
  dehnTwistAboutCore (originalFNCuffCircle q) A.map A.closedEmbedding
    A.openInterior A.coreHeight A.coreHeight_mem A.core_eq

/-- The actual annular embedding expressed on the standard complex annulus,
with radial coordinate increasing outward; the radial coordinate is clamped
outside that annulus. -/
def originalFNAnnulusPlane (e : Circle × unitInterval → X) : ℂ → X :=
  fun z => e (Circle.exp (Complex.arg z),
    Set.projIcc (0 : ℝ) 1 zero_le_one (‖z‖ - 1))

/-- Positivity of the same annular embedding in the original complex atlas. -/
def OriginalFNPositiveAnnulus (R : ClosedRiemannSurface X)
    (e : Circle × unitInterval → X) : Prop :=
  ∀ c ∈ R.toRiemannAtlas.charts,
    LiZhongQC.IsSensePreserving (fun z => c (originalFNAnnulusPlane e z))
      ({z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 2} ∩ originalFNAnnulusPlane e ⁻¹' c.source)

variable {g : ℕ} {inc : OriginalFNCuffIncidence g}

/-- The actual prescribed three blocks. The two sides of a cuff may belong
to the same pants. Each twisted curve retains the free class of the same
literal annular full turn of its chosen transverse curve. -/
structure OriginalFNThreeBlockData (D₀ : OriginalFNRealization M inc) where
  annulus : ∀ j, OriginalFNCuffAnnulus (D₀.cuff j)
  annulus_positive : ∀ j, OriginalFNPositiveAnnulus R (annulus j).map
  tau0 : Fin (3 * g - 3) → OriginalClosedGeodesic M
  tau1 : Fin (3 * g - 3) → OriginalClosedGeodesic M
  tau0_simple : ∀ j, Function.Injective ((tau0 j).periodic.lift : AddCircle (1 : ℝ) → X)
  tau1_simple : ∀ j, Function.Injective ((tau1 j).periodic.lift : AddCircle (1 : ℝ) → X)
  tau0_support : ∀ j, Set.range (tau0 j).curve ⊆
    (D₀.component ((inc.copy (j, 0)).1)).val ∪ Set.range (D₀.cuff j).curve ∪
      (D₀.component ((inc.copy (j, 1)).1)).val
  tau0_ne_cuff : ∀ j, Set.range (tau0 j).curve ≠ Set.range (D₀.cuff j).curve
  tau0_meets : ∀ j,
    (Set.range (tau0 j).curve ∩ Set.range (D₀.cuff j).curve).Nonempty
  dehn_class : ∀ j, LiZhongQC.FreelyHomotopic
    ⟨(annulus j).twist (tau0 j).toLoop.1,
      (tau0 j).toLoop.2.map (annulus j).twist.continuous⟩ (tau1 j).toLoop

/-- The given cuffs, transverse curves and their once-twisted representatives,
in precisely that block order. -/
def OriginalFNThreeBlockData.blockGeodesic {D₀ : OriginalFNRealization M inc}
    (T : OriginalFNThreeBlockData D₀) :
    Fin (3 * g - 3) ⊕ (Fin (3 * g - 3) ⊕ Fin (3 * g - 3)) → OriginalClosedGeodesic M
  | .inl j => D₀.cuff j
  | .inr (.inl j) => T.tau0 j
  | .inr (.inr j) => T.tau1 j

/-- The canonical finite reindexing of the three consecutive source blocks. -/
def originalFNThreeBlockIndex (g : ℕ) (hg : 1 < g) :
    Fin (9 * g - 9) ≃ Fin (3 * g - 3) ⊕ (Fin (3 * g - 3) ⊕ Fin (3 * g - 3)) := by
  have hd : 9 * g - 9 = (3 * g - 3) + ((3 * g - 3) + (3 * g - 3)) := by omega
  exact (finCongr hd).trans (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin (3 * g - 3))) finSumFinEquiv.symm))

/-- The actual original positive lengths of the prescribed three blocks,
on the whole original Fricke image. -/
def originalFNThreeBlockLengthMap (R : ClosedRiemannSurface X) (hg : 1 < g)
    (hgenus : R.HasGenus g) {e : X ≃ₜ PolygonQuotient g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc) (T : OriginalFNThreeBlockData D₀) :
    nativeFrickeImage hA → (Fin (9 * g - 9) → Set.Ioi (0 : ℝ)) := by
  let := R.compactSpace
  exact fun t k =>
    let q := T.blockGeodesic (originalFNThreeBlockIndex g hg k)
    ⟨frickeGeodesicLength R hg hgenus hA hAlt q.toLoop t,
      frickeGeodesicLength_pos R hg hgenus hA hAlt q.toLoop
        q.not_isNullHomotopicLoop t⟩

end LowDimensionalTopology.Geometry.Teichmuller
