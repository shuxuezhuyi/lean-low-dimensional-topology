/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through its public
anticonformal-involution predicate; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.PantsNielsenExtension
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalGeodesicArcs
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import LowDimensionalTopology.External.LiZhongQC.Ch09.S31_FiniteType
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.UnitInterval

/-!
# An unproved reflection of the original pants in its own extension

The intrinsic cuffs, closed seams and endpoint angles belong to the same
chosen-lift Nielsen extension. Its actual kernel identification couples the
reflection on the original open pants with the reflection on the intrinsic
closed kernel. The ambient closure of the original open subset is not used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Two regular germs enter the given arc and cuff traces with intrinsic
right angle. Their derivatives in an actual chart are explicitly nonzero. -/
def HasRegularOrthogonalInwardGerms
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (A L : Set X) (x : X) : Prop :=
  ∃ (α β : ℝ → X) (g : OpenPartialHomeomorph X ℂ) (v w : ℂ),
    g ∈ R.charts ∧ x ∈ g.source ∧ α 0 = x ∧ β 0 = x ∧
    ContinuousAt α 0 ∧ ContinuousAt β 0 ∧
    HasDerivAt (fun t : ℝ => g (α t)) v 0 ∧
    HasDerivAt (fun t : ℝ => g (β t)) w 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
    riemannIntrinsicCurveAngle R.toRiemannAtlas x α β 0 = Real.pi / 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε, α t ∈ A ∧ β t ∈ L

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

/-- One order-two reflection on the original open pants agrees, through the
actual kernel identification, with one order-two reflection of its intrinsic
closed kernel. Their fixed sets are the same three complete intrinsic
geodesic seams, with regular orthogonal endpoint germs on the actual cuffs.
The intrinsic model, cuffs, reflections and seams are all unproved existence
conclusions of this proposition. -/
def OriginalPantsReflection
    {X : Type} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (P : Set X)
    (hP : IsHyperbolicPairOfPants M P) (z : M.discCover ⁻¹' P) : Prop :=
  let E := PantsNielsenExtension M P z
  let R_E := pantsNielsenExtensionRiemannSurface M P z
  let C := pantsNielsenKernel M P z
  let Φ := pantsNielsenKernelHomeomorph M P z hP
  let : ChartedSpace ℂ ↥P :=
    (pantsOriginalRiemannSurface M P hP).toRiemannAtlas.toChartedSpace
  ∃ (B : HyperbolicSurfaceModel R_E) (J : ↥P ≃ₜ ↥P)
    (Jbar : ↥(closure C) ≃ₜ ↥(closure C))
    (q : Fin 3 → OriginalClosedGeodesic B) (s t : Fin 3 → E)
    (D : ∀ i : Fin 3, Path (s i) (t i)),
    IsCompact (closure C) ∧
    LiZhongQC.IsAnticonformalInvolution J ∧ orderOf J = 2 ∧ orderOf Jbar = 2 ∧
    (∀ i : Fin 3,
      Function.Injective ((q i).periodic.lift : AddCircle (1 : ℝ) → E)) ∧
    Function.Injective (fun i => range (q i).curve) ∧
    range (fun i => range (q i).curve) =
      {T : Set E | ∃ x ∈ frontier C, connectedComponentIn (frontier C) x = T} ∧
    (∀ p : ↥P,
      (Jbar ⟨(Φ p).val, subset_closure (Φ p).property⟩).val = (Φ (J p)).val) ∧
    Pairwise (fun i j : Fin 3 => Disjoint (range (D i)) (range (D j))) ∧
    (∀ i : Fin 3,
      IsOriginalGeodesicArc B (D i) ∧ range (D i) ⊆ closure C ∧
      (∀ u ∈ Ioo (0 : I) 1, D i u ∈ C) ∧
      s i ∈ range (q i).curve ∧ t i ∈ range (q (i + 1)).curve ∧
      HasRegularOrthogonalInwardGerms R_E (range (D i) ∩ C) (range (q i).curve) (s i) ∧
      HasRegularOrthogonalInwardGerms R_E
        (range (D i) ∩ C) (range (q (i + 1)).curve) (t i)) ∧
    ((Subtype.val : ↥(closure C) → E) '' {u | Jbar u = u} =
      ⋃ i : Fin 3, range (D i)) ∧
    (fun p : ↥P => (Φ p).val) '' {p | J p = p} = C ∩ ⋃ i : Fin 3, range (D i)

end LowDimensionalTopology.Unproved.Surfaces
