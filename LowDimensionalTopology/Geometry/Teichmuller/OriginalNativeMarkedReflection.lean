module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflectionInvolution
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonFamily
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric
public import LowDimensionalTopology.Geometry.Teichmuller.CompactQCMetricTopologyTransport
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCore

/-!
# The same given-J original reflection on the native marked quotient

The existing QC-source equivalences transport the actual marked reflection.
Its normalized-lift square is proved by those exact equivalence definitions.
No separate native reflection, tangent action or geometric symmetry is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J)

/-- The same original marked reflection through the two actual QC-source equivalences. -/
def originalNativeTeichmullerReflection : TeichmullerSpace.{0,0} R → TeichmullerSpace.{0,0} R :=
  letI := R.toRiemannAtlas.toChartedSpace
  let N := (closedSourceEquiv R).trans (TeichmullerSpace.qcEquiv R hg hgenus).symm
  fun q => N (originalTeichmullerReflection R J hJ (N.symm q))

/-- The actual native reflection is involutive on all original marked classes. -/
theorem originalNativeTeichmullerReflection_involutive :
    Function.Involutive (originalNativeTeichmullerReflection R hg hgenus J hJ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let N := (closedSourceEquiv R).trans (TeichmullerSpace.qcEquiv R hg hgenus).symm
  intro q
  change N (originalTeichmullerReflection R J hJ
    (N.symm (N (originalTeichmullerReflection R J hJ (N.symm q))))) = q
  rw [N.symm_apply_apply, originalTeichmullerReflection_involutive, N.apply_symm_apply]

/-- The actual identity-marked native base point is fixed by this same reflection. -/
theorem originalNativeTeichmullerReflection_basePoint :
    originalNativeTeichmullerReflection R hg hgenus J hJ (TeichmullerSpace.basePoint R) =
      TeichmullerSpace.basePoint R := by
  let := R.toRiemannAtlas.toChartedSpace
  let E := closedSourceEquiv R
  let Q := TeichmullerSpace.qcEquiv R hg hgenus
  let N := E.trans Q.symm
  let q₀ := basePoint (Surface.ofRiemannSurface R.toRiemannSurface)
  have hbase : N q₀ = TeichmullerSpace.basePoint R := by
    apply Q.injective
    change Q (Q.symm (E q₀)) = Q (TeichmullerSpace.basePoint R)
    rw [Q.apply_symm_apply]
    rfl
  change N (originalTeichmullerReflection R J hJ (N.symm (TeichmullerSpace.basePoint R))) =
    TeichmullerSpace.basePoint R
  rw [← hbase, N.symm_apply_apply, originalTeichmullerReflection_basePoint]

variable {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth

/-- The actual normalized-lift map intertwines the SAME native and group reflections. -/
theorem originalNativeTeichmullerReflection_gamma_square :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : TopologicalSpace (ClosedSpace R) :=
      distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
    letI := C; letI := mΓ; letI := CG
    let HR := closedGammaHomeomorph R hg hgenus hΓ hp
    ∀ q : TeichmullerSpace.{0,0} R,
      D (originalNativeTeichmullerReflection R hg hgenus J hJ q) =
        HR (originalTeichmullerReflection R J hJ (HR.symm (D q))) := by
  let := R.toRiemannAtlas.toChartedSpace
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let := C; let := mΓ; let := CG
  let E := closedSourceEquiv R
  let Q := TeichmullerSpace.qcEquiv R hg hgenus
  let N := E.trans Q.symm
  let S := sourceGammaEquiv R hg hgenus hP hΓ hfree hp
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  have hsquare (a : ClosedSpace R) : D (N a) = HR a := by
    change S.symm (Q (Q.symm (E a))) = S.symm (E a)
    rw [Q.apply_symm_apply]
  dsimp only
  intro q
  have hpre : HR.symm (D q) = N.symm q := by
    apply HR.injective
    rw [HR.apply_symm_apply, ← hsquare, N.apply_symm_apply]
  change D (N (originalTeichmullerReflection R J hJ (N.symm q))) =
    HR (originalTeichmullerReflection R J hJ (HR.symm (D q)))
  rw [hsquare, hpre]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
