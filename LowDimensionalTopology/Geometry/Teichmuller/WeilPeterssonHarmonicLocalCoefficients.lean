module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicVariations
public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGermContinuity
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The original WP coefficients in the actual harmonic coordinate family

The chosen harmonic linear family has the exact original Bers coordinates.
Differentiating that proved identity identifies its coefficient directions
with the inverse chart differential. The original tangent-to-harmonic map
and the unchanged integral law then give the transported harmonic formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "L" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "μ" => fun j : I =>
  (NativeHarmonicBeltrami.ofQuadratic (Γ := Γ) R p hp
    (nativeWeilPeterssonHarmonicFrame (Γ := Γ) R hp hg hgenus hΓ j) : B)

/-- The original finite harmonic family as an element of the actual
coefficient ball, on the unchanged small inverse-coordinate neighborhood. -/
def nativeWeilPeterssonHarmonicParameter (t : E)
    (ht : ‖(L).symm t‖ < 1 / 2) : Ball Γ :=
  ahlforsWeillBall (Δ := Γ) ((L).symm t) ht

/-- The actual projection derivative of each original harmonic direction is
the corresponding inverse-coordinate tangent at the same marked point. -/
theorem nativeWeilPeterssonHarmonicCoordinateTangent (t : Fin (3*g-3) → ℂ)
    (ht : ‖(L).symm t‖ < 1 / 2) (j : I) :
    let νt : Ball Γ := by
      exact nativeWeilPeterssonHarmonicParameter
        (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ t ht
    let a : TeichmullerSpace.{0,0} R := by
      exact β νt.val
    letI := C
    let Kt : TangentSpace TI a ≃L[ℂ] E := by
      exact nativeWeilPeterssonCoordinateEquiv
        (Γ := Γ) R hp hg hgenus hΓ hfree hsmooth a
    let Dproj : B →L[ℂ] TangentSpace TI a := by
      exact mfderiv 𝓘(ℂ, B) TI β νt.val
    Dproj (μ j) = Kt.symm (Pi.single j (1 : ℂ)) := by
  let νt : Ball Γ := nativeWeilPeterssonHarmonicParameter
    (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ t ht
  let a : TeichmullerSpace.{0,0} R := β νt.val
  let := C
  let Kt : TangentSpace TI a ≃L[ℂ] E :=
    nativeWeilPeterssonCoordinateEquiv (Γ := Γ) R hp hg hgenus hΓ hfree hsmooth a
  let Dproj : B →L[ℂ] TangentSpace TI a :=
    mfderiv 𝓘(ℂ, B) TI β νt.val
  change Dproj (μ j) = Kt.symm (Pi.single j (1 : ℂ))
  let A : E →L[ℂ] B :=
    (BersWeighted.ahlforsWeill (Γ := Γ)).comp ((L).symm.toContinuousLinearMap)
  let f : B → E := fun κ => BC (β κ)
  have hf : HasFDerivAt f
      ((L).toContinuousLinearMap.comp
        (nonzeroBersDerivative R hp hg hgenus hΓ νt)) (Subtype.val νt) :=
    hasFDerivAt_coefficientProjection_coordinates_nonzero R hg hgenus hΓ hfree hp νt
  have hνt : νt.val = A t := rfl
  have hfAt : HasFDerivAt f
      ((L).toContinuousLinearMap.comp
        (nonzeroBersDerivative R hp hg hgenus hΓ νt)) (A t) := hνt ▸ hf
  have hc : HasFDerivAt (fun s : E => f (A s))
      (((L).toContinuousLinearMap.comp
        (nonzeroBersDerivative R hp hg hgenus hΓ νt)).comp A) t :=
    hfAt.comp t A.hasFDerivAt
  have hopen : IsOpen {s : E | ‖(L).symm s‖ < 1 / 2} :=
    isOpen_lt (L).symm.continuous.norm continuous_const
  have heq : (fun s : E => f (A s)) =ᶠ[𝓝 t] fun s => s := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    change BC (β (BersWeighted.ahlforsWeill ((L).symm s))) = s
    rw [← nativeWeilPeterssonHarmonicFrame_sum R hp hg hgenus hΓ s]
    exact nativeWeilPeterssonHarmonicFrame_coordinates R hp hg hgenus hΓ hfree s hs
  have hD := (hc.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id t)
  have hframe : A (Pi.single j 1) = μ j :=
    (nativeWeilPeterssonHarmonicFrame_section R hp hg hgenus hΓ j).symm
  have haxis : (L) (nonzeroBersDerivative R hp hg hgenus hΓ νt (μ j)) =
      Pi.single j 1 := by
    have h := congrArg (fun T : E →L[ℂ] E => T (Pi.single j 1)) hD
    change (L) (nonzeroBersDerivative R hp hg hgenus hΓ νt (A (Pi.single j 1))) =
      Pi.single j 1 at h
    simpa only [hframe] using h
  have hproj : canonicalBersTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth
      a (Dproj (μ j)) = nonzeroBersDerivative R hp hg hgenus hΓ νt (μ j) :=
    canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero
      R hg hgenus hΓ hfree hp hsmooth νt (μ j)
  apply Kt.injective
  calc
    Kt (Dproj (μ j)) = (L) (nonzeroBersDerivative R hp hg hgenus hΓ νt (μ j)) :=
      congrArg (fun φ : BersWeighted.Automorphic Γ => (L) φ) hproj
    _ = Pi.single j (1 : ℂ) := haxis
    _ = Kt (Kt.symm (Pi.single j (1 : ℂ))) :=
      (Kt.apply_symm_apply (Pi.single j (1 : ℂ))).symm

local notation "N" => nativeWeilPeterssonHarmonicParameter
  (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ
local notation "Y" => deformedNativeSurface (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "pY" => deformedTargetCover (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "hpY" => deformedNativeSurface_uniformization
  (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "core" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv
  (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ hfree

/-- The same native coefficients are the literal transported harmonic
integral, equivalently the original mixed quadratic pairing, on every
genuine fundamental region of the same deformed surface. -/
theorem nativeWeilPeterssonLocalCoefficient_harmonicFamily (t : Fin (3*g-3) → ℂ)
    (ht : ‖(L).symm t‖ < 1 / 2)
    (P : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ (N t ht)).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (j k : I) :
    let νt : Ball Γ := N t ht
    let Ht := NativePetersson.harmonicProjection
      (Y νt) P (pY νt) (hpY νt) F hF
    let Lt := gammaDerivative hΓ νt
    coeff (basePoint R) j k t =
        WeilPetersson.beltramiPairing F (Ht (Lt (μ j))).val (Ht (Lt (μ k))).val ∧
      coeff (basePoint R) j k t =
        NativePetersson.pairing (Y νt) P (pY νt) (hpY νt) F hF (Lt (μ j))
          (NativePetersson.rieszQuadratic (Y νt) P (pY νt) (hpY νt) F hF (Lt (μ k))) := by
  let νt : Ball Γ := N t ht
  let Ht := NativePetersson.harmonicProjection (Y νt) P (pY νt) (hpY νt) F hF
  let Lt := gammaDerivative hΓ νt
  let HB := NativePetersson.Harmonic (Y νt) P (pY νt) (hpY νt) F hF
  let a : TeichmullerSpace.{0,0} R := β νt.val
  let := C
  let Kt : TangentSpace TI a ≃L[ℂ] E := coord a
  let Dproj : B →L[ℂ] TangentSpace TI a := mfderiv 𝓘(ℂ, B) TI β νt.val
  let THt : TangentSpace TI a ≃L[ℂ] HB := TH νt P F hF hsmooth
  have hcoords : BC a = t := by
    change BC (β (BersWeighted.ahlforsWeill ((L).symm t))) = t
    rw [← nativeWeilPeterssonHarmonicFrame_sum R hp hg hgenus hΓ t]
    exact nativeWeilPeterssonHarmonicFrame_coordinates R hp hg hgenus hΓ hfree t ht
  have hpoint : (chart (basePoint R)).symm t = a := by
    calc
      (chart (basePoint R)).symm t = (chart (basePoint R)).symm (BC a) :=
        congrArg (fun s : E => (chart (basePoint R)).symm s) hcoords.symm
      _ = a := (coefficientProjection_eq_chartSymm_at R hg hgenus hΓ hfree hp hsmooth
        (basePoint R) νt.val).symm
  have haxes (i : I) : Dproj (μ i) = Kt.symm (Pi.single i (1 : ℂ)) :=
    nativeWeilPeterssonHarmonicCoordinateTangent R hp hg hgenus hΓ hfree hsmooth t ht i
  have htransport (i : I) :
      ((THt (Dproj (μ i))).val.val : ℍ → ℂ) = ((Ht (Lt (μ i))).val : ℍ → ℂ) :=
    congrArg (fun b : HB => (b.val.val : ℍ → ℂ))
      (nonzeroTangentHarmonicEquiv_derivative R hp hg hgenus hΓ hfree
        νt P F hF hsmooth (μ i))
  have hcoef : coeff (basePoint R) j k t =
      WeilPetersson.beltramiPairing F (Ht (Lt (μ j))).val (Ht (Lt (μ k))).val := by
    calc
      coeff (basePoint R) j k t =
          (core a).inner (Kt.symm (Pi.single k (1 : ℂ)))
            (Kt.symm (Pi.single j (1 : ℂ))) :=
        congrArg (fun q : TeichmullerSpace.{0,0} R => (core q).inner
          ((coord q).symm (Pi.single k (1 : ℂ)))
          ((coord q).symm (Pi.single j (1 : ℂ)))) hpoint
      _ = (core a).inner (Dproj (μ k)) (Dproj (μ j)) :=
        congrArg₂ (fun v w : TangentSpace TI a => (core a).inner w v)
          (haxes j).symm (haxes k).symm
      _ = WeilPetersson.beltramiPairing F
          (THt (Dproj (μ j))).val.val (THt (Dproj (μ k))).val.val :=
        nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth
          νt P F hF (Dproj (μ j)) (Dproj (μ k))
      _ = WeilPetersson.beltramiPairing F (Ht (Lt (μ j))).val (Ht (Lt (μ k))).val :=
        congrArg₂ (WeilPetersson.beltramiPairing F) (htransport j) (htransport k)
  refine ⟨hcoef, hcoef.trans ?_⟩
  exact (NativePetersson.harmonicProjection_hermitian_compatibility
    (Y νt) P (pY νt) (hpY νt) F hF (Lt (μ j)) (Lt (μ k))).2.2.2

/-- An actual basis of the full deformed harmonic space, obtained by mapping
the standard coordinate basis through the same two genuine equivalences. -/
def nativeWeilPeterssonHarmonicTransportedBasis (t : Fin (3*g-3) → ℂ)
    (ht : ‖(L).symm t‖ < 1 / 2)
    (P : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ (N t ht)).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    let νt : Ball Γ := N t ht
    Module.Basis I ℂ (NativePetersson.Harmonic (Y νt) P (pY νt) (hpY νt) F hF) := by
  let νt : Ball Γ := N t ht
  let a : TeichmullerSpace.{0,0} R := β νt.val
  let := C
  let Kt : TangentSpace TI a ≃L[ℂ] E := coord a
  exact ((Pi.basisFun ℂ I).map Kt.symm.toLinearEquiv).map
    (TH νt P F hF hsmooth).toLinearEquiv

/-- Each vector of the actual basis is the original transported harmonic
coefficient, with both independence and spanning supplied by Basis.map. -/
theorem nativeWeilPeterssonHarmonicTransportedBasis_apply (t : Fin (3*g-3) → ℂ)
    (ht : ‖(L).symm t‖ < 1 / 2)
    (P : Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ (N t ht)).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (j : I) :
    let νt : Ball Γ := N t ht
    let Ht := NativePetersson.harmonicProjection
      (Y νt) P (pY νt) (hpY νt) F hF
    let Lt := gammaDerivative hΓ νt
    nativeWeilPeterssonHarmonicTransportedBasis R hp hg hgenus hΓ hfree hsmooth
        t ht P F hF j =
      (⟨Ht (Lt (μ j)), ⟨Lt (μ j), rfl⟩⟩ :
        NativePetersson.Harmonic (Y νt) P (pY νt) (hpY νt) F hF) := by
  let νt : Ball Γ := N t ht
  let Ht := NativePetersson.harmonicProjection (Y νt) P (pY νt) (hpY νt) F hF
  let Lt := gammaDerivative hΓ νt
  let HB := NativePetersson.Harmonic (Y νt) P (pY νt) (hpY νt) F hF
  let a : TeichmullerSpace.{0,0} R := β νt.val
  let := C
  let Kt : TangentSpace TI a ≃L[ℂ] E := coord a
  let Dproj : B →L[ℂ] TangentSpace TI a := mfderiv 𝓘(ℂ, B) TI β νt.val
  let THt : TangentSpace TI a ≃L[ℂ] HB := TH νt P F hF hsmooth
  have haxis : Dproj (μ j) = Kt.symm (Pi.single j (1 : ℂ)) :=
    nativeWeilPeterssonHarmonicCoordinateTangent R hp hg hgenus hΓ hfree hsmooth t ht j
  change THt (Kt.symm ((Pi.basisFun ℂ I) j)) = _
  calc
    THt (Kt.symm ((Pi.basisFun ℂ I) j)) = THt (Kt.symm (Pi.single j (1 : ℂ))) :=
      congrArg (fun v : E => THt (Kt.symm v)) (Pi.basisFun_apply ℂ I j)
    _ = THt (Dproj (μ j)) := congrArg THt haxis.symm
    _ = (⟨Ht (Lt (μ j)), ⟨Lt (μ j), rfl⟩⟩ : HB) :=
      nonzeroTangentHarmonicEquiv_derivative R hp hg hgenus hΓ hfree
        νt P F hF hsmooth (μ j)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
