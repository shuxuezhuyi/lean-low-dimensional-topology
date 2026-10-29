module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSameJClassSquare
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorFiniteBers
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSameJReferenceLift
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The same given-J reflection in the actual original Bers charts

The marked class square and the two independent finite coordinate choices give
the actual chart expression. The same lifted reference map supplies its
holomorphic factor. Double star makes that expression complex differentiable
on the true chart domain at every original class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami BersWeighted

/-- The SAME given-J reflection is antiholomorphic in every actual original Bers chart. -/
theorem originalTeichmullerReflection_antiholomorphic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : TopologicalSpace (ClosedSpace R) :=
      distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
    letI := gammaQCMetricSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
    letI := gammaBersChartedSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
    let HR := closedGammaHomeomorph R hg hgenus hΓ hp
    let rGamma : TeichGamma Γ → TeichGamma Γ := fun a =>
      HR (originalTeichmullerReflection R J hJ (HR.symm a))
    ∀ a : TeichGamma Γ, DifferentiableOn ℂ
      (fun v : Fin (3 * g - 3) → ℂ => fun j =>
        conj ((chartAt (Fin (3 * g - 3) → ℂ) (rGamma a))
          (rGamma ((chartAt (Fin (3 * g - 3) → ℂ) a).symm v)) j))
      ((chartAt (Fin (3 * g - 3) → ℂ) a).target ∩
        (chartAt (Fin (3 * g - 3) → ℂ) a).symm ⁻¹'
          (rGamma ⁻¹' (chartAt (Fin (3 * g - 3) → ℂ) (rGamma a)).source)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let RStar := originalMirrorNative R.toSourceClosedRS
  let hgenusStar := originalMirrorNative_hasGenus R hgenus
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let := gammaQCMetricSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
  let := gammaQCMetricSpace RStar hg hgenusStar hs.1 hs.2.1 hpSigma
  let := gammaBersChartedSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
  let := gammaBersChartedSpace RStar hg hgenusStar hs.1 hs.2.1 hpSigma
  let : Nonempty (TeichGamma Γ) := ⟨TeichGamma.origin Γ⟩
  let : Nonempty (TeichGamma Γσ) := ⟨TeichGamma.origin Γσ⟩
  let Z := Fin (3 * g - 3) → ℂ
  let G := gammaBersCoordinates R hg hgenus hΓ (s27g_actsFreely hp) hp
  let GStar := gammaBersCoordinates RStar hg hgenusStar hs.1 hs.2.1 hpSigma
  let hG := gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ (s27g_actsFreely hp) hp
  let hGStar := gammaBersCoordinates_isOpenEmbedding RStar hg hgenusStar hs.1 hs.2.1 hpSigma
  let e := hG.toOpenPartialHomeomorph G
  let eStar := hGStar.toOpenPartialHomeomorph GStar
  let U := range G
  let UStar := range GStar
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let r := originalTeichmullerReflection R J hJ
  let rGamma : TeichGamma Γ → TeichGamma Γ := fun a => HR (r (HR.symm a))
  let rho : BeltramiGamma Γ → BeltramiGamma Γσ :=
    fixedBersReflectionGamma σ hs.2.2.1 hs.2.2.2.1
  let C := originalMirrorFiniteBersReflection R hg hgenus hΓ hp
  let heJ := originalMirror_referenceInverse_isQCRS R J hJ
  let RefJ := referenceGammaEquiv RStar R hg hgenusStar hgenus
    J.symm heJ hs.1 hΓ hpSigma hp
  obtain ⟨wJ, hwJ⟩ := originalMirror_referenceLift R hΓ hp J
  change IsLift (fun τ => p (σ τ)) p J.symm wJ at hwJ
  have hRef : ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω RefJ :=
    (referenceGammaEquiv_contMDiff_bothDirections RStar R hg hgenusStar hgenus
      J.symm heJ hs.1 hΓ hpSigma hp wJ hwJ).1
  let F : Z → Z := G ∘ RefJ ∘ eStar.symm
  have hGdiff : ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω G := contMDiff_isOpenEmbedding hG
  have hF : ContMDiffOn 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω F UStar :=
    (hGdiff.comp hRef).comp_contMDiffOn (contMDiffOn_isOpenEmbedding_symm hGStar)
  have hFdiff : DifferentiableOn ℂ F UStar := hF.contDiffOn.differentiableOn (by simp)
  have hUStar : IsOpen UStar := hGStar.isOpenMap.isOpen_range
  have hcoordinateQ (q : ClosedSpace R) :
      G (HR (r q)) = F (C (G (HR q))) := by
    refine Quotient.inductionOn q ?_
    intro m
    let μ : BeltramiGamma Γ := Quotient.out (HR (mk m))
    have hclass : HR (mk m) = Quotient.mk _ μ := (Quotient.out_eq (HR (mk m))).symm
    have hsame := originalTeichmullerReflection_coefficientSquare R hg hgenus hΓ hp J hJ
      μ m hclass
    change HR (r (mk m)) = RefJ (Quotient.mk _ (rho μ)) at hsame
    have hfinite := originalMirrorFiniteBersReflection_coefficientSquare R hg hgenus hΓ hp μ
    change GStar (Quotient.mk _ (rho μ)) = C (G (Quotient.mk _ μ)) at hfinite
    erw [hsame, hclass, ← hfinite]
    change G (RefJ (Quotient.mk _ (rho μ))) =
      G (RefJ (eStar.symm (GStar (Quotient.mk _ (rho μ)))))
    erw [hGStar.toOpenPartialHomeomorph_left_inv]
  have hcoordinate (a : TeichGamma Γ) : G (rGamma a) = F (C (G a)) := by
    simpa only [HR.apply_symm_apply] using hcoordinateQ (HR.symm a)
  have himage (a : TeichGamma Γ) : C (G a) ∈ UStar := by
    let μ : BeltramiGamma Γ := Quotient.out a
    have hfinite := originalMirrorFiniteBersReflection_coefficientSquare R hg hgenus hΓ hp μ
    change GStar (Quotient.mk _ (rho μ)) = C (G (Quotient.mk _ μ)) at hfinite
    refine ⟨Quotient.mk _ (rho μ), ?_⟩
    exact hfinite.trans (congrArg (fun b => C (G b)) (Quotient.out_eq a))
  let c : Z ≃L⋆[ℂ] Z := starL ℂ
  let D : Z ≃L[ℂ] Z := C.trans c
  have hanti : DifferentiableOn ℂ (fun v : Z => star (F (C v))) U := by
    intro v hv
    obtain ⟨a, ha⟩ := hv
    have hmem : C v ∈ UStar := by rw [← ha]; exact himage a
    have hFd : DifferentiableAt ℂ F (C v) := hFdiff.differentiableAt (hUStar.mem_nhds hmem)
    have hdouble : DifferentiableAt ℂ (star ∘ F ∘ star) (D v) := by
      change DifferentiableAt ℂ (star ∘ F ∘ star) (star (C v))
      exact hFd.star_star
    have hcomp := hdouble.comp v D.toContinuousLinearMap.differentiableAt
    change DifferentiableAt ℂ (fun x : Z => star (F (star (star (C x))))) v at hcomp
    simpa only [star_star] using hcomp.differentiableWithinAt
  have hglobal : DifferentiableOn ℂ (fun v : Z => star (G (rGamma (e.symm v)))) U := by
    apply hanti.congr
    rintro v ⟨a, rfl⟩
    rw [hG.toOpenPartialHomeomorph_left_inv]
    exact congrArg star (hcoordinate a)
  dsimp only
  intro a
  change DifferentiableOn ℂ (fun v : Z => star (G (rGamma (e.symm v))))
    (e.target ∩ e.symm ⁻¹' (rGamma ⁻¹' e.source))
  apply hglobal.mono
  intro v hv
  simpa only [e, U, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hv.1

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
