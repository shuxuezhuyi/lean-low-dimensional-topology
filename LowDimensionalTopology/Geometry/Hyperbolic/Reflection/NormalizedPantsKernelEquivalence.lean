module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NormalizedFirstPeripheralRigidity
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.PantsNielsenExtension
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenOriginalRegion
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts

/-! Conditional rigidity for actual normalized models of the original pants'
OWN Nielsen extensions. Each kernel=own-core hypothesis is a single-pants
geometric assertion; no comparison map or uniqueness is assumed. -/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.DiscreteGroups

/-- Given the concrete single-pants normalization and core identifications,
the SAME intrinsic full peripheral lengths give an analytic homeomorphism of
the actual extensions, their actual kernels, and all three ordered cuff ranges.
For arbitrary ambient pants, X,Y are their OWN exact-stabilizer extensions and
P,U their literal kernels; the existing same-pants kernel homeomorphisms then
transport this conclusion back to the unchanged original pants. -/
theorem normalizedPantsKernel_equivalence_of_original_lengths
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (M : HyperbolicSurfaceModel R) (N : HyperbolicSurfaceModel S)
    (P : Set X) (U : Set Y)
    (hP : IsHyperbolicPairOfPants M P) (hU : IsHyperbolicPairOfPants N U)
    (F₁ : FuchsianDisc M.group) (F₂ : FuchsianDisc N.group)
    (hF₁ : F₁.carrier = extendedUnitDisc) (hF₂ : F₂.carrier = extendedUnitDisc)
    (hNE₁ : IsNonElementary M.group) (hNE₂ : IsNonElementary N.group)
    (hcore₁ : M.homeomorph '' P =
      mobiusDomainProjection (unitDiscMobiusInvariantDomain M.group M.invariant) ''
        (Subtype.val ⁻¹' F₁.nielsenRegion hNE₁))
    (hcore₂ : N.homeomorph '' U =
      mobiusDomainProjection (unitDiscMobiusInvariantDomain N.group N.invariant) ''
        (Subtype.val ⁻¹' F₂.nielsenRegion hNE₂))
    (κ τ : ℝ) (hκ : 1 < κ) (hτ : 1 < τ)
    (D E A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : D.val = !![κ⁻¹, 0; 0, κ]) (hE : E.val = !![τ⁻¹, 0; 0, τ])
    (hAr : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hBr : B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hAa : 1 < A 1 0 + A 1 1) (hBa : 1 < B 1 0 + B 1 1)
    (hAt : 0 < Matrix.trace A.val) (hBt : 0 < Matrix.trace B.val)
    (hAp : Matrix.trace (A * D).val < 0) (hBp : Matrix.trace (B * E).val < 0)
    (hGM : M.group = Subgroup.closure
      {cayleyMobius * realSLMobius D * cayleyMobius⁻¹,
       cayleyMobius * realSLMobius A * cayleyMobius⁻¹})
    (hGN : N.group = Subgroup.closure
      {cayleyMobius * realSLMobius E * cayleyMobius⁻¹,
       cayleyMobius * realSLMobius B * cayleyMobius⁻¹})
    (q : Fin 3 → OriginalClosedGeodesic M) (r : Fin 3 → OriginalClosedGeodesic N)
    (hlen : ∀ i, (q i).length = (r i).length)
    (hAM : ∀ i z, M.halfPlaneCover ((![D, A, (A * D)⁻¹] i) • z) = M.halfPlaneCover z)
    (hBN : ∀ i z, N.halfPlaneCover ((![E, B, (B * E)⁻¹] i) • z) = N.halfPlaneCover z)
    (hAh : ∀ i, 4 < (Matrix.trace (![D, A, (A * D)⁻¹] i).val) ^ 2)
    (hBh : ∀ i, 4 < (Matrix.trace (![E, B, (B * E)⁻¹] i).val) ^ 2)
    (hAc : ∀ i, LiZhongQC.Covers M.halfPlaneCover (![D, A, (A * D)⁻¹] i) (q i).toLoop)
    (hBc : ∀ i, LiZhongQC.Covers N.halfPlaneCover (![E, B, (B * E)⁻¹] i) (r i).toLoop) :
    M.group = N.group ∧ ∃ f : X ≃ₜ Y, RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f ∧
      f '' P = U ∧ (∀ z : ℍ, f (M.halfPlaneCover z) = N.halfPlaneCover z) ∧
      (∀ i, f '' range (q i).curve = range (r i).curve) ∧
      RiemannConformallyEquivalent (pantsOriginalRiemannSurface M P hP)
        (pantsOriginalRiemannSurface N U hU) := by
  obtain ⟨hDE, hAB⟩ := normalizedPeripheralPair_eq_of_original_lengths M N
    κ τ hκ hτ D E A B hD hE hAr hBr hAa hBa hAt hBt hAp hBp
    q r hlen hAM hBN hAh hBh hAc hBc
  subst E
  subst B
  have hG : M.group = N.group := hGM.trans hGN.symm
  refine ⟨hG, ?_⟩
  rcases M with ⟨G, hI, hDisc, hEll, e, he⟩
  rcases N with ⟨G', hI', hDisc', hEll', e', he'⟩
  change G = G' at hG
  subst G'
  rcases F₁ with ⟨C, hC, hiC, hdC⟩
  rcases F₂ with ⟨C', hC', hiC', hdC'⟩
  change C = extendedUnitDisc at hF₁
  change C' = extendedUnitDisc at hF₂
  subst C
  subst C'
  let f : X ≃ₜ Y := e.trans e'.symm
  have hf : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f :=
    (riemannAnalyticMap_homeomorph_symm e' he').comp he
  have hfu : f '' P = U := by
    calc
      f '' P = e'.symm '' (e '' P) :=
        (image_image (e'.symm : _ → Y) (e : X → _) P).symm
      _ = e'.symm '' (e' '' U) :=
        congrArg (fun T => e'.symm '' T) (hcore₁.trans hcore₂.symm)
      _ = U := e'.toEquiv.symm_image_image U
  have hcov (z : ℍ) : f ((⟨G,hI,hDisc,hEll,e,he⟩ : HyperbolicSurfaceModel R).halfPlaneCover z) =
      (⟨G,hI',hDisc',hEll',e',he'⟩ : HyperbolicSurfaceModel S).halfPlaneCover z := by
    change e'.symm (e (e.symm _)) = e'.symm _
    rw [e.apply_symm_apply]
  have hwords (i : Fin 3) : f '' range (q i).curve = range (r i).curve := by
    let W := ![D, A, (A * D)⁻¹] i
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    obtain ⟨Γ, hΓ, hp⟩ :=
      (⟨G,hI,hDisc,hEll,e,he⟩ : HyperbolicSurfaceModel R).exists_halfPlaneCover_uniformization
    obtain ⟨Δ, hΔ, hn⟩ :=
      (⟨G,hI',hDisc',hEll',e',he'⟩ : HyperbolicSurfaceModel S).exists_halfPlaneCover_uniformization
    have ht : 4 < (Matrix.trace W.val) ^ 2 := hAh i
    have hw : realSLMobius W ≠ 1 := by
      intro h
      have htrace := hSL_trace_sq_of_projection_one W h
      linarith
    rw [(q i).trace_eq_axis_image_of_covers hp W ((hΓ W).2 (hAM i)) hw ht (hAc i),
      (r i).trace_eq_axis_image_of_covers hn W ((hΔ W).2 (hBN i)) hw ht (hBc i),
      image_image]
    exact congrArg (fun g : ℍ → Y => g '' (hHyperbolicAxis W hw ht).carrier) (funext hcov)
  let p : P ≃ₜ U := (f.image P).trans (Homeomorph.setCongr hfu)
  have hp : RiemannAnalyticMap
      (pantsOriginalRiemannSurface (⟨G,hI,hDisc,hEll,e,he⟩ : HyperbolicSurfaceModel R) P hP).toRiemannAtlas
      (pantsOriginalRiemannSurface (⟨G,hI',hDisc',hEll',e',he'⟩ : HyperbolicSurfaceModel S) U hU).toRiemannAtlas p := by
    simpa only [pantsOriginalRiemannSurface_toRiemannAtlas] using
      RiemannAnalyticMap.liftLocalHomeomorph Subtype.val Subtype.val
      hP.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      hU.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph f p hf p.continuous (fun _ => rfl)
  exact ⟨f, hf, hfu, hcov, hwords, p, hp, p.bijective⟩

end LowDimensionalTopology.Geometry.Surfaces
