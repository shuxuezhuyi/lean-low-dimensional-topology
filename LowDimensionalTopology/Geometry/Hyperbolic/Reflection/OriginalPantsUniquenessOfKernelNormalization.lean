module

public import LowDimensionalTopology.Unproved.Surfaces.OwnPantsKernelNormalizationUnoriented
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NormalizedPantsKernelEquivalence

/-! Conditional uniqueness of the original pants from their intrinsic cuff lengths.
Cuff labels are unoriented sets in each OWN exact-stabilizer extension. Their
equal lengths are certified by actual simple FULL periods of the original
extension projection chosen by the single-pants normalization premise. -/

public section
noncomputable section
open Set
open LowDimensionalTopology.Unproved.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Equal ordered intrinsic cuff lengths give a conformal equivalence of the
two unchanged ORIGINAL pants, conditional only on each concrete single-pants
normalization premise. Actual whole-extension boundary correspondence is kept.
No distinctness of ambient-frontier images or comparison map is assumed. -/
theorem originalPants_equivalence_of_intrinsic_cuff_lengths
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (M : HyperbolicSurfaceModel R) (N : HyperbolicSurfaceModel S)
    (P : Set X) (U : Set Y)
    (hP : IsHyperbolicPairOfPants M P) (hU : IsHyperbolicPairOfPants N U)
    (z : M.discCover ⁻¹' P) (w : N.discCover ⁻¹' U)
    (hNormP : OwnPantsKernelNormalizationUnoriented M P hP z)
    (hNormU : OwnPantsKernelNormalizationUnoriented N U hU w)
    (L : Fin 3 → Set (PantsNielsenExtension M P z))
    (K : Fin 3 → Set (PantsNielsenExtension N U w))
    (hLinj : Function.Injective L) (hKinj : Function.Injective K)
    (hLall : range L = {T | ∃ x ∈ frontier (pantsNielsenKernel M P z),
      connectedComponentIn (frontier (pantsNielsenKernel M P z)) x = T})
    (hKall : range K = {T | ∃ x ∈ frontier (pantsNielsenKernel N U w),
      connectedComponentIn (frontier (pantsNielsenKernel N U w)) x = T})
    (hperiods :
      ∃ (b : Fin 3 → OriginalClosedGeodesic (Classical.choose hNormP))
        (c : Fin 3 → OriginalClosedGeodesic (Classical.choose hNormU)),
        (∀ i, Function.Injective ((b i).periodic.lift :
          AddCircle (1 : ℝ) → PantsNielsenExtension M P z) ∧ range (b i).curve = L i) ∧
        (∀ i, Function.Injective ((c i).periodic.lift :
          AddCircle (1 : ℝ) → PantsNielsenExtension N U w) ∧ range (c i).curve = K i) ∧
        ∀ i, (b i).length = (c i).length) :
    RiemannConformallyEquivalent (pantsOriginalRiemannSurface M P hP)
      (pantsOriginalRiemannSurface N U hU) ∧
    ∃ f : PantsNielsenExtension M P z ≃ₜ PantsNielsenExtension N U w,
      RiemannAnalyticMap (pantsNielsenExtensionRiemannSurface M P z).toRiemannAtlas
        (pantsNielsenExtensionRiemannSurface N U w).toRiemannAtlas f ∧
      f '' pantsNielsenKernel M P z = pantsNielsenKernel N U w ∧
      ∀ i, f '' L i = K i := by
  obtain ⟨b, c, hb, hc, hlen⟩ := hperiods
  obtain ⟨_, _, _, hnormalizeP⟩ := Classical.choose_spec hNormP
  obtain ⟨_, _, _, hnormalizeU⟩ := Classical.choose_spec hNormU
  let a : Fin 3 → ENNReal := fun i => (b i).length
  obtain ⟨NP, _, DP, AP, κP, _, FP, hNEP, qP, _, _, hκP, hDP,
      hArP, hAaP, _, _, _, hAtP, hApP, _, _, hGenP, hqP, hKernelP, hFP, hCoreP⟩ :=
    hnormalizeP L a hLinj hLall (fun i => ⟨b i, (hb i).1, (hb i).2, rfl⟩)
  obtain ⟨NU, _, DU, AU, κU, _, FU, hNEU, qU, _, _, hκU, hDU,
      hArU, hAaU, _, _, _, hAtU, hApU, _, _, hGenU, hqU, hKernelU, hFU, hCoreU⟩ :=
    hnormalizeU K a hKinj hKall (fun i => ⟨c i, (hc i).1, (hc i).2, (hlen i).symm⟩)
  have hlengths (i : Fin 3) : (qP i).length = (qU i).length :=
    (hqP i).2.1.trans (hqU i).2.1.symm
  obtain ⟨_, f, hf, hfKernel, _, hfLabels, hKernelEq⟩ :=
    normalizedPantsKernel_equivalence_of_original_lengths NP NU
      (pantsNielsenKernel M P z) (pantsNielsenKernel N U w)
      hKernelP hKernelU FP FU hFP hFU hNEP hNEU hCoreP hCoreU
      κP κU hκP hκU DP DU AP AU hDP hDU hArP hArU hAaP hAaU
      hAtP hAtU hApP hApU hGenP hGenU qP qU hlengths
      (fun i => (hqP i).2.2.2.1) (fun i => (hqU i).2.2.2.1)
      (fun i => (hqP i).2.2.2.2.1) (fun i => (hqU i).2.2.2.2.1)
      (fun i => (hqP i).2.2.2.2.2) (fun i => (hqU i).2.2.2.2.2)
  have hOwnKernel : RiemannConformallyEquivalent
      (pantsNielsenKernelRiemannSurface M P z hP)
      (pantsNielsenKernelRiemannSurface N U w hU) := by
    rw [pantsNielsenKernelRiemannSurface_eq_original M P z hP NP hKernelP,
      pantsNielsenKernelRiemannSurface_eq_original N U w hU NU hKernelU] at hKernelEq
    exact hKernelEq
  have hOriginal := ((pantsNielsenKernel_conformallyEquivalent M P z hP).trans
    hOwnKernel).trans (pantsNielsenKernel_conformallyEquivalent N U w hU).symm
  refine ⟨hOriginal, f, hf, hfKernel, ?_⟩
  intro i
  rw [← (hqP i).1, hfLabels i, (hqU i).1]

end LowDimensionalTopology.Geometry.Surfaces
