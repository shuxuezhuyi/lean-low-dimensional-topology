/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNThreeBlockData
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNTwistCurve
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeMarkedLengthSpectrumContinuity
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTransverseTwistLengthConvexity
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTransverseLengthBridges
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.StrictConvexShiftedPair
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Order.Compact

/-!
# The prescribed three-block proper embedding

The same original Fenchel--Nielsen homeomorphism and the three explicit
geometric statements give a proper embedding by the actual prescribed cuff,
transverse and once-annular-twisted lengths. The compact-parameter bound is
proved here from positivity, convexity, proper fibers and joint continuity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

/-- The elementary finite-cover step used below for the actual transverse
lengths. Endpoint barriers at zero and at two fixed parameters control all
nearby convex fibers, and compactness leaves finitely many barriers. -/
private theorem compact_transverse_sublevel_bound
    {A : Type*} [TopologicalSpace A] (f : A → ℝ → ℝ)
    (hc : Continuous (fun p : A × ℝ => f p.1 p.2))
    (hpos : ∀ a s, 0 < f a s)
    (hconvex : ∀ a, ConvexOn ℝ Set.univ (f a))
    (hproper : ∀ a, IsProperMap (f a))
    {K : Set A} (hK : IsCompact K) (B : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ a ∈ K, ∀ s, f a s ≤ B → |s| ≤ r := by
  classical
  have hfixed (s : ℝ) : Continuous (fun a => f a s) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hlocal (a : A) : ∃ r : ℝ, 0 < r ∧ ∃ V : Set A,
      IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V, ∀ s, f b s ≤ B → |s| ≤ r := by
    let C := max B (f a 0) + 1
    have hC₁ : B < C := by dsimp [C]; linarith [le_max_left B (f a 0)]
    have hC₂ : f a 0 < C := by dsimp [C]; linarith [le_max_right B (f a 0)]
    obtain ⟨c, hc⟩ :=
      ((hproper a).isCompact_preimage (isCompact_Icc : IsCompact (Set.Icc 0 C))).bddAbove_image
        continuous_abs.continuousOn
    let r := max c 0 + 1
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right c 0]
    have hcr : c < r := by dsimp [r]; linarith [le_max_left c 0]
    have hbarrier (s : ℝ) (hs : |s| = r) : C < f a s := by
      by_contra h
      have hm : s ∈ (f a) ⁻¹' Set.Icc 0 C := ⟨(hpos a s).le, le_of_not_gt h⟩
      have hb := hc (Set.mem_image_of_mem abs hm)
      rw [hs] at hb
      linarith
    have hp : C < f a r := hbarrier r (abs_of_pos hr)
    have hn : C < f a (-r) := hbarrier (-r) (by rw [abs_neg, abs_of_pos hr])
    let V : Set A := {b | B < f b r ∧ f b 0 < f b r ∧
      B < f b (-r) ∧ f b 0 < f b (-r)}
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const (hfixed r)).inter
        ((isOpen_lt (hfixed 0) (hfixed r)).inter
          ((isOpen_lt continuous_const (hfixed (-r))).inter
            (isOpen_lt (hfixed 0) (hfixed (-r)))))
    refine ⟨r, hr, V, hVo, ⟨hC₁.trans hp, hC₂.trans hp, hC₁.trans hn, hC₂.trans hn⟩, ?_⟩
    intro b hb s hs
    apply abs_le.mpr
    constructor
    · by_contra h
      have hsr : s < -r := lt_of_not_ge h
      have hmono := (hconvex b).strictAntiOn (Set.mem_univ (0 : ℝ))
        (neg_lt_zero.mpr hr) hb.2.2.2
      have hlt : f b (-r) < f b s :=
        hmono ⟨Set.mem_univ s, hsr.le⟩ ⟨Set.mem_univ (-r), le_rfl⟩ hsr
      linarith [hb.2.2.1]
    · by_contra h
      have hsr : r < s := lt_of_not_ge h
      have hmono := (hconvex b).strictMonoOn (Set.mem_univ (0 : ℝ)) hr hb.2.1
      have hlt : f b r < f b s :=
        hmono ⟨Set.mem_univ r, le_rfl⟩ ⟨Set.mem_univ s, hsr.le⟩ hsr
      linarith [hb.1]
  choose r hr V hVo hmem hbound using hlocal
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hVo (by
    intro a _ha
    exact Set.mem_iUnion.mpr ⟨a, hmem a⟩)
  refine ⟨∑ a ∈ I, r a, Finset.sum_nonneg (fun a _ha => (hr a).le), ?_⟩
  intro a ha s hs
  obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.mp (hI ha)
  exact (hbound b a hab s hs).trans
    (Finset.single_le_sum (fun c _hc => (hr c).le) hb)

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc) (T : OriginalFNThreeBlockData D₀)

/-- The actual prescribed three blocks give a proper embedding of the whole
original Fricke image, conditional only on the explicit original geometric
premises. The homeomorphism and the compact-parameter bound are derived. -/
theorem originalFNThreeBlockLengthMap_properEmbedding
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (hConvex : Unproved.Teichmuller.OriginalFNTransverseTwistLengthConvexity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hLocal : Unproved.Teichmuller.OriginalFNTransverseOtherTwistsInvariant
      R hg hgenus hA hAlt D₀ T φ Θ)
    (hShift : Unproved.Teichmuller.OriginalFNSignedDehnLengthShift
      R hg hgenus hA hAlt D₀ T φ Θ) :
    Topology.IsEmbedding (originalFNThreeBlockLengthMap R hg hgenus hA hAlt D₀ T) ∧
      IsProperMap (originalFNThreeBlockLengthMap R hg hgenus hA hAlt D₀ T) := by
  classical
  let := R.compactSpace
  let := nativeFrickeTopology hA
  let : LocallyCompactSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let H := (originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize).homeomorph F
  let E := nativeFrickeHomeomorph hA hAlt
  let L (q : OriginalClosedGeodesic M) :=
    frickeGeodesicLength R hg hgenus hA hAlt q.toLoop
  let J := originalFNThreeBlockIndex g hg
  let G := originalFNThreeBlockLengthMap R hg hgenus hA hAlt D₀ T
  have hLc (q : OriginalClosedGeodesic M) : Continuous (L q) :=
    frickeGeodesicLength_continuous R hg hgenus hA hAlt q.toLoop q.not_isNullHomotopicLoop
  have hLpos (q : OriginalClosedGeodesic M) (t : nativeFrickeImage hA) : 0 < L q t :=
    frickeGeodesicLength_pos R hg hgenus hA hAlt q.toLoop q.not_isNullHomotopicLoop t
  have hG (t : nativeFrickeImage hA)
      (i : Fin (3 * g - 3) ⊕ (Fin (3 * g - 3) ⊕ Fin (3 * g - 3))) :
      (G t (J.symm i) : ℝ) = L (T.blockGeodesic i) t := by
    change L (T.blockGeodesic (J (J.symm i))) t = _
    rw [J.apply_symm_apply]
  have hGcuff (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)) :
      G t (J.symm (.inl j)) = (H t).1 j := by
    apply Subtype.ext
    exact hG t (.inl j)
  have hGc : Continuous G := by
    apply continuous_pi
    intro k
    apply continuous_induced_rng.mpr
    change Continuous (L (T.blockGeodesic (J k)))
    exact hLc _
  let f (j : Fin (3 * g - 3)) (a : Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) (s : ℝ) :=
    L (T.tau0 j) (H.symm (a, Function.update (0 : Fin (3 * g - 3) → ℝ) j s))
  have hfc (j : Fin (3 * g - 3)) :
      Continuous (fun p : (Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) × ℝ => f j p.1 p.2) :=
    (hLc _).comp (H.symm.continuous.comp
      (continuous_fst.prodMk (continuous_const.update j continuous_snd)))
  have hfp (j : Fin (3 * g - 3)) (a : Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) :
      StrictConvexOn ℝ Set.univ (f j a) ∧ IsProperMap (f j a) := by
    obtain ⟨γ, hγ⟩ := exists_originalFNTwistCurve R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize a 0 j
    let t₀ := H.symm (a, (0 : Fin (3 * g - 3) → ℝ))
    have ht₀ : F t₀ = (a, (0 : Fin (3 * g - 3) → ℝ)) := H.apply_symm_apply _
    have hbased (s : ℝ) : F (E (γ s)) =
        ((F t₀).1, Function.update (F t₀).2 j ((F t₀).2 j + s)) := by
      rw [ht₀]
      simpa only [Pi.zero_apply, zero_add] using hγ s
    have hpath (s : ℝ) : E (γ s) =
        H.symm (a, Function.update (0 : Fin (3 * g - 3) → ℝ) j s) := by
      apply H.injective
      exact (hγ s).trans (H.apply_symm_apply _).symm
    have hgeom := hConvex hU hφ hΘ hRigid hRealize t₀ j (T.tau0 j)
      (T.tau0_simple j) (T.tau0_support j) (T.tau0_ne_cuff j) (T.tau0_meets j) γ hbased
    have hfeq : (fun s => L (T.tau0 j) (E (γ s))) = f j a := by
      funext s
      exact congrArg (L (T.tau0 j)) (hpath s)
    have hstrict := hgeom.1
    have hproper := hgeom.2.1
    change StrictConvexOn ℝ Set.univ (fun s => L (T.tau0 j) (E (γ s))) at hstrict
    change IsProperMap (fun s => L (T.tau0 j) (E (γ s))) at hproper
    rw [hfeq] at hstrict hproper
    exact ⟨hstrict, hproper⟩
  have hL₀ (j : Fin (3 * g - 3)) (t : nativeFrickeImage hA) :
      L (T.tau0 j) t = f j (H t).1 ((H t).2 j) := by
    apply hLocal hU hφ hΘ hRigid hRealize j t
      (H.symm ((H t).1, Function.update (0 : Fin (3 * g - 3) → ℝ) j ((H t).2 j)))
    · change (H t).1 = (H (H.symm _)).1
      simp only [H.apply_symm_apply]
    · change (H t).2 j = (H (H.symm _)).2 j
      simp only [H.apply_symm_apply, Function.update_self]
  obtain ⟨ε, hε, hshift⟩ := hShift hU hφ hΘ hRigid hRealize
  have hL₁ (j : Fin (3 * g - 3)) (t : nativeFrickeImage hA) :
      L (T.tau1 j) t = f j (H t).1 ((H t).2 j + ε j * (2 * Real.pi)) := by
    obtain ⟨γ, hγ⟩ := exists_originalFNTwistCurve R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize (H t).1 (H t).2 j
    let β : C(ℝ, TeichmullerSpace.{0, 0} R) :=
      ⟨fun s => γ ((H t).2 j + s),
        γ.continuous.comp (continuous_const.add continuous_id)⟩
    have hbased (s : ℝ) : F (E (β s)) =
        ((F t).1, Function.update (F t).2 j ((F t).2 j + s)) := hγ _
    have hzero : E (β 0) = t := by
      apply H.injective
      change F (E (β 0)) = F t
      simpa only [add_zero, Function.update_eq_self, Prod.eta] using hbased 0
    have hs := hshift t j β hbased 0
    change L (T.tau1 j) (E (β 0)) =
      L (T.tau0 j) (E (β (0 + ε j * (2 * Real.pi)))) at hs
    rw [hzero, zero_add] at hs
    calc
      L (T.tau1 j) t = L (T.tau0 j) (E (β (ε j * (2 * Real.pi)))) := hs
      _ = f j (H (E (β (ε j * (2 * Real.pi))))).1
          ((H (E (β (ε j * (2 * Real.pi))))).2 j) := hL₀ j _
      _ = f j (H t).1 ((H t).2 j + ε j * (2 * Real.pi)) := by
        change f j (F (E (β (ε j * (2 * Real.pi))))).1
          ((F (E (β (ε j * (2 * Real.pi))))).2 j) = _
        rw [hbased]
        simp only [Function.update_self]
        rfl
  have hGi : Function.Injective G := by
    intro t u htu
    have hlengths : (H t).1 = (H u).1 := by
      funext j
      exact (hGcuff t j).symm.trans ((congrFun htu _).trans (hGcuff u j))
    have hblocks (i : Fin (3 * g - 3) ⊕ (Fin (3 * g - 3) ⊕ Fin (3 * g - 3))) :
        L (T.blockGeodesic i) t = L (T.blockGeodesic i) u :=
      (hG t i).symm.trans ((congrArg Subtype.val (congrFun htu _)).trans (hG u i))
    have hangles : (H t).2 = (H u).2 := by
      funext j
      have h₀ : f j (H t).1 ((H t).2 j) = f j (H u).1 ((H u).2 j) :=
        (hL₀ j t).symm.trans ((hblocks (.inr (.inl j))).trans (hL₀ j u))
      have h₁ : f j (H t).1 ((H t).2 j + ε j * (2 * Real.pi)) =
          f j (H u).1 ((H u).2 j + ε j * (2 * Real.pi)) :=
        (hL₁ j t).symm.trans ((hblocks (.inr (.inr j))).trans (hL₁ j u))
      rw [← hlengths] at h₀ h₁
      have hεne : ε j ≠ 0 := by rcases hε j with h | h <;> rw [h] <;> norm_num
      have hstep : ε j * (2 * Real.pi) ≠ 0 :=
        mul_ne_zero hεne (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact Auxiliary.Analysis.strictConvexOn_shifted_pair_injective
        (f j (H t).1) (hfp j (H t).1).1 (ε j * (2 * Real.pi)) hstep
          (Prod.ext h₀ h₁)
    exact H.injective (Prod.ext hlengths hangles)
  have hGp : IsProperMap G := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hGc, ?_⟩
    intro S hS
    let cuffProjection : (Fin (9 * g - 9) → Set.Ioi (0 : ℝ)) →
        (Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) := fun v j => v (J.symm (.inl j))
    have hproj : Continuous cuffProjection := continuous_pi fun j => continuous_apply _
    let K := cuffProjection '' S
    have hK : IsCompact K := hS.image hproj
    have hupper (j : Fin (3 * g - 3)) : ∃ B : ℝ,
        ∀ v ∈ S, (v (J.symm (.inr (.inl j))) : ℝ) ≤ B := by
      obtain ⟨B, hB⟩ := hS.bddAbove_image
        (continuous_subtype_val.comp (continuous_apply (J.symm (.inr (.inl j))))).continuousOn
      exact ⟨B, fun v hv => hB (Set.mem_image_of_mem _ hv)⟩
    choose B hB using hupper
    have hbound (j : Fin (3 * g - 3)) : ∃ r : ℝ, 0 ≤ r ∧
        ∀ a ∈ K, ∀ s, f j a s ≤ B j → |s| ≤ r :=
      compact_transverse_sublevel_bound (f j) (hfc j)
        (fun a s => hLpos (T.tau0 j) _) (fun a => (hfp j a).1.convexOn)
        (fun a => (hfp j a).2) hK (B j)
    choose r hr hbound using hbound
    let box : Set (Fin (3 * g - 3) → ℝ) := {b | ∀ j, b j ∈ Set.Icc (-r j) (r j)}
    have hbox : IsCompact box := isCompact_pi_infinite fun _ => isCompact_Icc
    have hsubset : G ⁻¹' S ⊆ H.symm '' (K ×ˢ box) := by
      intro t ht
      have hfirst : (H t).1 ∈ K := by
        refine ⟨G t, ht, ?_⟩
        funext j
        exact hGcuff t j
      refine ⟨H t, ⟨hfirst, ?_⟩, H.symm_apply_apply t⟩
      intro j
      have htau : L (T.tau0 j) t ≤ B j := by
        have hb := hB j (G t) ht
        rw [hG t (.inr (.inl j))] at hb
        exact hb
      apply abs_le.mp
      exact hbound j (H t).1 hfirst ((H t).2 j) ((hL₀ j t) ▸ htau)
    exact ((hK.prod hbox).image H.symm.continuous).of_isClosed_subset
      (hS.isClosed.preimage hGc) hsubset
  exact ⟨(Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hGc hGi hGp.isClosedMap).isEmbedding, hGp⟩

end LowDimensionalTopology.Geometry.Teichmuller
