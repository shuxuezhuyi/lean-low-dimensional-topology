module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceLiftNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationPointNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTranslatedBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalImage
public import LowDimensionalTopology.Geometry.Teichmuller.PeterssonIntegralNaturality

/-!
# Recentring the actual normalized Bers translation

The same normalized compositions give an exact coefficient cocycle and
identify the actual twice-deformed projective group. No WP derivative,
harmonic naturality, closedness or Kähler conclusion is assumed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
open GammaMeasurableBeltrami

private theorem source_recentring_inverse (ν μ : LiZhongQC.BeltramiH) (z : ℂ) :
    Function.invFunOn (LiZhongQC.fMuSym (LiZhongQC.b33_t_tb ν μ).val) univ z =
      LiZhongQC.fMuSym ν.val
        (Function.invFunOn (LiZhongQC.fMuSym μ.val) univ z) := by
  obtain ⟨_, _, hν, _, _⟩ := LiZhongQC.b33_t_fs_inv_spec ν
  obtain ⟨_, _, _, hμ, _⟩ := LiZhongQC.b33_t_fs_inv_spec μ
  obtain ⟨_, _, hκ, _, _⟩ := LiZhongQC.b33_t_fs_inv_spec (LiZhongQC.b33_t_tb ν μ)
  have h : LiZhongQC.fMuSym (LiZhongQC.b33_t_tb ν μ).val
      (LiZhongQC.fMuSym ν.val
        (Function.invFunOn (LiZhongQC.fMuSym μ.val) univ z)) = z := by
    rw [LiZhongQC.b33_t_tb, LiZhongQC.b33_t_tb_fMuSym]
    simp only [Function.comp_apply, hν, hμ]
  have hi := congrArg
    (Function.invFunOn (LiZhongQC.fMuSym (LiZhongQC.b33_t_tb ν μ).val) univ) h
  rw [hκ] at hi
  exact hi.symm

/-- Two actual normalized coefficient translations cancel their common middle map. -/
theorem sourceTranslatedBeltrami_recentring
    (ν μ lam : LiZhongQC.BeltramiH) :
    LiZhongQC.translatedBeltrami (LiZhongQC.b33_t_tb ν μ).val
        (LiZhongQC.b33_t_tb ν lam).val =
      LiZhongQC.translatedBeltrami μ.val lam.val := by
  obtain ⟨_, _, hν, _, _⟩ := LiZhongQC.b33_t_fs_inv_spec ν
  have hcomp :
      LiZhongQC.fMuSym (LiZhongQC.b33_t_tb ν lam).val ∘
          Function.invFunOn (LiZhongQC.fMuSym (LiZhongQC.b33_t_tb ν μ).val) univ =
        LiZhongQC.fMuSym lam.val ∘ Function.invFunOn (LiZhongQC.fMuSym μ.val) univ := by
    funext z
    simp only [Function.comp_apply, source_recentring_inverse]
    rw [LiZhongQC.b33_t_tb, LiZhongQC.b33_t_tb_fMuSym]
    simp only [Function.comp_apply, hν]
  unfold LiZhongQC.translatedBeltrami
  rw [hcomp]

/-- The source Bers maps satisfy the exact cocycle on every genuine source point. -/
theorem sourceBersTranslation_recentring
    (ν μ lam : LiZhongQC.BeltramiH) :
    LiZhongQC.b33_t_chi (LiZhongQC.b33_t_tb ν μ)
        (LiZhongQC.b33_t_chi ν (LiZhongQC.bersFunction lam.val)) =
      LiZhongQC.b33_t_chi μ (LiZhongQC.bersFunction lam.val) := by
  rw [LiZhongQC.b33_t_chi_spec ν lam]
  have hval : (LiZhongQC.b33_t_tb ν lam).val =
      LiZhongQC.translatedBeltrami ν.val lam.val := rfl
  rw [← hval,
    LiZhongQC.b33_t_chi_spec (LiZhongQC.b33_t_tb ν μ) (LiZhongQC.b33_t_tb ν lam),
    LiZhongQC.b33_t_chi_spec μ lam, sourceTranslatedBeltrami_recentring]

variable {Γ : Subgroup Deck}

/-- The actual native translated coefficient has the same normalized composite,
including after passing through its genuine L-infinity class. -/
theorem normalizedMap_translatedBall_comp
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (z : ℂ) :
    normalizedMap (translatedBall hΓ ν μ) (normalizedMap ν z) = normalizedMap μ z := by
  rw [translatedBall_eq_fromSource, normalizedMap_fromSourceGamma]
  change LiZhongQC.fMuSym (LiZhongQC.translatedBeltrami
    (toSourceGamma ν).val.val (toSourceGamma μ).val.val) (normalizedMap ν z) = _
  rw [LiZhongQC.b33_t_tb_fMuSym]
  exact congrArg (normalizedMap μ) ((normalizedInverse_spec ν).choose_spec.2.1 z)

/-- The same identity on the actual upper-half-plane equivalences. -/
theorem normalizedUpperEquiv_translatedBall_comp
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) (z : ℍ) :
    normalizedUpperEquiv (translatedBall hΓ ν μ) (normalizedUpperEquiv ν z) =
      normalizedUpperEquiv μ z := by
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe] using normalizedMap_translatedBall_comp hΓ ν μ z

private theorem normalizedUpperEquiv_conjugacy {Δ : Subgroup Deck}
    (ρ : Ball Δ) (γ δ : Deck)
    (h : ∀ z ∈ LiZhongQC.upperHalf,
      normalizedMap ρ (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        LiZhongQC.mobiusFn (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1) (normalizedMap ρ z))
    (z : ℍ) : normalizedUpperEquiv ρ (γ • z) = δ • normalizedUpperEquiv ρ z := by
  apply UpperHalfPlane.ext
  have hz := h z z.im_pos
  rw [LiZhongQC.b33_d_mobiusFn_smul γ z] at hz
  change normalizedMap ρ (γ • z : ℍ) =
    LiZhongQC.mobiusFn (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1)
      (normalizedUpperEquiv ρ z : ℂ) at hz
  rw [LiZhongQC.b33_d_mobiusFn_smul δ (normalizedUpperEquiv ρ z)] at hz
  exact hz

/-- Recentring gives exactly the same genuine projective group, while allowing
the unavoidable independent central signs in the chosen SL matrix lifts. -/
theorem deformedGroup_translatedBall_projectiveImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    (deformedGroup (deformedGroup_spec hΓ ν).1 (translatedBall hΓ ν μ)).map
        Hyperbolic.realSLMobius =
      (deformedGroup hΓ μ).map Hyperbolic.realSLMobius := by
  let κ := translatedBall hΓ ν μ
  have hcomp := normalizedUpperEquiv_translatedBall_comp hΓ ν μ
  have compare (γ A B C : Deck)
      (hν : ∀ z : ℍ, normalizedUpperEquiv ν (γ • z) = A • normalizedUpperEquiv ν z)
      (hκ : ∀ z : ℍ, normalizedUpperEquiv κ (A • z) = B • normalizedUpperEquiv κ z)
      (hμ : ∀ z : ℍ, normalizedUpperEquiv μ (γ • z) = C • normalizedUpperEquiv μ z) :
      ∀ z : ℍ, B • z = C • z := by
    intro z
    let w := (normalizedUpperEquiv μ).symm z
    have he : normalizedUpperEquiv μ (γ • w) = B • normalizedUpperEquiv μ w := by
      calc
        normalizedUpperEquiv μ (γ • w) =
            normalizedUpperEquiv κ (normalizedUpperEquiv ν (γ • w)) := (hcomp _).symm
        _ = normalizedUpperEquiv κ (A • normalizedUpperEquiv ν w) :=
          congrArg (normalizedUpperEquiv κ) (hν w)
        _ = B • normalizedUpperEquiv κ (normalizedUpperEquiv ν w) := hκ _
        _ = B • normalizedUpperEquiv μ w := congrArg (fun y : ℍ => B • y) (hcomp w)
    simpa only [w, Equiv.apply_symm_apply] using he.symm.trans (hμ w)
  apply realSL_image_eq_of_actions
  · intro B hB
    obtain ⟨A, hA, hκ⟩ := (deformedGroup_spec (deformedGroup_spec hΓ ν).1 κ).2.2 B hB
    obtain ⟨γ, hγ, hν⟩ := (deformedGroup_spec hΓ ν).2.2 A hA
    obtain ⟨C, hC, hμ⟩ := (deformedGroup_spec hΓ μ).2.1 γ hγ
    exact ⟨C, hC, compare γ A B C (normalizedUpperEquiv_conjugacy ν γ A hν)
      (normalizedUpperEquiv_conjugacy κ A B hκ) (normalizedUpperEquiv_conjugacy μ γ C hμ)⟩
  · intro C hC
    obtain ⟨γ, hγ, hμ⟩ := (deformedGroup_spec hΓ μ).2.2 C hC
    obtain ⟨A, hA, hν⟩ := (deformedGroup_spec hΓ ν).2.1 γ hγ
    obtain ⟨B, hB, hκ⟩ := (deformedGroup_spec (deformedGroup_spec hΓ ν).1 κ).2.1 A hA
    refine ⟨B, hB, fun z => ?_⟩
    exact (compare γ A B C (normalizedUpperEquiv_conjugacy ν γ A hν)
      (normalizedUpperEquiv_conjugacy κ A B hκ) (normalizedUpperEquiv_conjugacy μ γ C hμ) z).symm

/-- In the common original weighted target, the actual native Bers maps obey
the exact cocycle on the whole genuine coefficient Bers image. -/
theorem bersTranslation_translatedBall_recentring
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) (hφ : φ ∈ coefficientBersImage hΓ) :
    (bersTranslation (deformedGroup_spec hΓ ν).1 (translatedBall hΓ ν μ)
        (bersTranslation hΓ ν φ)).val =
      (bersTranslation hΓ μ φ).val := by
  obtain ⟨lam, rfl⟩ := (mem_coefficientBersImage_iff_coefficient hΓ φ).mp hφ
  have hκ : LiZhongQC.b33_t_chi (toSourceGamma (translatedBall hΓ ν μ)).val =
      LiZhongQC.b33_t_chi
        (LiZhongQC.b33_t_tb (toSourceGamma ν).val (toSourceGamma μ).val) := by
    apply sourceBersTranslation_eq_of_sameBoundary
    intro x
    change normalizedMap (translatedBall hΓ ν μ) x =
      LiZhongQC.fMuSym
        (LiZhongQC.b33_t_tb (toSourceGamma ν).val (toSourceGamma μ).val).val x
    have hn := normalizedMap_fromSourceGamma (translatedSource hΓ ν μ)
    rw [← translatedBall_eq_fromSource hΓ ν μ] at hn
    exact congrFun hn (x : ℂ)
  apply BersWeighted.decode_injective
  change ((bersTranslation (deformedGroup_spec hΓ ν).1 (translatedBall hΓ ν μ)
      (bersTranslation hΓ ν (BersWeighted.automorphicProjection hΓ lam.val))).toSource : ℂ → ℂ) =
    ((bersTranslation hΓ μ (BersWeighted.automorphicProjection hΓ lam.val)).toSource : ℂ → ℂ)
  rw [bersTranslation_toSource (deformedGroup_spec hΓ ν).1,
    bersTranslation_toSource hΓ ν, bersTranslation_toSource hΓ μ, hκ,
    BersWeighted.automorphicProjection_toSource_eq hΓ lam.val (Ball.norm_lt_one lam)]
  exact sourceBersTranslation_recentring
    (toSourceGamma ν).val (toSourceGamma μ).val (toSourceGamma lam).val

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
