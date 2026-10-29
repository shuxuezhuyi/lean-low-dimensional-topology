module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalCollarSupport

/-!
# One angular support from the actual covering fibers

The existing canonical-strip fiber argument only uses the given covering
and its full-period generator. It applies to that same actual covering
without constructing a new hyperbolic quotient model for the projection.
The proof is extracted from
`originalClosedGeodesic_exists_normalized_angular_one_support`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- Full-period fibers in the given canonical strip make the actual normalized
right-coset angular coefficient have at most one nonzero support. -/
theorem normalizedAngular_one_support_of_canonical_fibers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup Deck} {p : ℍ → X} (hp : LiZhongQC.IsUniformization Γ p)
    (A Q : Deck) (s : ℝ) (hs : 0 < s) (hAΓ : A ∈ Γ)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (hfib : ∀ z ∈ Hyperbolic.hCanonicalRegion A,
      ∀ w ∈ Hyperbolic.hCanonicalRegion A,
        p z = p w ↔ ∃ n : ℤ, w = A ^ n • z) :
    let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
    ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s)),
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΓQ s u ζ ≠ 0 →
          rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΓQ s v ζ ≠ 0 →
            u = v := by
  classical
  let ΓQ : Subgroup Deck := Γ.map (MulAut.conj Q).toMonoidHom
  let θ : Width := canonicalBandWidth s hs
  change ∀ ζ : ℂ,
    ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s)),
      rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ ≠ 0 →
      rightCosetInfinitesimalZeroExtension θ ΓQ s v ζ ≠ 0 → u = v
  intro ζ u v
  refine Quotient.inductionOn₂ u v ?_
  intro γ δ hγ hδ
  change pullbackInfinitesimalZeroExtension θ γ.val ζ ≠ 0 at hγ
  change pullbackInfinitesimalZeroExtension θ δ.val ζ ≠ 0 at hδ
  have hζ : 0 < ζ.im := by
    by_contra hn
    exact hγ (pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ.val
      (le_of_not_gt hn))
  let z : ℍ := ⟨ζ, hζ⟩
  have hband (E : Deck) (hE : pullbackInfinitesimalZeroExtension θ E ζ ≠ 0) :
      E • z ∈ closedAngularBand θ := by
    by_contra hn
    have hn' : Complex.arg ((E • z : ℍ) : ℂ) ∉ interval θ := hn
    apply hE
    change pullbackInfinitesimalZeroExtension θ E (z : ℂ) = 0
    rw [pullbackInfinitesimalZeroExtension_coe, infinitesimal, ite_eq_right hn', zero_mul]
  have hcan (E : Deck) (hE : pullbackInfinitesimalZeroExtension θ E ζ ≠ 0) :
      Q⁻¹ • (E • z) ∈ Hyperbolic.hCanonicalRegion A := by
    have hD : E • z ∈ Hyperbolic.hCanonicalRegion (Fuchsian.hLogDilationSL s) :=
      closedAngularBand_canonicalBandWidth_subset_hCanonicalRegion s hs (hband E hE)
    rw [← Hyperbolic.hCanonicalRegion_congr _ _ hQA] at hD
    apply (Hyperbolic.hCanonicalRegion_conjugation_mem A Q (Q⁻¹ • (E • z))).mp
    simpa only [smul_inv_smul] using hD
  have hγΓ : γ.val ∈ Γ.map (MulAut.conj Q).toMonoidHom := γ.property
  have hδΓ : δ.val ∈ Γ.map (MulAut.conj Q).toMonoidHom := δ.property
  obtain ⟨g, hg, hgQ⟩ := Subgroup.mem_map.mp hγΓ
  obtain ⟨d, hd, hdQ⟩ := Subgroup.mem_map.mp hδΓ
  change Q * g * Q⁻¹ = γ.val at hgQ
  change Q * d * Q⁻¹ = δ.val at hdQ
  let z₀ : ℍ := Q⁻¹ • z
  let x : ℍ := g • z₀
  let y : ℍ := d • z₀
  have hx : x ∈ Hyperbolic.hCanonicalRegion A := by
    simpa only [← hgQ, mul_smul, inv_smul_smul, x, z₀] using hcan γ.val hγ
  have hy : y ∈ Hyperbolic.hCanonicalRegion A := by
    simpa only [← hdQ, mul_smul, inv_smul_smul, y, z₀] using hcan δ.val hδ
  have hxy : p x = p y := by
    dsimp only [x, y]
    rw [LiZhongQC.s30a_p_smul hp hg, LiZhongQC.s30a_p_smul hp hd]
  obtain ⟨n, hn⟩ := (hfib x hx y hy).mp hxy
  let C : Deck := d * g⁻¹
  have hCΓ : C ∈ Γ := Γ.mul_mem hd (Γ.inv_mem hg)
  have hCx : C • x = y := by
    dsimp only [C, x, y]
    rw [mul_smul, inv_smul_smul]
  let D : Deck := (A ^ n)⁻¹ * C
  have hDΓ : D ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.zpow_mem hAΓ n)) hCΓ
  have hDfix : D • x = x := by
    dsimp only [D]
    rw [mul_smul, hCx, hn, inv_smul_smul]
  have hDproj : Hyperbolic.realSLMobius D = 1 := by
    rcases LiZhongQC.s27g_actsFreely hp D hDΓ x hDfix with he | he
    · rw [he, map_one]
    · rw [he, Hyperbolic.realSLMobius_neg, map_one]
  have hCproj : (Hyperbolic.realSLMobius A) ^ n = Hyperbolic.realSLMobius C := by
    apply inv_mul_eq_one.mp
    simpa only [D, map_mul, map_inv, map_zpow] using hDproj
  have hnormC : Hyperbolic.realSLMobius (δ.val * γ.val⁻¹) =
      Hyperbolic.realSLMobius (Q * C * Q⁻¹) := by
    apply congrArg Hyperbolic.realSLMobius
    rw [← hdQ, ← hgQ]
    dsimp only [C]
    group
  have hpowers : Hyperbolic.realSLMobius (δ.val * γ.val⁻¹) ∈
      Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    calc
      (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) ^ n =
          (Hyperbolic.realSLMobius Q * Hyperbolic.realSLMobius A *
            (Hyperbolic.realSLMobius Q)⁻¹) ^ n := by
        rw [← hQA, map_mul, map_mul, map_inv]
      _ = Hyperbolic.realSLMobius Q * (Hyperbolic.realSLMobius A) ^ n *
          (Hyperbolic.realSLMobius Q)⁻¹ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
          (((MulAut.conj (Hyperbolic.realSLMobius Q)).toMonoidHom).map_zpow
            (Hyperbolic.realSLMobius A) n).symm
      _ = Hyperbolic.realSLMobius (Q * C * Q⁻¹) := by
        simp only [hCproj, map_mul, map_inv]
      _ = Hyperbolic.realSLMobius (δ.val * γ.val⁻¹) := hnormC.symm
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  change (Hyperbolic.realSLMobius.comp ΓQ.subtype) (δ * γ⁻¹) ∈
    Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using hpowers


end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
