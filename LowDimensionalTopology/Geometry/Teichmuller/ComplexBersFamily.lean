module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersCoordinates
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.S34Final

/-!
# Actual proper holomorphic fibres indexed by native markings

The Bers orbit quotient is the total space. Its base is a genuine open subset
of finite-dimensional complex space, and the fibre attached to a native class
is a closed surface with the original analytic orbit-covering description.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- A proper holomorphic family with genuine compact fibres for all native classes. -/
theorem exists_proper_holomorphic_family {g : ℕ} (hg : 1 < g)
    (hgenus : R.HasGenus g) (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    ∃ (coords : TeichmullerSpace.{u, u} R → Fin (3 * g - 3) → ℂ)
      (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (_ : TopologicalSpace (LiZhongQC.BersQuotient Γ))
      (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (LiZhongQC.BersQuotient Γ))
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (LiZhongQC.BersQuotient Γ))
      (pr : LiZhongQC.BersQuotient Γ →
        (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ))),
      LiZhongQC.IsHolomorphicFamily (n := 3 * g - 3) pr ∧
      ∀ a : TeichmullerSpace.{u, u} R,
        ∃ (Y : LiZhongQC.ClosedRS.{u}) (j : Y.carrier → LiZhongQC.BersQuotient Γ)
          (cov : ℂ → Y.carrier),
          LiZhongQC.HasGenus Y.carrier g ∧ Topology.IsEmbedding j ∧
          range j = pr ⁻¹' {⟨coords a, mem_range_self a⟩} ∧
          (∀ z (hz : z ∈ LiZhongQC.bersDisc Γ
              (LiZhongQC.bersMapGamma Γ
                (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a))),
            j (cov z) = Quot.mk _
              ⟨(LiZhongQC.bersMapGamma Γ
                  (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a), z),
                ⟨gammaEquiv R hg hgenus hPresentation hΓ hfree hp a, rfl⟩, hz⟩) ∧
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov
            (LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ
              (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a))) ∧
          ∀ z ∈ LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ
              (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)),
            ∀ w ∈ LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ
                (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)),
              cov z = cov w ↔ ∃ γ ∈ Γ, w = LiZhongQC.bersFiberAction Γ γ
                (LiZhongQC.bersMapGamma Γ
                  (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)) z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨c, hc, hopen, τ, atlas, hmanifold, pr, hfamily, hfibre⟩ :=
    LiZhongQC.thm34_1_bers hg (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp
  let e := gammaEquiv R hg hgenus hPresentation hΓ hfree hp
  have hrange : range (c ∘ e) = range c := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q, congrArg c (e.apply_symm_apply q)⟩
  let U₀ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ) := ⟨range c, hopen⟩
  let Q : (U : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)) →
      (TeichmullerSpace.{u, u} R → U) → Prop := fun U b =>
    ∃ (_ : TopologicalSpace (LiZhongQC.BersQuotient Γ))
      (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (LiZhongQC.BersQuotient Γ))
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (LiZhongQC.BersQuotient Γ))
      (pr : LiZhongQC.BersQuotient Γ → U),
      LiZhongQC.IsHolomorphicFamily (n := 3 * g - 3) pr ∧
      ∀ a : TeichmullerSpace.{u, u} R,
        ∃ (Y : LiZhongQC.ClosedRS.{u}) (j : Y.carrier → LiZhongQC.BersQuotient Γ)
          (cov : ℂ → Y.carrier),
          LiZhongQC.HasGenus Y.carrier g ∧ Topology.IsEmbedding j ∧
          range j = pr ⁻¹' {b a} ∧
          (∀ z (hz : z ∈ LiZhongQC.bersDisc Γ
              (LiZhongQC.bersMapGamma Γ (e a))),
            j (cov z) = Quot.mk _
              ⟨(LiZhongQC.bersMapGamma Γ (e a), z), ⟨e a, rfl⟩, hz⟩) ∧
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov
            (LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ (e a))) ∧
          ∀ z ∈ LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ (e a)),
            ∀ w ∈ LiZhongQC.bersDisc Γ (LiZhongQC.bersMapGamma Γ (e a)),
              cov z = cov w ↔ ∃ γ ∈ Γ, w = LiZhongQC.bersFiberAction Γ γ
                (LiZhongQC.bersMapGamma Γ (e a)) z
  have hsource : Q U₀ (fun a => ⟨c (e a), mem_range_self (e a)⟩) := by
    exact ⟨τ, atlas, hmanifold, pr, hfamily, fun a => hfibre (e a)⟩
  have htransport : ∀ (U : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ))
      (b : TeichmullerSpace.{u, u} R → U), U = U₀ →
      (∀ a, (b a : Fin (3 * g - 3) → ℂ) = c (e a)) → Q U b := by
    intro U b hU hb
    subst U
    have hb' : b = (fun a => ⟨c (e a), mem_range_self (e a)⟩ :
        TeichmullerSpace.{u, u} R → U₀) := by
      funext a
      exact Subtype.ext (hb a)
    rw [hb']
    exact hsource
  let U₁ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ) :=
    ⟨range (c ∘ e), hrange.symm ▸ hopen⟩
  have hU : U₁ = U₀ := TopologicalSpace.Opens.ext hrange
  refine ⟨c ∘ e, hc.comp e.injective, hrange.symm ▸ hopen, ?_⟩
  exact htransport U₁ (fun a => ⟨c (e a), mem_range_self a⟩) hU (fun a => rfl)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
