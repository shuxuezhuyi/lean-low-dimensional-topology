module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceGammaChange

/-!
# The original nonsymmetric lower-plane quotient

The book space T_beta consists of the actual nonsymmetric normalized maps,
with two compatible coefficients identified precisely when their maps agree
on the whole open lower half-plane. The proved welding comparison identifies
this quotient with the original symmetric boundary quotient. Its topology is
transported through exactly this correspondence, as in the book. The Bers
complex atlas uses the same original finite-dimensional Bers coordinates.

The normalized-solution and welding theorems reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.RawBersQuotient

open GammaMeasurableBeltrami

/-- The actual raw normalized maps agree on the entire open lower half-plane. -/
def lowerSetoid (Γ : Subgroup Deck) : Setoid (LiZhongQC.BeltramiGamma Γ) where
  r μ η := EqOn (LiZhongQC.normalizedSolution μ.val.val)
    (LiZhongQC.normalizedSolution η.val.val) LiZhongQC.lowerHalf
  iseqv := ⟨fun _ _ _ => rfl, fun h _ hz => (h hz).symm,
    fun h₁ h₂ _ hz => (h₁ hz).trans (h₂ hz)⟩

/-- The original book lower-plane model, with its literal raw-solution relation. -/
def TeichBeta (Γ : Subgroup Deck) : Type := Quotient (lowerSetoid Γ)

/-- Welding proves equality of the two actual relations, with no substitution
of a symmetric solution for a nonsymmetric one. -/
theorem lowerRelated_iff_boundaryRelated {Γ : Subgroup Deck}
    (μ η : LiZhongQC.BeltramiGamma Γ) :
    lowerSetoid Γ μ η ↔ LiZhongQC.teichSetoidGamma Γ μ η := by
  constructor
  · intro h
    exact LiZhongQC.bg_l_backward ((LiZhongQC.fMu_lower_model μ.val η.val).mp h)
  · intro h
    exact (LiZhongQC.fMu_lower_model μ.val η.val).mpr (LiZhongQC.bg_l_forward h)

/-- The original lower-plane and symmetric boundary quotients have the same
coefficient classes, by the proved actual welding theorem. -/
def betaGammaEquiv (Γ : Subgroup Deck) : TeichBeta Γ ≃ LiZhongQC.TeichGamma Γ where
  toFun := Quotient.map id (fun μ η h => (lowerRelated_iff_boundaryRelated μ η).mp h)
  invFun := Quotient.map id (fun μ η h => (lowerRelated_iff_boundaryRelated μ η).mpr h)
  left_inv a := Quotient.inductionOn a (fun _ => rfl)
  right_inv a := Quotient.inductionOn a (fun _ => rfl)

theorem betaGammaEquiv_mk {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) :
    betaGammaEquiv Γ (Quotient.mk _ μ) = Quotient.mk _ μ := by rfl

theorem betaGammaEquiv_symm_mk {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) :
    (betaGammaEquiv Γ).symm (Quotient.mk _ μ) = Quotient.mk _ μ := by rfl

instance {Γ : Subgroup Deck} : Nonempty (TeichBeta Γ) :=
  ⟨(betaGammaEquiv Γ).symm (LiZhongQC.TeichGamma.origin Γ)⟩

/-- The Bers map on this quotient is literally the Schwarzian of the raw
normalized solution, with the existing zero extension outside the lower plane. -/
def bersMap (Γ : Subgroup Deck) (a : TeichBeta Γ) : ℂ → ℂ :=
  LiZhongQC.bersMapGamma Γ (betaGammaEquiv Γ a)

theorem bersMap_mk {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) :
    bersMap Γ (Quotient.mk _ μ) = LiZhongQC.bersFunction μ.val.val := by
  exact LiZhongQC.bg_bersMapGamma_eq (μ := μ) rfl

open Surfaces TeichmullerSpace

universe u
variable {A : Type u} [TopologicalSpace A] (R : ClosedRiemannSurface A)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → A}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "Eβ" => betaGammaEquiv Γ
local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "Z" => Fin (3*g-3) → ℂ

/-- The book topology is transported from the actual original group QC metric
through the proved correspondence of the same coefficient classes. -/
@[instance_reducible] def betaMetricSpace : MetricSpace (TeichBeta Γ) := by
  letI := mΓ
  exact MetricSpace.induced (betaGammaEquiv Γ) (betaGammaEquiv Γ).injective inferInstance

local notation "mβ" => betaMetricSpace R hg hgenus hΓ hfree hp

/-- The original class correspondence is a homeomorphism for the book topology. -/
def betaGammaHomeomorph :
    letI := mΓ
    letI := mβ
    TeichBeta Γ ≃ₜ LiZhongQC.TeichGamma Γ := by
  letI := mΓ
  letI := mβ
  exact { Eβ with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      apply continuous_induced_rng.mpr
      change Continuous ((Eβ) ∘ (Eβ).symm)
      have he : (Eβ) ∘ (Eβ).symm = id := funext (Eβ).apply_symm_apply
      rw [he]
      exact continuous_id }

/-- The original Bers coordinates are used on the actual lower-plane quotient. -/
def betaBersCoordinates (a : TeichBeta Γ) : Z := G (Eβ a)

local notation "B" => betaBersCoordinates R hg hgenus hΓ hfree hp

theorem betaBersCoordinates_isOpenEmbedding :
    letI := mβ
    Topology.IsOpenEmbedding B := by
  let := mΓ
  let := mβ
  exact (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).comp
    (betaGammaHomeomorph R hg hgenus hΓ hfree hp).isOpenEmbedding

/-- The Bers atlas on the actual raw lower-plane quotient, transported through
its original class correspondence, as in the book. -/
@[instance_reducible] def betaBersChartedSpace :
    letI := mβ
    ChartedSpace Z (TeichBeta Γ) := by
  letI := mβ
  exact (betaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).singletonChartedSpace

theorem betaGammaEquiv_contMDiff_bothDirections :
    letI := mΓ
    letI := mβ
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    letI := betaBersChartedSpace R hg hgenus hΓ hfree hp
    ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (Eβ) ∧
      ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (Eβ).symm := by
  let := mΓ
  let := mβ
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  let := betaBersChartedSpace R hg hgenus hΓ hfree hp
  let : Nonempty (LiZhongQC.TeichGamma Γ) := ⟨LiZhongQC.TeichGamma.origin Γ⟩
  have hG : ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω G :=
    contMDiff_isOpenEmbedding (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
  have hB : ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω B :=
    contMDiff_isOpenEmbedding (betaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
  constructor
  · exact hB.of_comp_isOpenEmbedding
      (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
  · have hcomp : ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (B ∘ (Eβ).symm) :=
      hG.congr (fun a => by
        change G ((Eβ) ((Eβ).symm a)) = G a
        rw [(Eβ).apply_symm_apply])
    exact hcomp.of_comp_isOpenEmbedding
      (betaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)

end LowDimensionalTopology.Geometry.Teichmuller.RawBersQuotient
