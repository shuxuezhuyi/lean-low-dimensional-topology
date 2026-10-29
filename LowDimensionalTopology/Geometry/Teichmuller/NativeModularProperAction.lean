module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizerModularIsometry
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Proper discontinuity of the original full modular action

The original finite-ball theorem for ALL quasiconformal surface maps is
transported through the actual free-homotopy quotient and the actual
normalizer descent. The native topology is the original QC metric topology.
The full normalizer quotient may have a finite action kernel; the separate
range subgroup consists of the actual acting permutations. No faithfulness
of the original genus-two group is assumed.

The finite-ball analytic theorem is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular

open LiZhongQC

universe u

/-- Only finitely many actual ALL-QC modular classes move some point of an
original half-log ball back into that ball. Source `ModAction` uses direct
precomposition, so the inverse representative is accounted for explicitly. -/
theorem finite_ball_transporter {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X] [CompactSpace X]
    {g : ℕ} (hg : 1 < g) (hgenus : HasGenus X g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : IsUniformization Γ p) (a : TeichSpace X) (r : ℝ) :
    {γ : ModularGroup X | ∃ q : TeichSpace X,
      teichDistance a q < r ∧ teichDistance a (γ • q) < r}.Finite := by
  classical
  obtain ⟨F, hF⟩ := modAction_properly_discontinuous_of_uniformization hg hgenus a r hp
  let toAut : ModTransform X → Aut X := fun h => ⟨h.val, h.property.2⟩
  let S : Set (ModularGroup X) := (F : Set (ModTransform X)).image (fun h => mk (toAut h))
  have hS : S.Finite := F.finite_toSet.image _
  have hsub : ∀ γ : ModularGroup X,
      (∃ q : TeichSpace X, teichDistance a q < r ∧ teichDistance a (γ • q) < r) →
        γ⁻¹ ∈ S := by
    intro γ
    refine Quotient.inductionOn γ ?_
    intro f hγ
    obtain ⟨q, hq, hγq⟩ := hγ
    obtain ⟨h, hhF, hhom⟩ := hF (inverseSourceModTransform f)
      ⟨q, mk f • q, hq, (modAction_iff_smul f q (mk f • q)).mpr rfl, hγq⟩
    refine ⟨h, hhF, ?_⟩
    change (QuotientGroup.mk' (homotopyIdentitySubgroup X)) (toAut h) =
      ((QuotientGroup.mk' (homotopyIdentitySubgroup X)) f)⁻¹
    rw [← map_inv]
    exact ((mk_eq_mk_iff_homotopic (f⁻¹) (toAut h)).mpr hhom).symm
  have hi : (Inv.inv ⁻¹' S).Finite := hS.preimage inv_injective.injOn
  exact hi.subset (fun γ hγ => hsub γ hγ)

end LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "hfree" => LiZhongQC.s27g_actsFreely hp
local notation "Q" => sourceGammaEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "G" => QCNormalizerModular.ModularGroup hp
local notation "T" => LiZhongQC.TeichGamma Γ
local notation "ρ" => upperModularRepresentation R hg hgenus hΓ hp

/-- The full original normalizer quotient has only finitely many elements
moving any point of a given original half-log ball back into that ball. -/
theorem upperModular_finite_ball_transporter :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    ∀ (a : T) (r : ℝ), {γ : G | ∃ b : T,
      LiZhongQC.teichDistanceGamma a b < r ∧
        LiZhongQC.teichDistanceGamma a (ρ γ b) < r}.Finite := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  intro a r
  let E := QCNormalizerModular.modularEquiv hp
  have hfin := SourceQCModular.finite_ball_transporter hg (R.hasSourceGenus hgenus) hp (Q a) r
  apply (hfin.preimage E.injective.injOn).subset
  rintro γ ⟨b, hb, hγb⟩
  refine ⟨Q b, ?_, ?_⟩
  · rw [← sourceGammaEquiv_distance R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp]
    exact hb
  · have he : Q (ρ γ b) = E γ • Q b :=
      gammaModularRepresentation_source R hg hgenus hΓ hp (E γ) b
    rw [← he, ← sourceGammaEquiv_distance R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp]
    exact hγb

include hg hgenus hΓ in
/-- The action data are the actual original permutation representation. -/
@[instance_reducible] def upperModularAction :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    MulAction G T := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  exact MulAction.compHom T ρ

/-- The full ALL-QC original normalizer quotient acts properly discontinuously
on the original group Teichmuller space with its genuine QC metric topology.
No injectivity into the permutation group is required. -/
theorem upperModularAction_properlyDiscontinuous :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    letI := upperModularAction R hg hgenus hΓ hp
    ProperlyDiscontinuousSMul G T := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  let := upperModularAction R hg hgenus hΓ hp
  constructor
  intro K L hK hL
  rcases K.eq_empty_or_nonempty with rfl | ⟨a, _⟩
  · apply (Set.finite_empty : (∅ : Set G).Finite).subset
    rintro γ ⟨_, ⟨b, hb, rfl⟩, _⟩
    exact hb
  obtain ⟨r, hr⟩ := (hK.union hL).isBounded.subset_ball a
  have hfin := upperModular_finite_ball_transporter R hg hgenus hΓ hp a (r / 2)
  apply hfin.subset
  rintro γ ⟨_, ⟨b, hb, rfl⟩, hγb⟩
  refine ⟨b, ?_, ?_⟩
  · have hh := mem_ball.mp (hr (Or.inl hb))
    rw [dist_comm, gammaQCMetricSpace_dist R hg hgenus hΓ hfree hp] at hh
    linarith
  · have hh := mem_ball.mp (hr (Or.inr hγb))
    rw [dist_comm, gammaQCMetricSpace_dist R hg hgenus hΓ hfree hp] at hh
    exact (by linarith : LiZhongQC.teichDistanceGamma a (γ • b) < r / 2)

/-- The actual acting transformation subgroup is properly discontinuous too.
It is the representation range, so genus-two ineffective elements are not
incorrectly identified with distinct automorphisms. -/
theorem upperModularRange_properlyDiscontinuous :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    ProperlyDiscontinuousSMul (ρ).range T := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  let := upperModularAction R hg hgenus hΓ hp
  let := upperModularAction_properlyDiscontinuous R hg hgenus hΓ hp
  constructor
  intro K L hK hL
  have hfin : {γ : G | ((ρ γ) '' K ∩ L).Nonempty}.Finite :=
    finite_disjoint_inter_image hK hL
  apply (hfin.image (ρ).rangeRestrict).subset
  intro δ hδ
  obtain ⟨γ, hγ⟩ := δ.property
  refine ⟨γ, ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, Subgroup.smul_def, Equiv.Perm.smul_def, hγ] using hδ
  · apply Subtype.ext
    exact hγ

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
