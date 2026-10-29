module

public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeedRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.AngularLengthKernelPoincare
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# The actual geodesic right cosets and series under the same real Möbius change

The full inverse image of the projective cyclic group, including the actual
special-linear kernel, is transported by matrix conjugation. The resulting
right-coset equivalence transports every actual section. The original endpoint
series is the literal quadratic pullback of that same normalized series.

The actual Möbius composition and derivative APIs reuse Wu Xiaobin's
Li-Zhong-QC formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open GammaMeasurableBeltrami

private theorem conjugate_cyclic_mem_iff (Γ : Subgroup Deck) (A Q : Deck) (s : ℝ)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) (γ : Γ) :
    (MulAut.conj Q).subgroupMap Γ γ ∈
        AngularTwist.projectiveDilationSubgroup (LiZhongQC.conjGroup Γ Q) s ↔
      γ ∈ Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
        (Subgroup.zpowers (Hyperbolic.realSLMobius A)) := by
  let E := (MulAut.conj Q).subgroupMap Γ
  let EP := MulAut.conj (Hyperbolic.realSLMobius Q)
  have hA : EP (Hyperbolic.realSLMobius A) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) := by
    change Hyperbolic.realSLMobius Q * Hyperbolic.realSLMobius A *
      (Hyperbolic.realSLMobius Q)⁻¹ = _
    simpa only [map_mul, map_inv] using hQA
  have hγ : EP (Hyperbolic.realSLMobius γ.val) = Hyperbolic.realSLMobius (E γ).val := by
    change Hyperbolic.realSLMobius Q * Hyperbolic.realSLMobius γ.val *
      (Hyperbolic.realSLMobius Q)⁻¹ = Hyperbolic.realSLMobius (Q * γ.val * Q⁻¹)
    simp only [map_mul, map_inv]
  change Hyperbolic.realSLMobius (E γ).val ∈
      Subgroup.zpowers (Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) ↔
    Hyperbolic.realSLMobius γ.val ∈ Subgroup.zpowers (Hyperbolic.realSLMobius A)
  rw [← hγ, ← hA]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, EP.injective ((map_zpow EP (Hyperbolic.realSLMobius A) n).trans hn)⟩
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, (map_zpow EP (Hyperbolic.realSLMobius A) n).symm.trans (congrArg EP hn)⟩

/-- The same endpoint term transforms by the actual conjugated map and fourth denominator. -/
theorem normalized_term (A : Deck) (hA : Hyperbolic.realSLMobius A ≠ 1)
    (ht : 4 < (Matrix.trace A.val) ^ 2) (Q : Deck) (s : ℝ) (hs : 0 < s)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) (γ : Deck)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m γ z) *
        (deriv (LiZhongQC.h36p_m γ) z) ^ 2 =
      (deriv (LiZhongQC.h36p_m (Q * γ * Q⁻¹)) (LiZhongQC.h36p_m Q z) /
        LiZhongQC.h36p_m (Q * γ * Q⁻¹) (LiZhongQC.h36p_m Q z)) ^ 2 /
        ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 := by
  let δ : Deck := Q * γ * Q⁻¹
  have hmatrix : Q * γ = δ * Q := by dsimp only [δ]; group
  have hcomp : (fun w => LiZhongQC.h36p_m Q (LiZhongQC.h36p_m γ w)) =ᶠ[𝓝 z]
      (fun w => LiZhongQC.h36p_m δ (LiZhongQC.h36p_m Q w)) := by
    filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with w hw
    rw [← LiZhongQC.h36p_b_m_mul Q γ hw, ← LiZhongQC.h36p_b_m_mul δ Q hw, hmatrix]
  have hvalue : LiZhongQC.h36p_m Q (LiZhongQC.h36p_m γ z) =
      LiZhongQC.h36p_m δ (LiZhongQC.h36p_m Q z) := by
    rw [← LiZhongQC.h36p_b_m_mul Q γ hz, ← LiZhongQC.h36p_b_m_mul δ Q hz, hmatrix]
  have hQγ := LiZhongQC.h36p_m_hasDerivAt Q (LiZhongQC.h36p_m_mem γ hz)
  have hγ := LiZhongQC.h36p_m_hasDerivAt γ hz
  have hδ := LiZhongQC.h36p_m_hasDerivAt δ (LiZhongQC.h36p_m_mem Q hz)
  have hQ := LiZhongQC.h36p_m_hasDerivAt Q hz
  have hderiv : deriv (LiZhongQC.h36p_m Q) (LiZhongQC.h36p_m γ z) *
      deriv (LiZhongQC.h36p_m γ) z =
      deriv (LiZhongQC.h36p_m δ) (LiZhongQC.h36p_m Q z) * deriv (LiZhongQC.h36p_m Q) z := by
    rw [hQγ.deriv, hγ.deriv, hδ.deriv, hQ.deriv]
    exact ((hQγ.comp z hγ).congr_of_eventuallyEq hcomp.symm).unique (hδ.comp z hQ)
  rw [hyperbolicSeed_eq_squaredLogDerivative A hA ht Q s hs hQA
    (LiZhongQC.h36p_m_mem γ hz)]
  change _ = (deriv (LiZhongQC.h36p_m δ) (LiZhongQC.h36p_m Q z) /
    LiZhongQC.h36p_m δ (LiZhongQC.h36p_m Q z)) ^ 2 / ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4
  calc
    _ = ((deriv (LiZhongQC.h36p_m Q) (LiZhongQC.h36p_m γ z) *
        deriv (LiZhongQC.h36p_m γ) z) / LiZhongQC.h36p_m Q (LiZhongQC.h36p_m γ z)) ^ 2 := by ring
    _ = ((deriv (LiZhongQC.h36p_m δ) (LiZhongQC.h36p_m Q z) *
        deriv (LiZhongQC.h36p_m Q) z) / LiZhongQC.h36p_m δ (LiZhongQC.h36p_m Q z)) ^ 2 := by
      rw [hderiv, hvalue]
    _ = (deriv (LiZhongQC.h36p_m δ) (LiZhongQC.h36p_m Q z) /
        LiZhongQC.h36p_m δ (LiZhongQC.h36p_m Q z)) ^ 2 * (deriv (LiZhongQC.h36p_m Q) z) ^ 2 := by
      ring
    _ = _ := by
      rw [hQ.deriv]
      simp only [div_pow, one_pow, ← pow_mul, mul_one_div]

/-- Actual matrix conjugation transports the full projective cyclic right
cosets, every original section and the same original endpoint series. -/
theorem geodesicSeries_realMobius_conjugate (Γ : Subgroup Deck) (A : Deck)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (Q : Deck) (s : ℝ) (hs : 0 < s)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s)) :
    let ΓQ := LiZhongQC.conjGroup Γ Q
    let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))
    let CA := Quotient (QuotientGroup.rightRel SA)
    let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
    let E := (MulAut.conj Q).subgroupMap Γ
    ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
      ∃ (e : CA ≃ CQ) (ρQ : CQ → ΓQ),
        (∀ γ : Γ, e (Quotient.mk _ γ) = Quotient.mk _ (E γ)) ∧
        (∀ u : CA, ρQ (e u) = E (ρ u)) ∧
        (∀ v : CQ, Quotient.mk _ (ρQ v) = v) ∧
        ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
          (∑' u : CA, seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
              (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2) =
            (∑' v : CQ,
              (deriv (LiZhongQC.h36p_m (ρQ v).val) (LiZhongQC.h36p_m Q z) /
                LiZhongQC.h36p_m (ρQ v).val (LiZhongQC.h36p_m Q z)) ^ 2) /
              ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 := by
  dsimp only
  intro ρ hρ
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
    (Subgroup.zpowers (Hyperbolic.realSLMobius A))
  let CA := Quotient (QuotientGroup.rightRel SA)
  let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
  let E : Γ ≃* ΓQ := (MulAut.conj Q).subgroupMap Γ
  have hrel (γ δ : Γ) : QuotientGroup.rightRel SA γ δ ↔
      QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s) (E γ) (E δ) := by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    rw [← map_inv E, ← map_mul E]
    exact (conjugate_cyclic_mem_iff Γ A Q s hQA (δ * γ⁻¹)).symm
  let e : CA ≃ CQ := Quotient.congr E.toEquiv hrel
  let ρQ : CQ → ΓQ := fun v => E (ρ (e.symm v))
  have hρtransport (u : CA) : ρQ (e u) = E (ρ u) := by
    change E (ρ (e.symm (e u))) = E (ρ u)
    rw [e.symm_apply_apply]
  have hρQ (v : CQ) : Quotient.mk _ (ρQ v) = v := by
    change e (Quotient.mk _ (ρ (e.symm v))) = v
    rw [hρ, e.apply_symm_apply]
  refine ⟨e, ρQ, (fun _ => rfl), hρtransport, hρQ, ?_⟩
  intro z hz
  calc
    _ = ∑' u : CA,
        (deriv (LiZhongQC.h36p_m (ρQ (e u)).val) (LiZhongQC.h36p_m Q z) /
          LiZhongQC.h36p_m (ρQ (e u)).val (LiZhongQC.h36p_m Q z)) ^ 2 /
            ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 := by
      apply tsum_congr
      intro u
      rw [hρtransport]
      exact normalized_term A hA ht Q s hs hQA (ρ u).val hz
    _ = ∑' v : CQ,
        (deriv (LiZhongQC.h36p_m (ρQ v).val) (LiZhongQC.h36p_m Q z) /
          LiZhongQC.h36p_m (ρQ v).val (LiZhongQC.h36p_m Q z)) ^ 2 /
            ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 :=
      e.tsum_eq (fun v : CQ =>
        (deriv (LiZhongQC.h36p_m (ρQ v).val) (LiZhongQC.h36p_m Q z) /
          LiZhongQC.h36p_m (ρQ v).val (LiZhongQC.h36p_m Q z)) ^ 2 /
            ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4)
    _ = _ := tsum_div_const

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
