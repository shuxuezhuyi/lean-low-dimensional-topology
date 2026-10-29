/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkedSpace
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual targets on the reference carrier's universe

A marking supplies an actual homeomorphism from the reference to its target.
Pulling back the target's true complex atlas along that homeomorphism gives a
biholomorphic target in the reference universe. A zero universe lift separates
its complex atlas from the reference atlas without changing the point set.
All original targets and their marked equivalence classes are retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC
universe u v w

/-- Pull back the actual native atlas along an actual homeomorphism. -/
def Surface.pullbackHomeomorph {X : Type u} [TopologicalSpace X]
    (S : Surface.{v}) (e : X ≃ₜ S.carrier) : Surface.{u} where
  carrier := X
  topology := inferInstance
  riemann :=
    { toRiemannAtlas := S.riemann.toRiemannAtlas.liftLocalHomeomorph e e.isLocalHomeomorph
      t2Space := e.isEmbedding.t2Space
      connectedSpace := by
        let := S.riemann.pathConnectedSpace
        let := e.symm.pathConnectedSpace
        infer_instance }

/-- The actual transporting homeomorphism is analytic in both given atlases. -/
theorem Surface.pullbackHomeomorph_analytic {X : Type u} [TopologicalSpace X]
    (S : Surface.{v}) (e : X ≃ₜ S.carrier) :
    RiemannAnalyticMap (S.pullbackHomeomorph e).riemann.toRiemannAtlas
      S.riemann.toRiemannAtlas e :=
  S.riemann.toRiemannAtlas.liftLocalHomeomorph_projection_analytic e e.isLocalHomeomorph

/-- The original target atlas, on a zero universe lift of the reference carrier. -/
def Marked.sourceCarrierTarget {R : Surface.{u}} (m : Marked.{u, v} R) : Surface.{u} :=
  m.target.pullbackHomeomorph
    ((Homeomorph.ulift : ULift.{0, u} R.carrier ≃ₜ R.carrier).trans m.marking)

/-- This map identifies the pulled-back target with the original actual target. -/
def Marked.sourceCarrierProjection {R : Surface.{u}} (m : Marked.{u, v} R) :
    m.sourceCarrierTarget.carrier ≃ₜ m.target.carrier :=
  (Homeomorph.ulift : ULift.{0, u} R.carrier ≃ₜ R.carrier).trans m.marking

/-- The target identification is analytic for the genuine pulled-back atlas. -/
theorem Marked.sourceCarrierProjection_analytic {R : Surface.{u}}
    (m : Marked.{u, v} R) :
    RiemannAnalyticMap m.sourceCarrierTarget.riemann.toRiemannAtlas
      m.target.riemann.toRiemannAtlas m.sourceCarrierProjection :=
  m.target.pullbackHomeomorph_analytic m.sourceCarrierProjection

/-- The same target identification is a genuine native biholomorphism. -/
theorem Marked.sourceCarrierProjection_biholomorphic {R : Surface.{u}}
    (m : Marked.{u, v} R) :
    IsBiholomorphic (m.sourceCarrierProjection : m.sourceCarrierTarget.carrier → m.target.carrier) :=
  (analyticHomeomorph_iff_sourceBiholomorphic
    m.sourceCarrierTarget.riemann.toRiemannAtlas m.target.riemann.toRiemannAtlas
    m.sourceCarrierProjection).mp m.sourceCarrierProjection_analytic

/-- The same original marking, transported through the actual biholomorphic
identification of its target. Neither a covering nor a lift is supplied. -/
def Marked.sourceCarrierRepresentative {R : Surface.{u}}
    (m : Marked.{u, v} R) : Marked.{u, u} R where
  target := m.sourceCarrierTarget
  marking := m.marking.trans m.sourceCarrierProjection.symm
  qc := s28q_isQCRS_trans m.qc
    ⟨1, (isKQCRS_one_iff m.sourceCarrierProjection.symm).mpr
      m.sourceCarrierProjection_biholomorphic.homeomorph_symm⟩

/-- Projecting the transported marking recovers the original marking pointwise. -/
@[simp] theorem Marked.sourceCarrierProjection_marking {R : Surface.{u}}
    (m : Marked.{u, v} R) (x : R.carrier) :
    m.sourceCarrierProjection (m.sourceCarrierRepresentative.marking x) = m.marking x :=
  m.sourceCarrierProjection.apply_symm_apply (m.marking x)

/-- The actual original conformal-homotopy relation is preserved and reflected
by these target identifications, for independently sized actual targets. -/
theorem marked_equivalent_iff_sourceCarrierRepresentatives {R : Surface.{u}}
    (m n : Marked.{u, v} R) :
    m.Equivalent n ↔ m.sourceCarrierRepresentative.Equivalent n.sourceCarrierRepresentative := by
  rw [marked_equivalent_iff_analytic m n,
    marked_equivalent_iff_analytic m.sourceCarrierRepresentative n.sourceCarrierRepresentative]
  let a := m.sourceCarrierProjection
  let b := n.sourceCarrierProjection
  have ha := m.sourceCarrierProjection_analytic
  have hb := n.sourceCarrierProjection_analytic
  constructor
  · rintro ⟨c, hc, hh⟩
    let d := a.trans (c.trans b.symm)
    refine ⟨d, ?_, ?_⟩
    · exact (riemannAnalyticMap_homeomorph_symm b hb).comp (hc.comp ha)
    · obtain ⟨H⟩ := hh
      refine ⟨{ toFun := fun tx => b.symm (H tx)
                continuous_toFun := b.symm.continuous.comp H.continuous_toFun
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro x
        change b.symm (H (0, x)) = b.symm (c (a (a.symm (m.marking x))))
        calc
          b.symm (H (0, x)) = b.symm (c (m.marking x)) :=
            congrArg b.symm (H.map_zero_left x)
          _ = b.symm (c (a (a.symm (m.marking x)))) := by rw [a.apply_symm_apply]
      · intro x
        exact congrArg b.symm (H.map_one_left x)
  · rintro ⟨c, hc, hh⟩
    let d := a.symm.trans (c.trans b)
    refine ⟨d, ?_, ?_⟩
    · exact hb.comp (hc.comp (riemannAnalyticMap_homeomorph_symm a ha))
    · obtain ⟨H⟩ := hh
      refine ⟨{ toFun := fun tx => b (H tx)
                continuous_toFun := b.continuous.comp H.continuous_toFun
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro x
        exact congrArg b (H.map_zero_left x)
      · intro x
        change b (H (1, x)) = n.marking x
        calc
          b (H (1, x)) = b (b.symm (n.marking x)) := congrArg b (H.map_one_left x)
          _ = n.marking x := b.apply_symm_apply _

/-- Equality in the original independently sized quotient is equivalent to
equality of these actual common-universe representatives. -/
theorem mk_eq_mk_iff_sourceCarrierRepresentatives {R : Surface.{u}}
    (m n : Marked.{u, v} R) :
    mk m = mk n ↔ mk m.sourceCarrierRepresentative = mk n.sourceCarrierRepresentative := by
  constructor
  · intro h
    exact Quotient.sound
      ((marked_equivalent_iff_sourceCarrierRepresentatives m n).mp (Quotient.exact h))
  · intro h
    exact Quotient.sound
      ((marked_equivalent_iff_sourceCarrierRepresentatives m n).mpr (Quotient.exact h))

/-- A biholomorphic target identification transports the actual covering,
holomorphic projection, surjectivity and exact orbit fibres together. -/
theorem uniformization_postcompose_biholomorphic
    {S : Surface.{v}} {T : Surface.{w}}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S.carrier}
    (hp : IsUniformization Γ p) (c : S.carrier ≃ₜ T.carrier)
    (hc : IsBiholomorphic (c : S.carrier → T.carrier)) :
    IsUniformization Γ (c ∘ p) := by
  refine ⟨hp.1.homeomorph_comp c, hc.1.comp hp.2.1, c.surjective.comp hp.2.2.1, ?_⟩
  intro τ₁ τ₂
  change c (p τ₁) = c (p τ₂) ↔ _
  rw [c.injective.eq_iff, hp.2.2.2]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
