/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCTargetUniverse
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCLiftCoefficientTransport
public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.Instances.Shrink

/-!
# Actual marked targets in any target universe

The actual given uniformization is a surjection from the small type ℍ.
Composing it with the actual marking proves that the original target is small
in every universe. Mathlib's Shrink homeomorphism transports its actual
complex atlas, topology and marking; no universe inequality or new smallness
hypothesis is supplied. The literal original lifted coefficient is unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v w

/-- The actual original target is small in any requested target universe,
because the original covering followed by the actual marking is surjective. -/
theorem marked_target_small
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) :
    Small.{v} m.target.carrier :=
  small_of_surjective (m.marking.surjective.comp hp.2.2.1)

/-- The true original target atlas on its actual Mathlib Shrink model. -/
def Marked.targetUniverseTarget
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) : Surface.{v} := by
  letI : Small.{v} m.target.carrier := marked_target_small R hp m
  exact m.target.pullbackHomeomorph
    ((Shrink.homeomorph m.target.carrier).symm : Shrink.{v} m.target.carrier ≃ₜ m.target.carrier)

/-- The actual Shrink homeomorphism identifies the new target with the original. -/
def Marked.targetUniverseProjection
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) :
    (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier ≃ₜ m.target.carrier := by
  letI : Small.{v} m.target.carrier := marked_target_small R hp m
  exact (Shrink.homeomorph m.target.carrier).symm

/-- Atlas transport proves genuine analyticity of the actual target identification. -/
theorem targetUniverseProjection_analytic
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) :
    Surfaces.RiemannAnalyticMap
      (Marked.targetUniverseTarget R hp m : Surface.{v}).riemann.toRiemannAtlas
      m.target.riemann.toRiemannAtlas (Marked.targetUniverseProjection R hp m) := by
  let : Small.{v} m.target.carrier := marked_target_small R hp m
  exact m.target.pullbackHomeomorph_analytic
    ((Shrink.homeomorph m.target.carrier).symm : Shrink.{v} m.target.carrier ≃ₜ m.target.carrier)

/-- The same actual identification is biholomorphic for both native atlases. -/
theorem targetUniverseProjection_biholomorphic
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) :
    IsBiholomorphic (Marked.targetUniverseProjection R hp m :
      (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier → m.target.carrier) :=
  (analyticHomeomorph_iff_sourceBiholomorphic
    (Marked.targetUniverseTarget R hp m : Surface.{v}).riemann.toRiemannAtlas
    m.target.riemann.toRiemannAtlas (Marked.targetUniverseProjection R hp m)).mp
    (targetUniverseProjection_analytic R hp m)

/-- The actual original QC marking transported to the requested universe's
biholomorphic target; it is not an unrelated quotient representative. -/
def Marked.targetUniverseRepresentative
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) : Marked.{u, v} R where
  target := Marked.targetUniverseTarget R hp m
  marking := m.marking.trans (Marked.targetUniverseProjection R hp m).symm
  qc := s28q_isQCRS_trans m.qc
    ⟨1, (isKQCRS_one_iff (Marked.targetUniverseProjection R hp m).symm).mpr
      (targetUniverseProjection_biholomorphic R hp m).homeomorph_symm⟩

/-- Projecting the transported marking recovers the unchanged original marking. -/
theorem targetUniverseProjection_marking
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) (x : R.carrier) :
    Marked.targetUniverseProjection R hp m
      ((Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking x) = m.marking x :=
  (Marked.targetUniverseProjection R hp m).apply_symm_apply (m.marking x)

/-- Retargeting preserves the literal original lifted coefficient on all ℂ. -/
theorem targetUniverseRepresentative_liftCoeff
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, w} R) :
    s27u_liftCoeff p (Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking =
      s27u_liftCoeff p m.marking := by
  have h := liftCoeff_postcompose_biholomorphic hp.1.continuous
    (Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking.continuous
    (Marked.targetUniverseProjection R hp m) (targetUniverseProjection_biholomorphic R hp m)
  have heq : (Marked.targetUniverseProjection R hp m :
      (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier → m.target.carrier) ∘
      ((Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking :
        R.carrier → (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier) =
      (m.marking : R.carrier → m.target.carrier) := by
    funext x
    exact targetUniverseProjection_marking R hp m x
  calc
    s27u_liftCoeff p (Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking =
        s27u_liftCoeff p ((Marked.targetUniverseProjection R hp m :
          (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier → m.target.carrier) ∘
          ((Marked.targetUniverseRepresentative R hp m : Marked.{u, v} R).marking :
            R.carrier → (Marked.targetUniverseTarget R hp m : Surface.{v}).carrier)) := h.symm
    _ = s27u_liftCoeff p m.marking := congrArg (s27u_liftCoeff p) heq

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
