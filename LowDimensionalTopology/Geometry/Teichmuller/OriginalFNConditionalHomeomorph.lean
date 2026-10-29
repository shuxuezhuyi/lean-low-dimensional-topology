/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNMarkedGluing
public import LowDimensionalTopology.External.LiZhongQC.LiZhongExternal.Topology.InvarianceOfDomain
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The conditional homeomorphism of the prescribed original coordinate map

The explicit geometric premises provide actual marked rigidity and actual
marked realization. The same positive-length and chosen-real-angle map is
therefore bijective. Its proved continuity and the independent Euclidean
topology of the original Fricke image give inverse continuity by the existing
invariance-of-domain theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc)

/-- The SAME prescribed positive-length and full-real-twist map is a
homeomorphism onto its whole target, conditional on the explicit actual
marked rigidity and marked gluing realization statements. The branch is any
fixed admissible continuous real branch. -/
theorem originalFNRealCoordinateMap_isHomeomorph
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
      R hg hgenus hA hAlt D₀ φ Θ) :
    IsHomeomorph (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ) := by
  classical
  let F := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  have hfull := originalFNRealCoordinateMap_analytic_and_coordinates
    R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ
  have hraw : Continuous (fun t : nativeFrickeImage hA =>
      ((fun j => ((F t).1 j : ℝ)), (F t).2)) :=
    (hfull.1.continuousOn.domRestrict).congr (fun t => dite_eq_left t.property)
  have hfirst : Continuous (fun t : nativeFrickeImage hA => (F t).1) := by
    apply continuous_pi
    intro j
    exact continuous_induced_rng.mpr ((continuous_apply j).comp hraw.fst)
  have hcont : Continuous F := by
    simpa only [Prod.eta] using hfirst.prodMk hraw.snd
  have hFi : Function.Injective F := by
    intro t u heq
    obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA t.val).mp t.property
    obtain ⟨m, rfl⟩ := Quotient.exists_rep p
    obtain ⟨q, hq⟩ := (mem_nativeFrickeImage_iff hA u.val).mp u.property
    obtain ⟨n, rfl⟩ := Quotient.exists_rep q
    have ht : t = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ := Subtype.ext hp.symm
    have hu : u = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk n),
        ⟨TeichmullerSpace.mk n, rfl⟩⟩ := Subtype.ext hq.symm
    have hcoords := heq
    rw [ht, hu] at hcoords
    obtain ⟨k, hk, hmark⟩ := hRigid hU hφ hΘ m n hcoords
    have hmn : TeichmullerSpace.mk m = TeichmullerSpace.mk n :=
      (TeichmullerSpace.mk_eq_mk_iff m n).mpr ⟨k, hk, hmark⟩
    apply Subtype.ext
    exact hp.symm.trans ((congrArg (finiteFrickeCoordinates hA) hmn).trans hq)
  have hFs : Function.Surjective F := by
    rintro ⟨lengths, angles⟩
    obtain ⟨m, N, D, transport, hlengths, hangles⟩ :=
      hRealize hU hφ hΘ lengths angles
    refine ⟨⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩, ?_⟩
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact (hfull.2 m N D transport j).1.trans (hlengths j)
    · exact hangles
  obtain ⟨J⟩ := (nativeFrickeImage_domain R hg hgenus hA hAlt).2.2.2
  let count := 3 * g - 3
  have hdim : count + count = 6 * g - 6 := by
    dsimp [count]
    omega
  let logs : (Fin count → Set.Ioi (0 : ℝ)) ≃ₜ (Fin count → ℝ) :=
    Homeomorph.piCongrRight fun _ => Real.expOrderIso.toHomeomorph.symm
  let concat : ((Fin count → ℝ) × (Fin count → ℝ)) ≃ₜ
      (Fin (count + count) → ℝ) :=
    (Homeomorph.sumPiEquivProdPi (Fin count) (Fin count) (fun _ => ℝ)).symm.trans
      (Homeomorph.piCongrLeft (Y := fun _ : Fin (count + count) => ℝ) finSumFinEquiv)
  let reindex : (Fin (count + count) → ℝ) ≃ₜ (Fin (6 * g - 6) → ℝ) :=
    Homeomorph.piCongrLeft (Y := fun _ : Fin (6 * g - 6) => ℝ) (finCongr hdim)
  let K : ((Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) × (Fin (3 * g - 3) → ℝ)) ≃ₜ
      (Fin (6 * g - 6) → ℝ) :=
    ((logs.prodCongr (Homeomorph.refl (Fin count → ℝ))).trans concat).trans reindex
  let G : (Fin (6 * g - 6) → ℝ) → (Fin (6 * g - 6) → ℝ) :=
    fun v => K (F (J.symm v))
  have hGc : Continuous G := K.continuous.comp (hcont.comp J.symm.continuous)
  have hGi : Function.Injective G := K.injective.comp (hFi.comp J.symm.injective)
  have hGo : IsOpenMap G := by
    intro U hUopen
    exact LiZhongExternal.Topology.invariance_of_domain_finiteDimensional
      G U hUopen hGc.continuousOn (fun _ _ _ _ hxy => hGi hxy)
  have hFo : IsOpenMap F := by
    have hcomp := K.symm.isOpenMap.comp (hGo.comp J.isOpenMap)
    simpa only [Function.comp_def, G, J.symm_apply_apply, K.symm_apply_apply] using hcomp
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hFi hFo).isEmbedding,
      hFs⟩

end LowDimensionalTopology.Geometry.Teichmuller
