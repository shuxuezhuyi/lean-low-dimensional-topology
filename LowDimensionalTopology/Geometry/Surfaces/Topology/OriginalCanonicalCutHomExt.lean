/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalCanonicalCut
public import LowDimensionalTopology.Geometry.Surfaces.Topology.GeneratorLoopTransport

/-!
# All-class comparison from an actual canonical polygon cut

The same actual cut supplies every ordered side class and its original
fundamental-group equivalence. Its common conjugated inverse letters give
extensionality on all classes through the existing presented-group API.
The resulting common-path transport uses every one of the two sides per
handle without changing the original ordered family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces.OriginalOrientedCanonicalCut

open HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
  {g : ℕ} {hg : 0 < g} {p : X}

/-- Homomorphisms agreeing on every actual ordered side class of this same
original cut agree on its entire genuine fundamental group. -/
theorem hom_ext {H : Type} [Group H] (D : OriginalOrientedCanonicalCut R g hg p)
    (A B : FundamentalGroup X p →* H)
    (hslots : ∀ d : Fin g × Fin 2, A (D.family d) = B (D.family d)) : A = B := by
  classical
  have hcast {a b : X} (h : a = b) (l : Path a a) :
      TauCeti.FundamentalGroup.homeomorphMulEquivOfEq (Homeomorph.refl X) h
          (pathClass l) = pathClass (l.cast h.symm h.symm) := by
    subst b
    change FundamentalGroup.mapOfEq (ContinuousMap.id X)
      (show (ContinuousMap.id X) a = a from rfl) (pathClass l) = pathClass l
    exact TauCeti.FundamentalGroup.mapOfEq_id rfl (pathClass l)
  let T : FundamentalGroup X (D.polygon.symm (boundaryBase g).val) ≃*
      FundamentalGroup X p :=
    TauCeti.FundamentalGroup.homeomorphMulEquivOfEq (Homeomorph.refl X) D.basepoint_eq
  let E₀ := markedPolygonFundamentalEquiv hg D.polygon
  let E : FundamentalGroup X p ≃* LiZhongQC.surfaceGroup g := T.symm.trans E₀
  have hT (d : Fin g × Fin 2) :
      T (pathClass (markedPolygonLoop D.polygon d)) = D.family d :=
    hcast D.basepoint_eq (markedPolygonLoop D.polygon d)
  obtain ⟨c, hc⟩ := markedPolygonLoop_images_up_to_common_conjugation hg D.polygon
  have hE (d : Fin g × Fin 2) :
      E (D.family d) =
        c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹ := by
    rw [← hT d]
    change E₀ (T.symm (T (pathClass (markedPolygonLoop D.polygon d)))) = _
    rw [T.symm_apply_apply]
    exact hc d
  let K : LiZhongQC.surfaceGroup g ≃* FundamentalGroup X p :=
    (MulAut.conj c).trans E.symm
  have hK (d : Fin g × Fin 2) :
      K ((PresentedGroup.of (edgeLabelEquiv g d))⁻¹) = D.family d := by
    apply E.injective
    change E (E.symm ((MulAut.conj c) ((PresentedGroup.of (edgeLabelEquiv g d))⁻¹))) = _
    rw [E.apply_symm_apply]
    exact (hE d).symm
  have he : A.comp K.toMonoidHom = B.comp K.toMonoidHom := by
    apply PresentedGroup.ext
    intro s
    have hKs := hK ((edgeLabelEquiv g).symm s)
    rw [Equiv.apply_symm_apply] at hKs
    have hinv : (A.comp K.toMonoidHom) ((PresentedGroup.of s)⁻¹) =
        (B.comp K.toMonoidHom) ((PresentedGroup.of s)⁻¹) := by
      change A (K ((PresentedGroup.of s)⁻¹)) = B (K ((PresentedGroup.of s)⁻¹))
      rw [hKs]
      exact hslots ((edgeLabelEquiv g).symm s)
    apply inv_injective
    exact (map_inv (A.comp K.toMonoidHom)
      (PresentedGroup.of s : LiZhongQC.surfaceGroup g)).symm.trans
        (hinv.trans (map_inv (B.comp K.toMonoidHom)
          (PresentedGroup.of s : LiZhongQC.surfaceGroup g)))
  ext a
  obtain ⟨s, rfl⟩ := K.surjective a
  exact DFunLike.congr_fun he s

/-- The one supplied path that transports every ordered class of the same
actual cut transports all original fundamental-group classes. -/
theorem transport_all {Y : Type} [TopologicalSpace Y]
    (D : OriginalOrientedCanonicalCut R g hg p) (f k : C(X, Y))
    (c : Path (f p) (k p))
    (hslots : ∀ d : Fin g × Fin 2,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map f p (D.family d)) =
          FundamentalGroup.map k p (D.family d)) :
    ∀ a : FundamentalGroup X p,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c (FundamentalGroup.map f p a) =
        FundamentalGroup.map k p a := by
  let A := (FundamentalGroup.fundamentalGroupMulEquivOfPath c).toMonoidHom.comp
    (FundamentalGroup.map f p)
  let B := FundamentalGroup.map k p
  have he : A = B := D.hom_ext A B hslots
  intro a
  exact DFunLike.congr_fun he a

end LowDimensionalTopology.Geometry.Surfaces.OriginalOrientedCanonicalCut
