/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkedSpace

/-!
# Change the actual reference of a general QC-marked surface

The original given QC homeomorphism may join open or closed reference
surfaces. Every actual target is unchanged and its marking becomes f composed
with the inverse reference map. The full comparison family is unchanged on
every pair of quotient points, so the actual infimum of log K is unchanged.
The true forward and inverse maps are continuous for the topologies generated
by those actual distance balls. No compactness or metric-separation premise
is inserted, and no completeness is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces

universe u v w

variable {R : Surface.{u}} {R1 : Surface.{w}}
    (e : R.carrier ≃ₜ R1.carrier) (he : LiZhongQC.IsQCRS e)

/-- Keep the actual target and precompose its marking by the given inverse. -/
def referenceMarked (m : Marked.{u, v} R) : Marked.{w, v} R1 where
  target := m.target
  marking := e.symm.trans m.marking
  qc := LiZhongQC.s28q_isQCRS_trans (LiZhongQC.s28q_isQCRS_symm he) m.qc

/-- The new marking is literally the original f composed with e inverse. -/
theorem referenceMarked_marking (m : Marked.{u, v} R) :
    (referenceMarked e he m).marking = e.symm.trans m.marking := rfl

/-- The original transition remains compatible with the new markings. -/
theorem reference_marking_homotopy {m n : Marked.{u, v} R}
    {f : m.target.carrier ≃ₜ n.target.carrier}
    (h : ContinuousMap.Homotopic
      ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
        C(R.carrier, n.target.carrier))
      (n.marking : C(R.carrier, n.target.carrier))) :
    ContinuousMap.Homotopic
      (((referenceMarked e he m).marking.trans f : R1.carrier ≃ₜ n.target.carrier) :
        C(R1.carrier, n.target.carrier))
      (_root_.toContinuousMap
        ((referenceMarked e he n).marking : R1.carrier ≃ₜ n.target.carrier)) :=
  h.comp (ContinuousMap.Homotopic.refl (e.symm : C(R1.carrier, R.carrier)))

/-- The actual conformal marked relation is preserved. -/
theorem reference_marked_equivalent {m n : Marked.{u, v} R} (h : m.Equivalent n) :
    (referenceMarked e he m).Equivalent (referenceMarked e he n) := by
  obtain ⟨c, hc, hh⟩ := h
  exact ⟨c, hc, reference_marking_homotopy e he hh⟩

/-- Applying the actual inverse reference change cancels the two markings. -/
theorem reference_marked_symm_equivalent (m : Marked.{u, v} R) :
    (referenceMarked e.symm (LiZhongQC.s28q_isQCRS_symm he)
      (referenceMarked e he m)).Equivalent m := by
  refine ⟨Homeomorph.refl m.target.carrier, LiZhongQC.isBiholomorphic_id, ?_⟩
  have hmark :
      (((referenceMarked e.symm (LiZhongQC.s28q_isQCRS_symm he)
        (referenceMarked e he m)).marking.trans (Homeomorph.refl m.target.carrier) :
          R.carrier ≃ₜ m.target.carrier) : C(R.carrier, m.target.carrier)) =
        (m.marking : C(R.carrier, m.target.carrier)) := by
    ext x
    exact congrArg m.marking (e.symm_apply_apply x)
  rw [hmark]

/-- The actual reference change on every class of the general marked quotient. -/
def referenceMap : Space.{u, v} R → Space.{w, v} R1 :=
  Quotient.lift (fun m => mk (referenceMarked e he m))
    (fun _ _ h => Quotient.sound (reference_marked_equivalent e he h))

/-- The quotient map retains the literal given inverse-precomposed marking. -/
theorem referenceMap_mk (m : Marked.{u, v} R) :
    referenceMap e he (mk m) = mk (referenceMarked e he m) := rfl

/-- The actual inverse reference map induces an inverse on the whole quotient. -/
theorem referenceMap_symm (p : Space.{u, v} R) :
    referenceMap e.symm (LiZhongQC.s28q_isQCRS_symm he) (referenceMap e he p) = p := by
  refine Quotient.inductionOn p ?_
  intro m
  exact Quotient.sound (reference_marked_symm_equivalent e he m)

/-- A genuine bijection between the two original general marked quotients. -/
def referenceEquiv : Space.{u, v} R ≃ Space.{w, v} R1 where
  toFun := referenceMap e he
  invFun := referenceMap e.symm (LiZhongQC.s28q_isQCRS_symm he)
  left_inv := referenceMap_symm e he
  right_inv p := by
    simpa only [Homeomorph.symm_symm] using
      referenceMap_symm e.symm (LiZhongQC.s28q_isQCRS_symm he) p

/-- Every compatible transition keeps its actual map and its full log K value. -/
theorem reference_distanceFamily_subset (p q : Space.{u, v} R) :
    admissibleLogDilatations p q ⊆
      admissibleLogDilatations (referenceMap e he p) (referenceMap e he q) := by
  rintro d ⟨m, n, f, hm, hn, hf, hh, hd⟩
  refine ⟨referenceMarked e he m, referenceMarked e he n, f, ?_, ?_, hf,
    reference_marking_homotopy e he hh, hd⟩
  · exact congrArg (referenceMap e he) hm
  · exact congrArg (referenceMap e he) hn

/-- The complete actual dilatation family is identical on every pair of classes. -/
theorem reference_distanceFamily_eq (p q : Space.{u, v} R) :
    admissibleLogDilatations (referenceMap e he p) (referenceMap e he q) =
      admissibleLogDilatations p q := by
  apply subset_antisymm
  · intro d hd
    have h := reference_distanceFamily_subset e.symm (LiZhongQC.s28q_isQCRS_symm he)
      (referenceMap e he p) (referenceMap e he q) hd
    simpa only [referenceMap_symm] using h
  · exact reference_distanceFamily_subset e he p q

/-- The actual full-log infimum distance is preserved, with no chosen metric. -/
theorem reference_distance (p q : Space.{u, v} R) :
    distance (referenceMap e he p) (referenceMap e he q) = distance p q := by
  unfold distance
  rw [reference_distanceFamily_eq]

/-- The reference map is continuous for the actual distance-ball topologies. -/
theorem referenceMap_continuous :
    Continuous[distanceTopology.{u, v} R, distanceTopology.{w, v} R1]
      (referenceMap (R := R) (R1 := R1) e he : Space.{u, v} R → Space.{w, v} R1) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨q, r, rfl⟩
  let p : Space.{u, v} R := (referenceEquiv e he).symm q
  have hq : referenceMap e he p = q := (referenceEquiv e he).apply_symm_apply q
  have hpre : referenceMap e he ⁻¹' {b | distance b q < r} = {a | distance a p < r} := by
    ext a
    change distance (referenceMap e he a) q < r ↔ distance a p < r
    rw [← hq, reference_distance]
  rw [hpre]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨p, r, rfl⟩

/-- The actual forward map and actual inverse form a distance-topology homeomorphism. -/
def referenceHomeomorph :
    letI := distanceTopology.{u, v} R
    letI := distanceTopology.{w, v} R1
    Space.{u, v} R ≃ₜ Space.{w, v} R1 := by
  letI := distanceTopology.{u, v} R
  letI := distanceTopology.{w, v} R1
  exact
    { toEquiv := referenceEquiv e he
      continuous_toFun := referenceMap_continuous e he
      continuous_invFun := referenceMap_continuous e.symm (LiZhongQC.s28q_isQCRS_symm he) }

/-- The same homeomorphism preserves the actual original distance on all classes. -/
theorem referenceHomeomorph_distance (p q : Space.{u, v} R) :
    distance (referenceHomeomorph e he p) (referenceHomeomorph e he q) = distance p q :=
  reference_distance e he p q

/-- The original point [B,f] is sent to the actual identity base point of B. -/
theorem referenceMap_marked_base (A B : Surface.{u}) (f : A.carrier ≃ₜ B.carrier)
    (hf : LiZhongQC.IsQCRS f) :
    referenceMap f hf (mk ({ target := B, marking := f, qc := hf } : Marked.{u, u} A)) =
      basePoint B := by
  apply Quotient.sound
  refine ⟨Homeomorph.refl B.carrier, LiZhongQC.isBiholomorphic_id, ?_⟩
  have hmark : ((f.symm.trans f : B.carrier ≃ₜ B.carrier) : C(B.carrier, B.carrier)) =
      (Homeomorph.refl B.carrier : C(B.carrier, B.carrier)) := by
    ext x
    exact f.apply_symm_apply x
  change ContinuousMap.Homotopic
    ((f.symm.trans f : B.carrier ≃ₜ B.carrier) : C(B.carrier, B.carrier))
    (Homeomorph.refl B.carrier : C(B.carrier, B.carrier))
  rw [hmark]

/-- Any two original native Riemann surfaces, open or closed, have the genuine
inverse-precomposed reference homeomorphism preserving the whole original distance.
The target universe contains both original surfaces and their identity markings. -/
theorem original_reference_change
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannSurface X) (B : RiemannSurface Y) (f : X ≃ₜ Y)
    (hf : letI := A.toRiemannAtlas.toChartedSpace
      letI := B.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    let S := Surface.ofRiemannSurface A
    let T := Surface.ofRiemannSurface B
    letI := distanceTopology.{u, u} S
    letI := distanceTopology.{u, u} T
    ∃ H : Space.{u, u} S ≃ₜ Space.{u, u} T,
      (∀ p : Space.{u, u} S, H p = referenceMap (R := S) (R1 := T) f hf p) ∧
      ∀ p q, distance (H p) (H q) = distance p q := by
  let S := Surface.ofRiemannSurface A
  let T := Surface.ofRiemannSurface B
  let := distanceTopology.{u, u} S
  let := distanceTopology.{u, u} T
  exact ⟨referenceHomeomorph (R := S) (R1 := T) f hf, fun _ => rfl,
    fun p q => referenceHomeomorph_distance (R := S) (R1 := T) f hf p q⟩

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
