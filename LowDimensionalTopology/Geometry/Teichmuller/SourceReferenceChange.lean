/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S29_TeichmullerMetric

/-!
# Change the actual reference surface in the existing marked quotient

The given quasiconformal homeomorphism may join different reference surfaces.
The target marked surface is unchanged; its marking is composed with the
actual inverse reference map. Homotopy compatibility, the inverse quotient
map and the entire family defining the half-log distance are preserved.

These statements use the existing source `MarkedRS` and `TeichSpace` exactly.
Their targets are bundled closed Riemann surfaces. In particular this file
does not replace the general open-surface Teichmuller space by that closed
target model, and does not assert a global Bers biholomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange

open LiZhongQC

universe u
variable {A B : Type u}
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    (e : A ≃ₜ B) (he : LiZhongQC.IsQCRS e)

/-- Keep the original target and precompose its marking by the given inverse. -/
def marked (m : LiZhongQC.MarkedRS A) : LiZhongQC.MarkedRS B where
  X := m.X
  marking := e.symm.trans m.marking
  qc := LiZhongQC.s28q_isQCRS_trans (LiZhongQC.s28q_isQCRS_symm he) m.qc

/-- The actual target transition remains in exactly the same marking homotopy class. -/
theorem marking_homotopy {m n : LiZhongQC.MarkedRS A}
    {g : m.X.carrier ≃ₜ n.X.carrier}
    (h : ContinuousMap.Homotopic
      ((m.marking.trans g : A ≃ₜ n.X.carrier) : C(A, n.X.carrier))
      (n.marking : C(A, n.X.carrier))) :
    ContinuousMap.Homotopic
      (((marked e he m).marking.trans g : B ≃ₜ n.X.carrier) : C(B, n.X.carrier))
      ((marked e he n).marking : C(B, (marked e he n).X.carrier)) := by
  exact h.comp (ContinuousMap.Homotopic.refl (e.symm : C(B, A)))

/-- The original conformal marked-target relation is preserved across references. -/
theorem marked_equiv {m n : LiZhongQC.MarkedRS A} (h : m.Equiv n) :
    (marked e he m).Equiv (marked e he n) := by
  obtain ⟨c, hc, hh⟩ := h
  exact ⟨c, hc, marking_homotopy e he hh⟩

/-- The true inverse reference change cancels, up to the original marked relation. -/
theorem marked_symm_equiv (m : LiZhongQC.MarkedRS A) :
    (marked e.symm (LiZhongQC.s28q_isQCRS_symm he) (marked e he m)).Equiv m := by
  refine ⟨Homeomorph.refl m.X.carrier, LiZhongQC.isBiholomorphic_id, ?_⟩
  have hmark :
      (((marked e.symm (LiZhongQC.s28q_isQCRS_symm he) (marked e he m)).marking.trans
        (Homeomorph.refl m.X.carrier) : A ≃ₜ m.X.carrier) : C(A, m.X.carrier)) =
        (m.marking : C(A, m.X.carrier)) := by
    ext x
    change m.marking (e.symm (e x)) = m.marking x
    rw [e.symm_apply_apply]
  rw [hmark]

/-- The actual map on the existing original marked-surface quotient. -/
def quotientMap : LiZhongQC.TeichSpace A → LiZhongQC.TeichSpace B :=
  Quot.lift (fun m => Quot.mk _ (marked e he m))
    (fun _ _ h => Quot.sound (marked_equiv e he h))

/-- Every original representative has the literal inverse-precomposed marking. -/
theorem quotientMap_mk (m : LiZhongQC.MarkedRS A) :
    quotientMap e he (Quot.mk _ m) = Quot.mk _ (marked e he m) := rfl

/-- The original quotient inverse is induced by the actual inverse homeomorphism. -/
theorem quotientMap_symm (p : LiZhongQC.TeichSpace A) :
    quotientMap e.symm (LiZhongQC.s28q_isQCRS_symm he) (quotientMap e he p) = p := by
  refine Quot.inductionOn p ?_
  intro m
  exact Quot.sound (marked_symm_equiv e he m)

/-- A genuine equivalence between different reference-surface marked quotients. -/
def quotientEquiv : LiZhongQC.TeichSpace A ≃ LiZhongQC.TeichSpace B where
  toFun := quotientMap e he
  invFun := quotientMap e.symm (LiZhongQC.s28q_isQCRS_symm he)
  left_inv := quotientMap_symm e he
  right_inv p := by
    simpa only [Homeomorph.symm_symm] using
      quotientMap_symm e.symm (LiZhongQC.s28q_isQCRS_symm he) p

/-- The inverse equivalence keeps the actual forward reference map in its formula. -/
theorem quotientEquiv_symm_apply (p : LiZhongQC.TeichSpace B) :
    (quotientEquiv e he).symm p =
      quotientMap e.symm (LiZhongQC.s28q_isQCRS_symm he) p := rfl

/-- No target transition or dilatation is altered in the distance infimum. -/
theorem distanceFamily_subset (p q : LiZhongQC.TeichSpace A) :
    LiZhongQC.s29_m_teichSet p q ⊆
      LiZhongQC.s29_m_teichSet (quotientMap e he p) (quotientMap e he q) := by
  rintro d ⟨m, n, g, hm, hn, hg, hhom, hd⟩
  refine ⟨marked e he m, marked e he n, g, ?_, ?_, hg,
    marking_homotopy e he hhom, hd⟩
  · exact congrArg (quotientMap e he) hm
  · exact congrArg (quotientMap e he) hn

/-- The entire actual transition family, and not just its infimum, is preserved. -/
theorem distanceFamily_eq (p q : LiZhongQC.TeichSpace A) :
    LiZhongQC.s29_m_teichSet (quotientMap e he p) (quotientMap e he q) =
      LiZhongQC.s29_m_teichSet p q := by
  apply subset_antisymm
  · intro d hd
    have h := distanceFamily_subset e.symm (LiZhongQC.s28q_isQCRS_symm he)
      (quotientMap e he p) (quotientMap e he q) hd
    simpa only [quotientMap_symm] using h
  · exact distanceFamily_subset e he p q

/-- The original half-log Teichmuller distance is unchanged on every pair. -/
theorem teichDistance_quotientMap (p q : LiZhongQC.TeichSpace A) :
    LiZhongQC.teichDistance (quotientMap e he p) (quotientMap e he q) =
      LiZhongQC.teichDistance p q := by
  change sInf (LiZhongQC.s29_m_teichSet (quotientMap e he p) (quotientMap e he q)) =
    sInf (LiZhongQC.s29_m_teichSet p q)
  rw [distanceFamily_eq]

end LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange
