module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceRepresentatives

/-!
# The original quasiconformal comparison maps

The family consists of actual target homeomorphisms homotopic to the second
marking composed with the inverse first marking. Its log-dilatation image
is exactly the family already used by the original full-log distance.
The QC and dilatation APIs are credited to Wu Xiaobin's
Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

universe u v

/-- All actual QC target maps in the original relative marking homotopy class. -/
def comparisonFamily {R : Surface.{u}} (m n : Marked.{u, v} R) :
    Set (m.target.carrier ≃ₜ n.target.carrier) :=
  {f | LiZhongQC.IsQCRS f ∧ ContinuousMap.Homotopic
    (f : C(m.target.carrier, n.target.carrier))
    ((m.marking.symm.trans n.marking : m.target.carrier ≃ₜ n.target.carrier) :
      C(m.target.carrier, n.target.carrier))}

/-- Cancelling the original first marking gives the existing compatibility condition. -/
theorem mem_comparisonFamily_iff {R : Surface.{u}} (m n : Marked.{u, v} R)
    (f : m.target.carrier ≃ₜ n.target.carrier) :
    f ∈ comparisonFamily m n ↔ LiZhongQC.IsQCRS f ∧ ContinuousMap.Homotopic
      ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
        C(R.carrier, n.target.carrier)) (n.marking : C(R.carrier, n.target.carrier)) := by
  constructor
  · rintro ⟨hf, hh⟩
    refine ⟨hf, ?_⟩
    have h := hh.comp (ContinuousMap.Homotopic.refl (m.marking :
      C(R.carrier, m.target.carrier)))
    have hcancel :
        (((m.marking.symm.trans n.marking : m.target.carrier ≃ₜ n.target.carrier) :
          C(m.target.carrier, n.target.carrier)).comp
          (m.marking : C(R.carrier, m.target.carrier))) = n.marking := by
      ext x
      exact congrArg n.marking (m.marking.symm_apply_apply x)
    rw [hcancel] at h
    simpa only [LiZhongQC.coe_homeomorph_trans] using h
  · rintro ⟨hf, hh⟩
    refine ⟨hf, ?_⟩
    have h := hh.comp (ContinuousMap.Homotopic.refl (m.marking.symm :
      C(m.target.carrier, R.carrier)))
    have hcancel :
        (((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
          C(R.carrier, n.target.carrier)).comp
          (m.marking.symm : C(m.target.carrier, R.carrier))) = f := by
      ext x
      exact congrArg f (m.marking.apply_symm_apply x)
    rw [hcancel] at h
    simpa only [LiZhongQC.coe_homeomorph_trans] using h

/-- The actual relative marking itself belongs to the comparison family. -/
theorem comparisonFamily_nonempty {R : Surface.{u}} (m n : Marked.{u, v} R) :
    (comparisonFamily m n).Nonempty :=
  ⟨m.marking.symm.trans n.marking,
    LiZhongQC.s28q_isQCRS_trans (LiZhongQC.s28q_isQCRS_symm m.qc) n.qc,
    ContinuousMap.Homotopic.refl _⟩

/-- The existing distance family is precisely the log-K image of these actual maps. -/
theorem fixedLogDilatations_eq_image_comparisonFamily {R : Surface.{u}}
    (m n : Marked.{u, v} R) :
    fixedLogDilatations m n =
      (fun f : m.target.carrier ≃ₜ n.target.carrier =>
        Real.log (LiZhongQC.maxDilatationRS f).toReal) '' comparisonFamily m n := by
  ext d
  constructor
  · rintro ⟨f, hf, hh, hd⟩
    exact ⟨f, (mem_comparisonFamily_iff m n f).mpr ⟨hf, hh⟩, hd.symm⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨hqc, hh⟩ := (mem_comparisonFamily_iff m n f).mp hf
    exact ⟨f, hqc, hh, rfl⟩

/-- The original distance is the literal source infimum over the comparison maps. -/
theorem distance_eq_comparisonFamily_inf {R : Surface.{u}} (m n : Marked.{u, v} R) :
    distance (mk m) (mk n) = sInf
      ((fun f : m.target.carrier ≃ₜ n.target.carrier =>
        Real.log (LiZhongQC.maxDilatationRS f).toReal) '' comparisonFamily m n) := by
  rw [distance_eq_fixed_inf, fixedLogDilatations_eq_image_comparisonFamily]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
