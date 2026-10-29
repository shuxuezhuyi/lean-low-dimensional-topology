module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGerm

/-!
# Continuity of the actual inverse Bers germ in its original weighted norms

Translation by the coefficient of the inverse normalized map is the actual
normalized pullback. The proved source Bers translation continuity therefore
applies to the literal pullback of the Ahlfors-Weill section. The faithful
weighted supremum realizes these epsilon estimates in the native target norm.
No continuity, inverse, or coordinate compatibility is supplied as a field.

The normalized-map and source continuity arguments use Wu Xiaobin's LiZhongQC
development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

variable {Γ : Subgroup GammaMeasurableBeltrami.Deck}

/-- A bound on the literal source Bers supremum is a bound in the same native norm. -/
theorem Automorphic.norm_le_of_bersNormL_le (φ : Automorphic Γ) {C : ℝ} (hC : 0 ≤ C)
    (hφ : LiZhongQC.bersNormL (φ.toSource : ℂ → ℂ) ≤ ENNReal.ofReal C) : ‖φ‖ ≤ C := by
  change ‖φ.val‖ ≤ C
  apply lp.norm_le_of_forall_le hC
  intro z
  rw [← norm_decode_mul_weight]
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  exact (le_iSup₂_of_le (z : ℂ) z.property le_rfl).trans hφ

/-- On the original coefficient ball, the entire canonical source function is retained. -/
theorem automorphicProjection_toSource_eq (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) (hμ : ‖μ‖ < 1) :
    ((automorphicProjection hΓ μ).toSource : ℂ → ℂ) =
      LiZhongQC.bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val) := by
  change decode (projection μ) = _
  rw [projection, dite_eq_left hμ, decode_projectionValue,
    GammaMeasurableBeltrami.bersProjection_eq]

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The actual source zero coefficient, with its proved strict coefficient bound. -/
def sourceZeroCoefficient : LiZhongQC.BeltramiH := ⟨0, LiZhongQC.bB_l_zero_mem⟩

theorem fMuSym_sourceZeroCoefficient :
    LiZhongQC.fMuSym sourceZeroCoefficient.val = id := by
  have hs : LiZhongQC.symmetricExtension (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [LiZhongQC.symmetricExtension, Pi.zero_apply, map_zero, ite_self]
  change LiZhongQC.normalizedSolution (LiZhongQC.symmetricExtension (0 : ℂ → ℂ)) = id
  rw [hs, LiZhongQC.bB_l_normalizedSolution_zero]

/-- The coefficient of the actual inverse normalized quasiconformal map. -/
def sourceInverseBase (ν : LiZhongQC.BeltramiH) : LiZhongQC.BeltramiH :=
  LiZhongQC.b33_t_tb ν sourceZeroCoefficient

theorem fMuSym_sourceInverseBase (ν : LiZhongQC.BeltramiH) :
    LiZhongQC.fMuSym (sourceInverseBase ν).val =
      Function.invFunOn (LiZhongQC.fMuSym ν.val) univ := by
  change LiZhongQC.fMuSym (LiZhongQC.translatedBeltrami ν.val sourceZeroCoefficient.val) = _
  rw [LiZhongQC.b33_t_tb_fMuSym, fMuSym_sourceZeroCoefficient, Function.id_comp]

theorem inverse_sourceInverseBase (ν : LiZhongQC.BeltramiH) (z : ℂ) :
    Function.invFunOn (LiZhongQC.fMuSym (sourceInverseBase ν).val) univ z =
      LiZhongQC.fMuSym ν.val z := by
  obtain ⟨_, _, hνleft, _, _⟩ := LiZhongQC.b33_t_fs_inv_spec ν
  obtain ⟨_, _, hηleft, _, _⟩ := LiZhongQC.b33_t_fs_inv_spec (sourceInverseBase ν)
  have hi : LiZhongQC.fMuSym (sourceInverseBase ν).val
      (LiZhongQC.fMuSym ν.val z) = z := by
    rw [fMuSym_sourceInverseBase, hνleft]
  have he := hηleft (LiZhongQC.fMuSym ν.val z)
  rw [hi] at he
  exact he

/-- Actual pullback Bers values are translation by the actual inverse-map coefficient. -/
theorem sourceBers_pullback_eq_inverseTranslation (ν κ : LiZhongQC.BeltramiH) :
    LiZhongQC.bersFunction (LiZhongQC.b33_t_pb ν κ).val =
      LiZhongQC.bersFunction
        (LiZhongQC.translatedBeltrami (sourceInverseBase ν).val κ.val) := by
  apply (LiZhongQC.b33_t_bf_eq_iff (LiZhongQC.b33_t_pb ν κ)
    (LiZhongQC.b33_t_tb (sourceInverseBase ν) κ)).2
  apply LiZhongQC.bg_l_forward (μ₁ := LiZhongQC.b33_t_pb ν κ)
    (μ₂ := LiZhongQC.b33_t_tb (sourceInverseBase ν) κ)
  intro x
  change LiZhongQC.fMuSym (LiZhongQC.b33_t_pb ν κ).val x =
    LiZhongQC.fMuSym
      (LiZhongQC.translatedBeltrami (sourceInverseBase ν).val κ.val) x
  rw [LiZhongQC.b33_t_pb_fMuSym, LiZhongQC.b33_t_tb_fMuSym,
    Function.comp_apply, Function.comp_apply, inverse_sourceInverseBase]

/-- The literal section as an actual native coefficient-ball element. -/
def ahlforsWeillBall {Δ : Subgroup Deck} (φ : BersWeighted.Automorphic Δ)
    (hφ : ‖φ‖ < 1 / 2) : Ball Δ :=
  ⟨BersWeighted.ahlforsWeill φ, by
    rw [Metric.mem_ball, dist_zero_right]
    exact (BersWeighted.norm_ahlforsWeill_le φ).trans_lt (by linarith)⟩

theorem ahlforsWeillBall_source {Δ : Subgroup Deck} (hΔ : LiZhongQC.IsFuchsian Δ)
    (φ : BersWeighted.Automorphic Δ) (hφ : ‖φ‖ < 1 / 2) :
    LiZhongQC.bersFunction (toSourceGamma (ahlforsWeillBall φ hφ)).val.val =
      (φ.toSource : ℂ → ℂ) := by
  have he := BersWeighted.automorphicProjection_toSource_eq hΔ
    (BersWeighted.ahlforsWeill φ) (Ball.norm_lt_one (ahlforsWeillBall φ hφ))
  rw [BersWeighted.automorphicProjection_ahlforsWeill hΔ φ hφ] at he
  exact he.symm

/-- The actual native inverse germ retains the literal normalized pullback source value. -/
theorem inverseBersGerm_source_pullback (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (hφ : ‖φ‖ < 1 / 2) :
    ((inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ) =
      LiZhongQC.bersFunction
        (LiZhongQC.b33_t_pb (toSourceGamma ν).val
          (toSourceGamma (ahlforsWeillBall φ hφ)).val).val := by
  let κB := ahlforsWeillBall φ hφ
  let σ := pulledBackSource hΓ ν κB
  have hκ : ‖(BersWeighted.ahlforsWeill φ).val‖ < 1 := by
    rw [ClosedSubmodule.norm_coe]
    exact Ball.norm_lt_one κB
  have he : gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ) =
      (fromSourceGamma σ).val := by
    apply Subtype.ext
    change pullback ν (BersWeighted.ahlforsWeill φ).val = sourceAmbient σ.val
    rw [pullback, dite_eq_left hκ]
    rfl
  change ((BersWeighted.automorphicProjection hΓ
    (gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ))).toSource : ℂ → ℂ) = _
  rw [he, BersWeighted.automorphicProjection_toSource_eq hΓ _
    (Ball.norm_lt_one (fromSourceGamma σ))]
  exact sourceBers_congr_ae (toSourceGamma (fromSourceGamma σ)) σ
    (toSourceGamma_fromSourceGamma_ae σ)

/-- The actual inverse germ is continuous on its full original weighted half-unit ball. -/
theorem continuousOn_inverseBersGerm (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ContinuousOn (inverseBersGerm hΓ ν)
      (Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (1 / 2)) := by
  intro φ hφ
  have hφn : ‖φ‖ < 1 / 2 := mem_ball_zero_iff.mp hφ
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  let κφ := (toSourceGamma (ahlforsWeillBall φ hφn)).val
  obtain ⟨δ, hδ, hcont⟩ := LiZhongQC.b33_t_tb_cont
    (sourceInverseBase (toSourceGamma ν).val) κφ (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro ψ hψ hdist
  have hψn : ‖ψ‖ < 1 / 2 := mem_ball_zero_iff.mp hψ
  let κψ := (toSourceGamma (ahlforsWeillBall ψ hψn)).val
  have hsub : ((ψ - φ).toSource : ℂ → ℂ) =
      (ψ.toSource : ℂ → ℂ) - (φ.toSource : ℂ → ℂ) := by
    exact map_sub BersWeighted.decodeLinearMap ψ.val φ.val
  have hinput : LiZhongQC.bersNormL
      (LiZhongQC.bersFunction κψ.val - LiZhongQC.bersFunction κφ.val) <
        ENNReal.ofReal δ := by
    change LiZhongQC.bersNormL
      (LiZhongQC.bersFunction (toSourceGamma (ahlforsWeillBall ψ hψn)).val.val -
        LiZhongQC.bersFunction (toSourceGamma (ahlforsWeillBall φ hφn)).val.val) < _
    rw [ahlforsWeillBall_source (deformedGroup_spec hΓ ν).1 ψ hψn,
      ahlforsWeillBall_source (deformedGroup_spec hΓ ν).1 φ hφn, ← hsub]
    apply (BersWeighted.Automorphic.bersNormL_toSource_le (ψ - φ)).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by
      simpa only [dist_eq_norm] using hdist)
  have hb := hcont κψ hinput
  have hEsφ := (inverseBersGerm_source_pullback hΓ ν φ hφn).trans
    (sourceBers_pullback_eq_inverseTranslation (toSourceGamma ν).val κφ)
  have hEsψ := (inverseBersGerm_source_pullback hΓ ν ψ hψn).trans
    (sourceBers_pullback_eq_inverseTranslation (toSourceGamma ν).val κψ)
  have houtput : LiZhongQC.bersNormL
      (((inverseBersGerm hΓ ν ψ - inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ)) ≤
        ENNReal.ofReal (ε / 2) := by
    have hs : ((inverseBersGerm hΓ ν ψ - inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ) =
        ((inverseBersGerm hΓ ν ψ).toSource : ℂ → ℂ) -
          ((inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ) :=
      map_sub BersWeighted.decodeLinearMap _ _
    rw [hs, hEsψ, hEsφ]
    exact hb.le
  rw [dist_eq_norm]
  exact (BersWeighted.Automorphic.norm_le_of_bersNormL_le _ (by linarith) houtput).trans_lt
    (by linarith)

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
