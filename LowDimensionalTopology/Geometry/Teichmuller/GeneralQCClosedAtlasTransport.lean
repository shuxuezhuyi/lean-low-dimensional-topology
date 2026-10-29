/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarkingSurjectivity

/-!
# Preserve the actual QC map when repackaging a source atlas

The old and native surfaces have identical carriers, topologies and complete
complex chart sets. Their preferred chart choices may differ. Actual identity
biholomorphisms give QC and exact maximal-dilatation transport of the same map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces
universe u v

/-- The identity from an original source target to its native round-trip atlas
is genuinely biholomorphic; equality of preferred chart choices is not assumed. -/
theorem closedTarget_identity_biholomorphic (S : LiZhongQC.ClosedRS.{v}) :
    @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace S.chartedSpace
      S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
      (id : S.carrier → S.carrier) := by
  apply (analyticHomeomorph_ofManifold_iff_sourceBiholomorphic
    (CX := S.chartedSpace) (CY := S.toNative.toRiemannAtlas.toChartedSpace)
    (MX := S.isManifold) (MY := S.toNative.toRiemannAtlas.isManifold)
    (Homeomorph.refl S.carrier)).mp
  change RiemannAnalyticMap S.toNative.toRiemannAtlas S.toNative.toRiemannAtlas
    (id : S.carrier → S.carrier)
  exact RiemannAnalyticMap.id _

/-- Repackaging the actual target preserves both QC of the same homeomorphism
and its exact maximal dilatation. All source chart instances remain explicit. -/
theorem qc_target_toNative
    {A : Type u} [TA : TopologicalSpace A] [CA : ChartedSpace ℂ A]
    [MA : IsManifold 𝓘(ℂ) ω A]
    (S : LiZhongQC.ClosedRS.{v})
    (f : @Homeomorph A S.carrier TA S.topologicalSpace)
    (hf : @LiZhongQC.IsQCRS A TA CA
      S.carrier S.topologicalSpace S.chartedSpace f) :
    @LiZhongQC.IsQCRS A TA CA
      S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace f ∧
    @LiZhongQC.maxDilatationRS A TA CA
        S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace f =
      @LiZhongQC.maxDilatationRS A TA CA
        S.carrier S.topologicalSpace S.chartedSpace f := by
  let CN := S.toNative.toRiemannAtlas.toChartedSpace
  let MN := S.toNative.toRiemannAtlas.isManifold
  have hA : @LiZhongQC.IsBiholomorphic A TA CA A TA CA (id : A → A) :=
    @LiZhongQC.isBiholomorphic_id A TA CA
  have hS := closedTarget_identity_biholomorphic S
  have hSi : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace CN
      S.carrier S.topologicalSpace S.chartedSpace (id : S.carrier → S.carrier) :=
    @LiZhongQC.IsBiholomorphic.homeomorph_symm
      S.carrier S.topologicalSpace S.chartedSpace
      S.carrier S.topologicalSpace CN (Homeomorph.refl S.carrier) hS
  have hforward := @LiZhongQC.s29_m_maxDil_conj_biholo
    A TA CA MA A TA CA MA
    S.carrier S.topologicalSpace S.chartedSpace S.isManifold
    S.carrier S.topologicalSpace CN MN
    f hf (Homeomorph.refl A) hA (Homeomorph.refl S.carrier) hS
  have hnew : @LiZhongQC.IsQCRS A TA CA S.carrier S.topologicalSpace CN f :=
    hforward.1
  have hbackward := @LiZhongQC.s29_m_maxDil_conj_biholo
    A TA CA MA A TA CA MA
    S.carrier S.topologicalSpace CN MN
    S.carrier S.topologicalSpace S.chartedSpace S.isManifold
    f hnew (Homeomorph.refl A) hA (Homeomorph.refl S.carrier) hSi
  exact ⟨hnew, le_antisymm hforward.2 hbackward.2⟩

/-- The inverse of the same actual QC homeomorphism has exactly the same
maximal dilatation, with both charted-space roles kept explicit. -/
theorem qc_symm_maxDilatation_eq
    {A : Type u} [TA : TopologicalSpace A] [CA : ChartedSpace ℂ A] [hA : Nonempty A]
    {B : Type v} [TB : TopologicalSpace B] [CB : ChartedSpace ℂ B]
    (f : @Homeomorph A B TA TB)
    (hf : @LiZhongQC.IsQCRS A TA CA B TB CB f) :
    @LiZhongQC.IsQCRS B TB CB A TA CA f.symm ∧
    @LiZhongQC.maxDilatationRS B TB CB A TA CA f.symm =
      @LiZhongQC.maxDilatationRS A TA CA B TB CB f := by
  obtain ⟨hi, hle⟩ := @LiZhongQC.s29_m_maxDil_symm_le
    A TA CA hA B TB CB f hf
  have hback := @LiZhongQC.s29_m_maxDil_symm_le
    B TB CB (Nonempty.map f hA) A TA CA f.symm hi
  refine ⟨hi, le_antisymm hle ?_⟩
  simpa only [Homeomorph.symm_symm] using hback.2

/-- Repackaging both actual closed targets preserves the original comparison
homeomorphism, its QC property and its exact maximal dilatation. -/
theorem qc_closed_toNative (S : LiZhongQC.ClosedRS.{u}) (T : LiZhongQC.ClosedRS.{v})
    (f : @Homeomorph S.carrier T.carrier S.topologicalSpace T.topologicalSpace)
    (hf : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f) :
    @LiZhongQC.IsQCRS
      S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
      T.carrier T.topologicalSpace T.toNative.toRiemannAtlas.toChartedSpace f ∧
    @LiZhongQC.maxDilatationRS
        S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
        T.carrier T.topologicalSpace T.toNative.toRiemannAtlas.toChartedSpace f =
      @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
        T.carrier T.topologicalSpace T.chartedSpace f := by
  let CS := S.toNative.toRiemannAtlas.toChartedSpace
  let MS := S.toNative.toRiemannAtlas.isManifold
  have hfi := @qc_symm_maxDilatation_eq
    S.carrier S.topologicalSpace S.chartedSpace S.connectedSpace.toNonempty
    T.carrier T.topologicalSpace T.chartedSpace f hf
  have hfirst := @qc_target_toNative
    T.carrier T.topologicalSpace T.chartedSpace T.isManifold S f.symm hfi.1
  have hreturn := @qc_symm_maxDilatation_eq
    T.carrier T.topologicalSpace T.chartedSpace T.connectedSpace.toNonempty
    S.carrier S.topologicalSpace CS f.symm hfirst.1
  have hs : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace CS
      T.carrier T.topologicalSpace T.chartedSpace f := by
    simpa only [Homeomorph.symm_symm] using hreturn.1
  have hKs : @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace CS
      T.carrier T.topologicalSpace T.chartedSpace f =
      @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
        T.carrier T.topologicalSpace T.chartedSpace f := by
    calc
      @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace CS
          T.carrier T.topologicalSpace T.chartedSpace f =
          @LiZhongQC.maxDilatationRS T.carrier T.topologicalSpace T.chartedSpace
            S.carrier S.topologicalSpace CS f.symm := by
              simpa only [Homeomorph.symm_symm] using hreturn.2
      _ = @LiZhongQC.maxDilatationRS T.carrier T.topologicalSpace T.chartedSpace
          S.carrier S.topologicalSpace S.chartedSpace f.symm := hfirst.2
      _ = @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
          T.carrier T.topologicalSpace T.chartedSpace f := hfi.2
  have hlast := @qc_target_toNative
    S.carrier S.topologicalSpace CS MS T f hs
  exact ⟨hlast.1, hlast.2.trans hKs⟩

/-- A conformal comparison is still conformal in the unchanged native chart sets. -/
theorem biholomorphic_closed_toNative (S : LiZhongQC.ClosedRS.{u})
    (T : LiZhongQC.ClosedRS.{v})
    (f : @Homeomorph S.carrier T.carrier S.topologicalSpace T.topologicalSpace)
    (hf : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f) :
    @LiZhongQC.IsBiholomorphic
      S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
      T.carrier T.topologicalSpace T.toNative.toRiemannAtlas.toChartedSpace f := by
  have h1 := (@LiZhongQC.isKQCRS_one_iff
    S.carrier S.topologicalSpace S.chartedSpace
    T.carrier T.topologicalSpace T.chartedSpace S.isManifold T.isManifold f).mpr hf
  have hq : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f := ⟨1, h1⟩
  have hK : @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f = 1 := by
    apply le_antisymm
    · simpa only [ENNReal.ofReal_one] using
        (@LiZhongQC.maxDilatationRS_le S.carrier S.topologicalSpace S.chartedSpace
          T.carrier T.topologicalSpace T.chartedSpace f 1 h1)
    · exact @LiZhongQC.s29_m_one_le_maxDilatationRS
        S.carrier S.topologicalSpace S.chartedSpace S.connectedSpace.toNonempty
        T.carrier T.topologicalSpace T.chartedSpace f hq
  have hn := qc_closed_toNative S T f hq
  have hn1 := @LiZhongQC.utm_isKQCRS_one_of_maxDil
    S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
    T.carrier T.topologicalSpace T.toNative.toRiemannAtlas.toChartedSpace f hn.1
    (hn.2.trans hK)
  exact (@LiZhongQC.isKQCRS_one_iff
    S.carrier S.topologicalSpace S.toNative.toRiemannAtlas.toChartedSpace
    T.carrier T.topologicalSpace T.toNative.toRiemannAtlas.toChartedSpace
    S.toNative.toRiemannAtlas.isManifold T.toNative.toRiemannAtlas.isManifold f).mp hn1

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
