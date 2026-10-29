module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflection
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceTopology

/-!
# The original marked reflection is an involutive distance homeomorphism

The two explicit chart conjugations cancel. Native chart choices are compared
by the existing identity biholomorphisms. The same actual target transitions
and their maximal dilatations identify the original full-log distance families.
No complex regularity of the induced Teichmüller map is asserted here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped ENNReal Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces

/-- Conjugating the same explicit chart twice returns all its original data. -/
theorem originalReflectedChart_twice {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y ℂ) :
    originalReflectedChart (originalReflectedChart e) = e := by
  apply OpenPartialHomeomorph.ext
  · intro x
    exact Complex.conj_conj (e x)
  · intro z
    change e.symm (conj (conj z)) = e.symm z
    rw [Complex.conj_conj]
  · rfl

/-- The two explicit conjugations recover the original atlas and preferred charts. -/
theorem originalMirrorChartedSpace_twice (S : LiZhongQC.ClosedRS.{0}) :
    originalMirrorChartedSpace (originalMirrorClosedRS S) = S.chartedSpace := by
  apply ChartedSpace.ext
  · change originalReflectedChart '' (originalReflectedChart '' S.chartedSpace.atlas) =
      S.chartedSpace.atlas
    ext e
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      simpa only [originalReflectedChart_twice] using hf
    · intro he
      exact ⟨originalReflectedChart e, ⟨e, he, rfl⟩, originalReflectedChart_twice e⟩
  · funext x
    exact originalReflectedChart_twice (S.chartedSpace.chartAt x)

/-- The same actual map has the same QC constant in the two explicit mirrors. -/
theorem originalMirror_isKQCRS_iff (S T : LiZhongQC.ClosedRS.{0})
    (f : S.carrier ≃ₜ T.carrier) (K : ℝ) :
    @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f K ↔
    @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f K := by
  constructor
  · intro hf
    have h := originalMirror_isKQCRS
      (originalMirrorClosedRS S) (originalMirrorClosedRS T) f K hf
    change @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace
      (originalMirrorChartedSpace (originalMirrorClosedRS S))
      T.carrier T.topologicalSpace
      (originalMirrorChartedSpace (originalMirrorClosedRS T)) f K at h
    rw [originalMirrorChartedSpace_twice S, originalMirrorChartedSpace_twice T] at h
    exact h
  · exact originalMirror_isKQCRS S T f K

/-- Mirroring preserves the exact maximal dilatation of this actual QC map. -/
theorem originalMirror_qc_maxDilatation_eq (S T : LiZhongQC.ClosedRS.{0})
    (f : S.carrier ≃ₜ T.carrier)
    (hf : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f) :
    @LiZhongQC.IsQCRS S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f ∧
    @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f =
    @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f := by
  have hm := originalMirror_isQCRS S T f hf
  have hK := @LiZhongQC.s29_m_isKQCRS_maxDil
    S.carrier S.topologicalSpace S.chartedSpace S.connectedSpace.toNonempty
    T.carrier T.topologicalSpace T.chartedSpace f hf
  have hKm := @LiZhongQC.s29_m_isKQCRS_maxDil
    S.carrier S.topologicalSpace (originalMirrorChartedSpace S) S.connectedSpace.toNonempty
    T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f hm
  have hle := @LiZhongQC.maxDilatationRS_le
    S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
    T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f _
    (originalMirror_isKQCRS S T f _ hK)
  have hge := @LiZhongQC.maxDilatationRS_le
    S.carrier S.topologicalSpace S.chartedSpace
    T.carrier T.topologicalSpace T.chartedSpace f _
    ((originalMirror_isKQCRS_iff S T f _).mp hKm)
  rw [ENNReal.ofReal_toReal (@LiZhongQC.s29_m_maxDilatationRS_ne_top
    S.carrier S.topologicalSpace S.chartedSpace
    T.carrier T.topologicalSpace T.chartedSpace f hf)] at hle
  rw [ENNReal.ofReal_toReal (@LiZhongQC.s29_m_maxDilatationRS_ne_top
    S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
    T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f hm)] at hge
  exact ⟨hm, le_antisymm hle hge⟩

/-- Passing to the native mirror atlases retains the same map and exact K. -/
theorem originalMirror_native_qc_maxDilatation_eq (S T : LiZhongQC.ClosedRS.{0})
    (f : S.carrier ≃ₜ T.carrier)
    (hf : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f) :
    @LiZhongQC.IsQCRS S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace
      T.carrier T.topologicalSpace (originalMirrorNative T).toRiemannAtlas.toChartedSpace f ∧
    @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace
      T.carrier T.topologicalSpace (originalMirrorNative T).toRiemannAtlas.toChartedSpace f =
    @LiZhongQC.maxDilatationRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f := by
  have hm := originalMirror_qc_maxDilatation_eq S T f hf
  have hn := qc_closed_toNative (originalMirrorClosedRS S)
    (originalMirrorClosedRS T) f hm.1
  exact ⟨hn.1, hn.2.trans hm.2⟩

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)

/-- Double reflection is equivalent to the same original marked target. -/
theorem originalReflectedClosedMarked_twice_equivalent (m : ClosedMarked R) :
    (originalReflectedClosedMarked R J hJ
      (originalReflectedClosedMarked R J hJ m)).Equivalent m := by
  let S := closedTarget R m
  let T := closedTarget R (originalReflectedClosedMarked R J hJ m)
  have hi : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace
      (originalMirrorChartedSpace S) S.carrier S.topologicalSpace T.chartedSpace
      (id : S.carrier → S.carrier) :=
    closedTarget_identity_biholomorphic (originalMirrorClosedRS S)
  have hmi := originalMirror_isBiholomorphic (originalMirrorClosedRS S) T
    (Homeomorph.refl S.carrier) hi
  have hforward : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace S.chartedSpace
      S.carrier S.topologicalSpace (originalMirrorChartedSpace T)
      (id : S.carrier → S.carrier) := by
    change @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace
      (originalMirrorChartedSpace (originalMirrorClosedRS S))
      S.carrier S.topologicalSpace (originalMirrorChartedSpace T)
      (id : S.carrier → S.carrier) at hmi
    rw [originalMirrorChartedSpace_twice S] at hmi
    exact hmi
  have hback := @LiZhongQC.IsBiholomorphic.homeomorph_symm
    S.carrier S.topologicalSpace S.chartedSpace
    S.carrier S.topologicalSpace (originalMirrorChartedSpace T)
    (Homeomorph.refl S.carrier) hforward
  have hnative := @LiZhongQC.IsBiholomorphic.homeomorph_symm
    S.carrier S.topologicalSpace (originalMirrorChartedSpace T)
    S.carrier S.topologicalSpace (originalMirrorNative T).toRiemannAtlas.toChartedSpace
    (Homeomorph.refl S.carrier)
    (closedTarget_identity_biholomorphic (originalMirrorClosedRS T))
  have hc : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace
      (originalMirrorNative T).toRiemannAtlas.toChartedSpace
      S.carrier S.topologicalSpace S.chartedSpace (id : S.carrier → S.carrier) :=
    @LiZhongQC.IsBiholomorphic.comp
      S.carrier S.topologicalSpace (originalMirrorNative T).toRiemannAtlas.toChartedSpace
      S.carrier S.topologicalSpace (originalMirrorChartedSpace T)
      S.carrier S.topologicalSpace S.chartedSpace
      (id : S.carrier → S.carrier) (id : S.carrier → S.carrier) hback hnative
  refine ⟨Homeomorph.refl m.target.carrier, hc, ?_⟩
  let f : C(X, m.target.carrier) :=
    ⟨fun x => m.marking (J (J x)),
      m.marking.continuous.comp (J.continuous.comp J.continuous)⟩
  let g : C(X, m.target.carrier) := ⟨m.marking, m.marking.continuous⟩
  change ContinuousMap.Homotopic f g
  have hmark : f = g := by
    ext x
    change m.marking (J (J x)) = m.marking x
    rw [hJ.1 x]
  exact hmark.symm ▸ ContinuousMap.Homotopic.refl g

/-- The induced map on the original QC quotient is genuinely an involution. -/
theorem originalTeichmullerReflection_involutive :
    Function.Involutive (originalTeichmullerReflection R J hJ) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro m
  exact Quotient.sound (originalReflectedClosedMarked_twice_equivalent R J hJ m)

/-- The actual original identity class is fixed by the same reflection. -/
theorem originalTeichmullerReflection_basePoint :
    originalTeichmullerReflection R J hJ
      (basePoint (Surface.ofRiemannSurface R.toRiemannSurface)) =
      basePoint (Surface.ofRiemannSurface R.toRiemannSurface) := by
  let m : ClosedMarked R :=
    { target := Surface.ofRiemannSurface R.toRiemannSurface
      marking := Homeomorph.refl X
      qc := LiZhongQC.isQCRS_refl }
  let S := closedTarget R m
  have hK := originalInvolution_isKQCRS_toMirror S J hJ
  have hb := (@LiZhongQC.isKQCRS_one_iff X inferInstance S.chartedSpace
    X inferInstance (originalMirrorChartedSpace S)
    S.isManifold (originalMirror_isManifold S) J).mp hK
  have hnative : @LiZhongQC.IsBiholomorphic X inferInstance S.chartedSpace
      X inferInstance (originalMirrorNative S).toRiemannAtlas.toChartedSpace J :=
    @LiZhongQC.IsBiholomorphic.comp
      X inferInstance S.chartedSpace
      X inferInstance (originalMirrorChartedSpace S)
      X inferInstance (originalMirrorNative S).toRiemannAtlas.toChartedSpace
      (J : X → X) (id : X → X)
      (closedTarget_identity_biholomorphic (originalMirrorClosedRS S)) hb
  have hc := @LiZhongQC.IsBiholomorphic.homeomorph_symm
    X inferInstance S.chartedSpace
    X inferInstance (originalMirrorNative S).toRiemannAtlas.toChartedSpace J hnative
  change mk (originalReflectedClosedMarked R J hJ m) = mk m
  apply Quotient.sound
  refine ⟨J.symm, hc, ?_⟩
  let f : C(X, X) := ⟨fun x => J.symm (J x), J.symm.continuous.comp J.continuous⟩
  let g : C(X, X) := ⟨id, continuous_id⟩
  change ContinuousMap.Homotopic f g
  have hmark : f = g := by
    ext x
    exact J.symm_apply_apply x
  exact hmark.symm ▸ ContinuousMap.Homotopic.refl g

/-- Each original transition supplies the identical full-log value after reflection. -/
theorem originalReflection_dilatations_subset (p q : ClosedSpace R) :
    admissibleLogDilatations p q ⊆ admissibleLogDilatations
      (originalTeichmullerReflection R J hJ p) (originalTeichmullerReflection R J hJ q) := by
  rintro d ⟨m, n, f, hm, hn, hf, hh, hd⟩
  have hnative := originalMirror_native_qc_maxDilatation_eq
    (closedTarget R m) (closedTarget R n) f hf
  refine ⟨originalReflectedClosedMarked R J hJ m,
    originalReflectedClosedMarked R J hJ n, f,
    congrArg (originalTeichmullerReflection R J hJ) hm,
    congrArg (originalTeichmullerReflection R J hJ) hn, hnative.1, ?_, ?_⟩
  · exact hh.comp (ContinuousMap.Homotopic.refl (⟨J, J.continuous⟩ : C(X, X)))
  · exact hd.trans (congrArg (fun K : ENNReal => Real.log K.toReal) hnative.2.symm)

/-- The entire actual admissible-dilatation sets agree on every pair of classes. -/
theorem originalReflection_dilatations_eq (p q : ClosedSpace R) :
    admissibleLogDilatations
      (originalTeichmullerReflection R J hJ p) (originalTeichmullerReflection R J hJ q) =
      admissibleLogDilatations p q := by
  apply subset_antisymm
  · intro d hd
    have h := originalReflection_dilatations_subset R J hJ
      (originalTeichmullerReflection R J hJ p) (originalTeichmullerReflection R J hJ q) hd
    simpa only [originalTeichmullerReflection_involutive R J hJ p,
      originalTeichmullerReflection_involutive R J hJ q] using h
  · exact originalReflection_dilatations_subset R J hJ p q

/-- The original full-log distance is preserved without replacing its topology. -/
theorem originalTeichmullerReflection_distance (p q : ClosedSpace R) :
    distance (originalTeichmullerReflection R J hJ p)
      (originalTeichmullerReflection R J hJ q) = distance p q := by
  unfold distance
  rw [originalReflection_dilatations_eq R J hJ]

/-- Continuity is for the original distance-ball topology on the original QC quotient. -/
theorem originalTeichmullerReflection_continuous :
    @Continuous (ClosedSpace R) (ClosedSpace R)
      (distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface))
      (distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface))
      (originalTeichmullerReflection R J hJ) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨q, r, rfl⟩
  let p := originalTeichmullerReflection R J hJ q
  have hq : originalTeichmullerReflection R J hJ p = q :=
    originalTeichmullerReflection_involutive R J hJ q
  have hpre : originalTeichmullerReflection R J hJ ⁻¹' {b | distance b q < r} =
      {a | distance a p < r} := by
    ext a
    change distance (originalTeichmullerReflection R J hJ a) q < r ↔ distance a p < r
    rw [← hq, originalTeichmullerReflection_distance R J hJ]
  rw [hpre]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨p, r, rfl⟩

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
