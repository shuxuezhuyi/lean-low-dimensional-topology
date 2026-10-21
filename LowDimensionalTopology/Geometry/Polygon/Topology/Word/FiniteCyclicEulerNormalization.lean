/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEulerSplits
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEulerCanonical
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicInvariants
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

theorem p1Subdivision_eulerCharacteristic {P Q:FiniteCyclicPresentation}
    (h:P1Subdivision P Q) (hP:P.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=by
  have hQ:=h.isSurfaceValid hP
  obtain ⟨a,⟨e⟩⟩:=h
  exact (p1_eulerCharacteristic P a hP).symm.trans (signed_eulerCharacteristic e hQ)

theorem p2Subdivision_eulerCharacteristic {P Q:FiniteCyclicPresentation}
    (h:P2Subdivision P Q) (hP:P.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=by
  have hQ:=h.isSurfaceValid hP
  obtain ⟨cut,_,⟨e⟩⟩:=h
  exact (p2_eulerCharacteristic P cut hP).symm.trans (signed_eulerCharacteristic e hQ)

theorem subdivisionStep_eulerCharacteristic {P Q:FiniteCyclicPresentation}
    (h:SubdivisionStep P Q) (hP:P.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=by
  rcases h with hi|h|h
  · obtain ⟨e⟩:=hi
    exact signed_eulerCharacteristic e (e.isSurfaceValid hP)
  · exact p1Subdivision_eulerCharacteristic h hP
  · exact p2Subdivision_eulerCharacteristic h hP

theorem subdivides_eulerCharacteristic {P Q:FiniteCyclicPresentation}
    (h:Subdivides P Q) (hP:P.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=by
  induction h with
  | refl=>rfl
  | tail hPath hstep ih=>exact ih.trans (subdivisionStep_eulerCharacteristic hstep (Subdivides.isSurfaceValid hPath hP))

theorem commonSubdivision_eulerCharacteristic {P Q:FiniteCyclicPresentation}
    (h:HasCommonSubdivision P Q) (hP:P.IsSurfaceValid) (hQ:Q.IsSurfaceValid):
    eulerCharacteristic P=eulerCharacteristic Q:=by
  obtain ⟨R,hPR,hQR⟩:=h
  exact (subdivides_eulerCharacteristic hPR hP).trans (subdivides_eulerCharacteristic hQR hQ).symm

theorem normalizationStep_eulerCharacteristic {P Q:ValidPresentation} (h:NormalizationStep P Q):
    eulerCharacteristic P.presentation=eulerCharacteristic Q.presentation:=by
  cases h with
  | commonSubdivision h=>exact commonSubdivision_eulerCharacteristic h P.valid Q.valid
  | unoriented h=>
    rcases h with hf|hb
    · obtain ⟨e⟩:=hf
      exact unoriented_eulerCharacteristic e Q.valid
    · obtain ⟨e⟩:=hb
      exact (unoriented_eulerCharacteristic e P.valid).symm
  | oneSidedP2 cut _=>exact (p2_eulerCharacteristic _ cut P.valid).symm

theorem normalizationEquivalent_eulerCharacteristic {P Q:ValidPresentation} (h:NormalizationEquivalent P Q):
    eulerCharacteristic P.presentation=eulerCharacteristic Q.presentation:=by
  induction h with
  | rel _ _ h=>exact normalizationStep_eulerCharacteristic h
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ij=>exact ih.trans ij

/-- The Euler characteristic computed from genuine glued word vertices is
 preserved by the complete certified normalization, including one-sided P2. -/
theorem normalizationResult_eulerCharacteristic {P:ValidPresentation} (r:NormalizationResult P):
    eulerCharacteristic P.presentation=eulerCharacteristic r.normalForm.canonicalPresentation:=
  normalizationEquivalent_eulerCharacteristic (P:=P)
    (Q:=canonicalValidPresentation r.normalForm r.admissible) r.equivalent

/-- Actual closed coherent input has its genuine finite Euler characteristic
 determined by its sphere or closed orientable normalization endpoint. -/
theorem closed_coherent_normalizationResult_euler {P:ValidPresentation} (r:NormalizationResult P)
    (hc:IsClosed P.presentation) (ho:IsCoherentlyOrientable P.presentation):
    (r.normalForm=.sphere∧eulerCharacteristic P.presentation=2)∨
      ∃g,0<g∧r.normalForm=.orientable g 0∧eulerCharacteristic P.presentation=2-2*(g:ℤ):=by
  have he:=normalizationResult_eulerCharacteristic r
  rcases closed_coherent_normalizationResult r hc ho with hs|⟨g,hg⟩
  · refine Or.inl ⟨hs,he.trans ?_⟩
    rw [hs]
    exact sphere_eulerCharacteristic
  · have hp:0<g:=by
      have ha:=r.admissible
      rw [hg] at ha
      simp only [NormalForm.IsEvalAdmissible] at ha
      omega
    refine Or.inr ⟨g,hp,hg,he.trans ?_⟩
    rw [hg]
    exact orientableClosed_eulerCharacteristic g hp

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
