/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceRepresentatives
public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMetric
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedAtlasTransport

/-!
# The same original QC classes for a closed reference

Every target of a genuine general QC marking of a compact reference is
compact by that very homeomorphism. The source closed bundle therefore adds
no new mathematical hypothesis and keeps the target carrier, topology,
complex charts and marking unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces
universe u

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The general marked objects with this original closed reference. -/
abbrev ClosedMarked := Marked.{u, u} (Surface.ofRiemannSurface R.toRiemannSurface)

/-- Its actual general QC-marked quotient, with the original identity class. -/
abbrev ClosedSpace := Space.{u, u} (Surface.ofRiemannSurface R.toRiemannSurface)

/-- The target compactness follows from the original reference and the actual marking. -/
theorem closed_target_compact (m : ClosedMarked R) : CompactSpace m.target.carrier := by
  let : CompactSpace (Surface.ofRiemannSurface R.toRiemannSurface).carrier :=
    R.compactSpace
  exact m.marking.compactSpace

/-- Only the proved compactness is added to the unchanged target data. -/
def closedTarget (m : ClosedMarked R) : LiZhongQC.ClosedRS.{u} where
  carrier := m.target.carrier
  topologicalSpace := inferInstance
  t2Space := inferInstance
  connectedSpace := inferInstance
  compactSpace := closed_target_compact R m
  chartedSpace := inferInstance
  isManifold := inferInstance

/-- Repackage the same target and the same QC marking into the existing source bundle. -/
def toClosedMarked (m : ClosedMarked R) :
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.MarkedRS X := by
  letI := R.toRiemannAtlas.toChartedSpace
  exact { X := closedTarget R m, marking := m.marking, qc := m.qc }

/-- Both actual conformal-marking relations have exactly the same witnesses. -/
theorem toClosedMarked_equivalent_iff (m n : ClosedMarked R) :
    (letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.MarkedRS.Equiv (toClosedMarked R m) (toClosedMarked R n)) ↔
        m.Equivalent n := Iff.rfl

/-- The unchanged actual marked surface induces the source class. -/
def toClosedSource : ClosedSpace R →
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.TeichSpace X := by
  letI := R.toRiemannAtlas.toChartedSpace
  exact Quotient.lift (fun m => Quot.mk _ (toClosedMarked R m))
    (fun m n h => Quot.sound ((toClosedMarked_equivalent_iff R m n).mpr h))

/-- The source image retains its exact original representative. -/
theorem toClosedSource_mk (m : ClosedMarked R) :
    toClosedSource R (mk m) =
      (letI := R.toRiemannAtlas.toChartedSpace;
        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (toClosedMarked R m)) := rfl

/-- Repackaging cannot identify different original general marked classes. -/
theorem toClosedSource_injective : Function.Injective (toClosedSource R) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro m n h
  apply Quotient.sound
  apply (toClosedMarked_equivalent_iff R m n).mp
  exact (LiZhongQC.markedRS_equiv_equivalence (S₀ := X)).eqvGen_iff.mp
    (Quot.eqvGen_exact h)

/-- Read the same original source target in its unchanged native chart set. -/
def fromClosedMarked :
    (letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.MarkedRS X) → ClosedMarked R := by
  letI := R.toRiemannAtlas.toChartedSpace
  intro m
  exact
    { target := Surface.ofRiemannSurface m.X.toNative.toRiemannSurface
      marking := m.marking
      qc := (qc_target_toNative (CA := R.toRiemannAtlas.toChartedSpace)
        (MA := R.toRiemannAtlas.isManifold) m.X m.marking m.qc).1 }

/-- The unchanged marking is conformally equivalent to its original source representative. -/
theorem toClosedMarked_fromClosedMarked_equivalent :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ m : LiZhongQC.MarkedRS X,
      LiZhongQC.MarkedRS.Equiv (toClosedMarked R (fromClosedMarked R m)) m := by
  let := R.toRiemannAtlas.toChartedSpace
  intro m
  refine ⟨Homeomorph.refl m.X.carrier, ?_, ContinuousMap.Homotopic.refl _⟩
  exact @LiZhongQC.IsBiholomorphic.homeomorph_symm
    m.X.carrier m.X.topologicalSpace m.X.chartedSpace
    m.X.carrier m.X.topologicalSpace m.X.toNative.toRiemannAtlas.toChartedSpace
    (Homeomorph.refl m.X.carrier) (closedTarget_identity_biholomorphic m.X)

/-- Actual conformal-marking witnesses also transport from old source targets to native ones. -/
theorem fromClosedMarked_equivalent :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ m n : LiZhongQC.MarkedRS X, m.Equiv n →
      (fromClosedMarked R m).Equivalent (fromClosedMarked R n) := by
  let := R.toRiemannAtlas.toChartedSpace
  rintro m n ⟨f, hf, hh⟩
  exact ⟨f, biholomorphic_closed_toNative m.X n.X f hf, hh⟩

/-- Both directions recover exactly the same original conformal-homotopy relation. -/
theorem fromClosedMarked_equivalent_iff :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ m n : LiZhongQC.MarkedRS X,
      (fromClosedMarked R m).Equivalent (fromClosedMarked R n) ↔ m.Equiv n := by
  let := R.toRiemannAtlas.toChartedSpace
  intro m n
  constructor
  · intro h
    have hmn := (toClosedMarked_equivalent_iff R
      (fromClosedMarked R m) (fromClosedMarked R n)).mpr h
    have he := LiZhongQC.markedRS_equiv_equivalence (S₀ := X)
    exact he.trans (he.symm (toClosedMarked_fromClosedMarked_equivalent R m))
      (he.trans hmn (toClosedMarked_fromClosedMarked_equivalent R n))
  · exact fromClosedMarked_equivalent R m n

/-- Every existing QC class has a genuine general marking on the same carrier and marking map. -/
theorem toClosedSource_surjective :
    letI := R.toRiemannAtlas.toChartedSpace
    Function.Surjective (toClosedSource R) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p
  refine Quot.inductionOn p ?_
  intro m
  exact ⟨mk (fromClosedMarked R m),
    Quot.sound (toClosedMarked_fromClosedMarked_equivalent R m)⟩

/-- The actual general QC quotient and the existing closed-source quotient coincide. -/
def closedSourceEquiv : ClosedSpace R ≃
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.TeichSpace X := by
  letI := R.toRiemannAtlas.toChartedSpace
  exact Equiv.ofBijective (toClosedSource R)
    ⟨toClosedSource_injective R, toClosedSource_surjective R⟩

/-- The equivalence is the actual unchanged-target map on every original class. -/
theorem closedSourceEquiv_apply (p : ClosedSpace R) :
    closedSourceEquiv R p = toClosedSource R p := rfl

/-- The complete full-log comparison families are identical on every pair. -/
theorem admissibleLogDilatations_closedSource (p q : ClosedSpace R) :
    letI := R.toRiemannAtlas.toChartedSpace
    admissibleLogDilatations p q = QCBookMetric.admissibleLogDilatations
      (toClosedSource R p) (toClosedSource R q) := by
  let := R.toRiemannAtlas.toChartedSpace
  ext d
  constructor
  · rintro ⟨m, n, f, hm, hn, hf, hh, hd⟩
    exact ⟨toClosedMarked R m, toClosedMarked R n, f,
      congrArg (toClosedSource R) hm, congrArg (toClosedSource R) hn, hf, hh, hd⟩
  · rintro ⟨m, n, f, hm, hn, hf, hh, hd⟩
    let M : ClosedMarked R := fromClosedMarked R m
    let N : ClosedMarked R := fromClosedMarked R n
    have hM : toClosedSource R (mk M) = Quot.mk _ m :=
      Quot.sound (toClosedMarked_fromClosedMarked_equivalent R m)
    have hN : toClosedSource R (mk N) = Quot.mk _ n :=
      Quot.sound (toClosedMarked_fromClosedMarked_equivalent R n)
    have hnativ := qc_closed_toNative m.X n.X f hf
    refine ⟨M, N, f, toClosedSource_injective R (hM.trans hm),
      toClosedSource_injective R (hN.trans hn), hnativ.1, hh, ?_⟩
    change d = Real.log
      (@LiZhongQC.maxDilatationRS
        m.X.carrier m.X.topologicalSpace m.X.toNative.toRiemannAtlas.toChartedSpace
        n.X.carrier n.X.topologicalSpace n.X.toNative.toRiemannAtlas.toChartedSpace f).toReal
    exact hd.trans
      (congrArg (fun K : ENNReal => Real.log K.toReal) hnativ.2.symm)

/-- The original general full-log distance is exactly the existing source full-log distance. -/
theorem distance_eq_source_bookDistance (p q : ClosedSpace R) :
    letI := R.toRiemannAtlas.toChartedSpace
    distance p q = QCBookMetric.bookDistance (toClosedSource R p) (toClosedSource R q) := by
  let := R.toRiemannAtlas.toChartedSpace
  change sInf (admissibleLogDilatations p q) =
    sInf (QCBookMetric.admissibleLogDilatations (toClosedSource R p) (toClosedSource R q))
  rw [admissibleLogDilatations_closedSource]

/-- The source's half-log convention accounts for precisely the factor two. -/
theorem distance_eq_two_mul_source (p q : ClosedSpace R) :
    letI := R.toRiemannAtlas.toChartedSpace
    distance p q = 2 * LiZhongQC.teichDistance (toClosedSource R p) (toClosedSource R q) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  rw [distance_eq_source_bookDistance, QCBookMetric.bookDistance_eq_two_mul]

/-- The genuine closed-source equivalence preserves the complete original normalization. -/
theorem closedSourceEquiv_distance (p q : ClosedSpace R) :
    letI := R.toRiemannAtlas.toChartedSpace
    distance p q = 2 * LiZhongQC.teichDistance
      (closedSourceEquiv R p) (closedSourceEquiv R q) :=
  distance_eq_two_mul_source R p q

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
