module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMetric
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The full quasiconformal modular group on the original marked quotient

All actual quasiconformal self-homeomorphisms form a subgroup. Those freely
homotopic to the identity form a normal subgroup. The quotient acts on the
existing closed-target marked quotient by inverse precomposition, with the
literal reference-change map on every representative. Both the original
half-log distance and the full-log book metric are preserved.

The final consumer uses the inherited atlas and actual genus of the original
closed Riemann surface. This file supplies the group, quotient action and
metric part; global complex analyticity is assembled separately from the
actual reference-change coordinate diagram. It makes no comparison with the
Teichmuller space of general open reference surfaces.

The marked-surface and quasiconformal APIs are reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular

open LiZhongQC

universe u
variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]

/-- The subgroup of all actual quasiconformal self-homeomorphisms. -/
def quasiconformalAutSubgroup : Subgroup (X ≃ₜ X) where
  carrier := {e | IsQCRS e}
  one_mem' := isQCRS_refl
  mul_mem' hf hg := s28q_isQCRS_trans hg hf
  inv_mem' hf := s28q_isQCRS_symm hf

/-- Actual quasiconformal automorphisms, with composition as multiplication. -/
abbrev Aut := quasiconformalAutSubgroup X

variable {X}

/-- The actual continuous self-map underlying the given QC automorphism. -/
def continuousMap (f : Aut X) : C(X, X) := _root_.toContinuousMap f.val

@[simp] theorem continuousMap_one :
    continuousMap (1 : Aut X) = ContinuousMap.id X := rfl

@[simp] theorem continuousMap_mul (f g : Aut X) :
    continuousMap (f * g) = (continuousMap f).comp (continuousMap g) := rfl

@[simp] theorem continuousMap_inv (f : Aut X) :
    continuousMap f⁻¹ = _root_.toContinuousMap f.val.symm := rfl

variable (X)

/-- The actual QC automorphisms freely homotopic to the identity. -/
def homotopyIdentitySubgroup : Subgroup (Aut X) where
  carrier := {f | ContinuousMap.Homotopic (continuousMap f) (ContinuousMap.id X)}
  one_mem' := ContinuousMap.Homotopic.refl (ContinuousMap.id X)
  mul_mem' hf hg := hf.comp hg
  inv_mem' := by
    intro f hf
    have hc := (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap f.val.symm)).comp hf
    have hcancel : (_root_.toContinuousMap f.val.symm).comp (continuousMap f) =
        ContinuousMap.id X := by
      ext x
      exact f.val.symm_apply_apply x
    rw [hcancel] at hc
    exact hc.symm

instance : (homotopyIdentitySubgroup X).Normal where
  conj_mem := by
    intro n hn g
    change ContinuousMap.Homotopic (continuousMap n) (ContinuousMap.id X) at hn
    have hc := (ContinuousMap.Homotopic.refl (continuousMap g)).comp
      (hn.comp (ContinuousMap.Homotopic.refl (_root_.toContinuousMap g.val.symm)))
    have hcancel : (continuousMap g).comp
        ((ContinuousMap.id X).comp (_root_.toContinuousMap g.val.symm)) =
        ContinuousMap.id X := by
      ext x
      exact g.val.apply_symm_apply x
    rw [hcancel] at hc
    exact hc

/-- The actual reference-change permutation attached to every QC self-map. -/
def autRepresentation : Aut X →* Equiv.Perm (TeichSpace X) where
  toFun f := SourceReferenceChange.quotientEquiv f.val f.property
  map_one' := by
    apply Equiv.ext
    intro p
    change SourceReferenceChange.quotientMap (Homeomorph.refl X) isQCRS_refl p = p
    refine Quot.inductionOn p ?_
    intro m
    refine Quot.sound ⟨Homeomorph.refl m.X.carrier, isBiholomorphic_id, ?_⟩
    exact ContinuousMap.Homotopic.refl (m.marking : C(X, m.X.carrier))
  map_mul' f g := by
    apply Equiv.ext
    intro p
    change SourceReferenceChange.quotientMap (f.val * g.val)
        (s28q_isQCRS_trans g.property f.property) p =
      SourceReferenceChange.quotientMap f.val f.property
        (SourceReferenceChange.quotientMap g.val g.property p)
    refine Quot.inductionOn p ?_
    intro m
    refine Quot.sound ⟨Homeomorph.refl m.X.carrier, isBiholomorphic_id, ?_⟩
    exact ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap (SourceReferenceChange.marked (f.val * g.val)
        (s28q_isQCRS_trans g.property f.property) m).marking)

/-- Freely null-homotopic QC reference changes act trivially. -/
theorem homotopyIdentity_le_actionKer :
    homotopyIdentitySubgroup X ≤ (autRepresentation X).ker := by
  intro f hf
  change autRepresentation X f = 1
  apply Equiv.ext
  intro p
  change SourceReferenceChange.quotientMap f.val f.property p = p
  have hinv := (homotopyIdentitySubgroup X).inv_mem hf
  change ContinuousMap.Homotopic (_root_.toContinuousMap f.val.symm)
    (ContinuousMap.id X) at hinv
  refine Quot.inductionOn p ?_
  intro m
  refine Quot.sound ⟨Homeomorph.refl m.X.carrier, isBiholomorphic_id, ?_⟩
  exact (ContinuousMap.Homotopic.refl (m.marking : C(X, m.X.carrier))).comp hinv

/-- The full QC mapping class group, using the actual homotopy-identity subgroup. -/
abbrev ModularGroup := Aut X ⧸ homotopyIdentitySubgroup X

variable {X}

/-- The modular class of the original QC automorphism. -/
def mk (f : Aut X) : ModularGroup X := QuotientGroup.mk f

/-- Equality of these modular classes is exactly free homotopy. -/
theorem mk_eq_mk_iff_homotopic (f g : Aut X) :
    mk f = mk g ↔ ContinuousMap.Homotopic (continuousMap f) (continuousMap g) := by
  constructor
  · intro h
    have hrel := QuotientGroup.eq_iff_div_mem.mp h
    change ContinuousMap.Homotopic (continuousMap (f / g)) (ContinuousMap.id X) at hrel
    have hc := hrel.comp (ContinuousMap.Homotopic.refl (continuousMap g))
    have hcancel : (continuousMap (f / g)).comp (continuousMap g) = continuousMap f := by
      ext x
      change f.val (g.val.symm (g.val x)) = f.val x
      rw [g.val.symm_apply_apply]
    rw [hcancel] at hc
    exact hc
  · intro h
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ContinuousMap.Homotopic (continuousMap (f / g)) (ContinuousMap.id X)
    have hc := h.comp (ContinuousMap.Homotopic.refl (_root_.toContinuousMap g.val.symm))
    have hcancel : (continuousMap g).comp (_root_.toContinuousMap g.val.symm) =
        ContinuousMap.id X := by
      ext x
      exact g.val.apply_symm_apply x
    rw [hcancel] at hc
    exact hc

variable (X)

/-- The permutation representation of the full original QC quotient group. -/
def representation : ModularGroup X →* Equiv.Perm (TeichSpace X) :=
  QuotientGroup.lift (homotopyIdentitySubgroup X) (autRepresentation X)
    (homotopyIdentity_le_actionKer X)

/-- The actual full QC mapping class group acts on the existing marked quotient. -/
instance : MulAction (ModularGroup X) (TeichSpace X) :=
  MulAction.compHom (TeichSpace X) (representation X)

variable {X}

/-- The modular transformation is literally inverse precomposition by its representative. -/
@[simp] theorem mk_smul (f : Aut X) (p : TeichSpace X) :
    mk f • p = SourceReferenceChange.quotientMap f.val f.property p := rfl

/-- The original class action on every marked representative keeps its actual target. -/
theorem mk_smul_mk (f : Aut X) (m : MarkedRS X) :
    HSMul.hSMul (α := ModularGroup X) (β := TeichSpace X) (γ := TeichSpace X)
      (mk f) (Quot.mk _ m) =
      (Quot.mk _ (SourceReferenceChange.marked f.val f.property m) : TeichSpace X) := rfl

/-- The source modular relation uses direct precomposition, so its representative
is the actual inverse of the book's left-action representative. -/
def inverseSourceModTransform (f : Aut X) : ModTransform X :=
  ⟨f.val.symm, s28q_isOrientationPreservingRS_of_isQCRS (s28q_isQCRS_symm f.property),
    s28q_isQCRS_symm f.property⟩

/-- The descended action agrees with the already defined actual source relation. -/
theorem modAction_iff_smul (f : Aut X) (p q : TeichSpace X) :
    ModAction (inverseSourceModTransform f) p q ↔ q = mk f • p := by
  have hm : ModAction (inverseSourceModTransform f) p (mk f • p) := by
    refine Quot.inductionOn p ?_
    intro m
    exact ⟨m, s28q_isQCRS_trans (s28q_isQCRS_symm f.property) m.qc, rfl, rfl⟩
  constructor
  · intro h
    exact s28q_modAction_right_unique h hm
  · intro h
    exact h.symm ▸ hm

/-- The literal actual reference change depends only on the original free homotopy class. -/
theorem quotientMap_eq_of_homotopic (f g : Aut X)
    (h : ContinuousMap.Homotopic (continuousMap f) (continuousMap g)) (p : TeichSpace X) :
    SourceReferenceChange.quotientMap f.val f.property p =
      SourceReferenceChange.quotientMap g.val g.property p := by
  have he := congrArg (fun γ : ModularGroup X => γ • p)
    ((mk_eq_mk_iff_homotopic f g).mpr h)
  simpa only [mk_smul] using he

/-- The entire original family of marking-compatible log dilatations is preserved. -/
theorem distanceFamily_smul (γ : ModularGroup X) (p q : TeichSpace X) :
    s29_m_teichSet (γ • p) (γ • q) = s29_m_teichSet p q := by
  refine Quotient.inductionOn γ ?_
  intro f
  change s29_m_teichSet (SourceReferenceChange.quotientMap f.val f.property p)
    (SourceReferenceChange.quotientMap f.val f.property q) = s29_m_teichSet p q
  exact SourceReferenceChange.distanceFamily_eq f.val f.property p q

/-- Every original QC modular class preserves the actual half-log distance on all pairs. -/
theorem teichDistance_smul (γ : ModularGroup X) (p q : TeichSpace X) :
    teichDistance (γ • p) (γ • q) = teichDistance p q := by
  change sInf (s29_m_teichSet (γ • p) (γ • q)) = sInf (s29_m_teichSet p q)
  rw [distanceFamily_smul]

/-- The full-log book distance is preserved by the identical quotient transformation. -/
theorem bookDistance_smul (γ : ModularGroup X) (p q : TeichSpace X) :
    QCBookMetric.bookDistance (γ • p) (γ • q) = QCBookMetric.bookDistance p q := by
  rw [QCBookMetric.bookDistance_eq_two_mul, QCBookMetric.bookDistance_eq_two_mul,
    teichDistance_smul]

variable [T2Space X] [ConnectedSpace X] [CompactSpace X]

/-- The actual QC quotient action is an isometry for the original book metric. -/
theorem bookMetric_isometry {g : ℕ} (hg : 1 < g) (hgenus : HasGenus X g)
    (γ : ModularGroup X) :
    let := QCBookMetric.metricSpace hg hgenus
    Isometry (fun p : TeichSpace X => γ • p) := by
  let := QCBookMetric.metricSpace hg hgenus
  apply Isometry.of_dist_eq
  intro p q
  exact bookDistance_smul γ p q

end LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular

namespace LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Every class of ALL QC self-homeomorphisms of the same original closed
surface acts isometrically, with its actual inherited atlas and handle genus. -/
theorem closedSurface_modular_isometry (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    ∀ γ : ModularGroup X, Isometry (fun p : LiZhongQC.TeichSpace X => γ • p) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  dsimp only
  intro γ
  exact bookMetric_isometry hg (R.hasSourceGenus hgenus) γ

end LowDimensionalTopology.Geometry.Teichmuller.SourceQCModular
