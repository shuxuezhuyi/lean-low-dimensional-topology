/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The elementary group constructions and the internal free-product normal-form
definition. Reduced words contain no identity letters; the empty word represents
the identity. The indexing of a finite symmetric group uses `Fin n`.
-/

@[expose] public section

universe u v w

namespace LowDimensionalTopology.Geometry.Auxiliary.Algebra.Groups

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The symmetric group on a set of cardinality `n`. -/
abbrev symmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- The symmetric group defined is finite. -/
theorem symmetricGroup_finite (n : ℕ) : Finite (symmetricGroup n) := inferInstance

/-- transpositions generate the finite symmetric group. -/
theorem symmetricGroup_generated_by_transpositions (n : ℕ) :
    Subgroup.closure {σ : symmetricGroup n | σ.IsSwap} = ⊤ :=
  Equiv.Perm.closure_isSwap

/-- The kernel of a group homomorphism is normal. -/
theorem kernel_normal (f : G →* H) : f.ker.Normal := inferInstance

/-- The first isomorphism theorem for a surjective homomorphism. -/
noncomputable def firstIsomorphism (f : G →* H) (hf : Function.Surjective f) :
    G ⧸ f.ker ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective f hf

/-- conjugacy of group elements. -/
abbrev AreConjugate (g h : G) : Prop := IsConj g h

/-- The conjugating element may be taken in the group itself. -/
theorem areConjugate_iff (g h : G) :
    AreConjugate g h ↔ ∃ x : G, x * g * x⁻¹ = h :=
  isConj_iff

/-- The conjugacy class of an element. -/
def conjugacyClass (g : G) : Set G := conjugatesOf g

/-- The conjugacy class consists of exactly the conjugates in the geometric convention. -/
theorem mem_conjugacyClass_iff (g h : G) :
    h ∈ conjugacyClass g ↔ ∃ x : G, x * g * x⁻¹ = h :=
  isConj_iff

/-- Every element belongs to exactly one conjugacy class. -/
theorem conjugacyClasses_partition (g : G) :
    ∃! c : ConjClasses G, g ∈ c.carrier := by
  refine ⟨ConjClasses.mk g, ConjClasses.mem_carrier_mk, ?_⟩
  intro c hc
  exact (ConjClasses.mem_carrier_iff_mk_eq.mp hc).symm

/-- Distinct conjugacy classes are disjoint. -/
theorem conjugacyClasses_disjoint {c d : ConjClasses G} (hcd : c ≠ d) :
    Disjoint c.carrier d.carrier := by
  apply Set.disjoint_left.mpr
  intro g hc hd
  exact hcd ((ConjClasses.mem_carrier_iff_mk_eq.mp hc).symm.trans
    (ConjClasses.mem_carrier_iff_mk_eq.mp hd))

/-- The map with fixed element `g` and conjugating variable `x`. -/
def conjugationMap (g x : G) : G := x * g * x⁻¹

/-- right translation by the inverse of the fixed element. -/
def inverseTranslate (g x : G) : G := x * g⁻¹

/-- The image of the variable conjugation map is the conjugacy class. -/
theorem range_conjugationMap (g : G) :
    Set.range (conjugationMap g) = conjugacyClass g := by
  ext h
  exact (mem_conjugacyClass_iff g h).symm

/-- The variable conjugation map is surjective exactly for a trivial group. -/
theorem conjMap_surjective_iff_subsingleton (g : G) :
    Function.Surjective (conjugationMap g) ↔ Subsingleton G := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h 1
    have hg : g = 1 := isConj_one_left.mp (isConj_iff.mpr ⟨x, hx⟩)
    refine ⟨fun y z => ?_⟩
    obtain ⟨a, ha⟩ := h y
    obtain ⟨b, hb⟩ := h z
    have hy : y = 1 := by simpa [conjugationMap, hg] using ha.symm
    have hz : z = 1 := by simpa [conjugationMap, hg] using hb.symm
    exact hy.trans hz.symm
  · intro h
    let := h
    exact fun y => ⟨1, Subsingleton.elim _ _⟩

/-- Right translation by an inverse is bijective. -/
theorem inverseTranslate_bijective (g : G) : Function.Bijective (inverseTranslate g) := by
  constructor
  · intro x y h
    exact mul_right_cancel h
  · intro y
    exact ⟨y * g, by simp [inverseTranslate, mul_assoc]⟩

open scoped commutatorElement

/-- The commutator with the convention `ghg⁻¹h⁻¹`. -/
def commutator (g h : G) : G := ⁅g, h⁆

/-- The commutator convention is explicit. -/
theorem commutator_eq (g h : G) : commutator g h = g * h * g⁻¹ * h⁻¹ := rfl

/-- The commutator is `g` multiplied by a conjugate of `g⁻¹`. -/
theorem commutator_eq_mul_conjugate (g h : G) :
    commutator g h = g * (h * g⁻¹ * h⁻¹) := by
  simp [commutator, commutatorElement_def, mul_assoc]

section FreeProduct

variable {ι : Type w} (K : ι → Subgroup G)

/-- alternating words with no identity letters. -/
abbrev ReducedWord := Monoid.CoprodI.Word (fun i => K i)

/-- Evaluate a reduced word by multiplying its letters in the ambient group. -/
def reducedWordEval (word : ReducedWord K) : G :=
  (word.toList.map fun letter => (letter.2 : G)).prod

/-- The empty word represents the identity. -/
theorem reducedWordEval_empty :
    reducedWordEval K Monoid.CoprodI.Word.empty = 1 := rfl

/-- existence and uniqueness of an alternating reduced expression. -/
def HasFreeProductNormalForm : Prop :=
  ∀ g : G, ∃! word : ReducedWord K, reducedWordEval K word = g

/--
An internal free-product presentation by a family of subgroups.

Generation and trivial pairwise intersections are retained from the geometric setup.
The normal-form condition is a separate requirement, not a consequence asserted
from these first two conditions.
-/
structure IsInternalFreeProduct : Prop where
  generated : (⨆ i, K i) = ⊤
  pairwise_disjoint : Pairwise fun i j => Disjoint (K i) (K j)
  normal_form : HasFreeProductNormalForm K

/-- Under the geometric setup, being a free product means unique reduced expressions. -/
theorem isInternalFreeProduct_iff
    (hgen : (⨆ i, K i) = ⊤)
    (hdis : Pairwise fun i j => Disjoint (K i) (K j)) :
    IsInternalFreeProduct K ↔ HasFreeProductNormalForm K :=
  ⟨fun h => h.normal_form, fun h => ⟨hgen, hdis, h⟩⟩

end FreeProduct

end LowDimensionalTopology.Geometry.Auxiliary.Algebra.Groups
