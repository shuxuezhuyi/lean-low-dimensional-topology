/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusOrbitLimits
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The separation property defining a group packing; openness is explicit in domain theorems. -/
def IsMobiusPacking (H : Subgroup Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex) : Prop :=
  ∀ g : H, g ≠ 1 → Disjoint (g.val.val '' D) D

/-- The union of all actual translates of a sphere subset. -/
def mobiusSaturation (H : Subgroup Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex) : Set
    Mobius.ExtendedComplex :=
  ⋃ g : H, g.val.val '' D

theorem subset_mobiusSaturation (H : Subgroup Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex) :
    D ⊆ mobiusSaturation H D := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨1, ⟨z, hz, rfl⟩⟩

theorem mobiusSaturation_isOpen (H : Subgroup Mobius.complexMobiusGroup) {D : Set Mobius.ExtendedComplex}
    (hD : IsOpen D) : IsOpen (mobiusSaturation H D) :=
  isOpen_iUnion fun g => (Mobius.mobiusBoundaryHomeomorph g.val).isOpenMap D hD

theorem mobiusSaturation_invariant (H : Subgroup Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex)
    (h : H) {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusSaturation H D) :
    h • z ∈ mobiusSaturation H D := by
  obtain ⟨g, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨h * g, x, hx, rfl⟩

/-- A proper invariant open domain lies in the ordinary set. -/
theorem mobius_proper_invariant_open_subset_ordinary (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hproper : D ≠ Set.univ)
    (hinv : ∀ g : H, ∀ z ∈ D, g • z ∈ D) : D ⊆ mobiusOrdinarySet H := by
  have hne : Dᶜ.Nonempty := by
    by_contra h
    apply hproper
    apply Set.eq_univ_of_forall
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  have hcomp : ∀ g : H, ∀ z ∈ Dᶜ, g • z ∈ Dᶜ := by
    intro g z hz hgz
    exact hz (by simpa only [inv_smul_smul] using hinv g⁻¹ (g • z) hgz)
  have hlim := mobiusLimitSet_minimal H hH Dᶜ hD.isClosed_compl hne hcomp
  intro z hz hzL
  exact hlim hzL hz

/-- The actual compact-hit condition restricts to every subset of a discontinuity set. -/
theorem IsMobiusDiscontinuousOn.mono {H : Subgroup Mobius.complexMobiusGroup}
    {D S : Set Mobius.ExtendedComplex} (h : IsMobiusDiscontinuousOn H S) (hDS : D ⊆ S) :
    IsMobiusDiscontinuousOn H D :=
  fun K hK hKD => h K hK (hKD.trans hDS)

theorem discontinuous_on_proper_open_invariant_set (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hproper : D ≠ Set.univ)
    (hinv : ∀ g : H, ∀ z ∈ D, g • z ∈ D) : IsMobiusDiscontinuousOn H D :=
  (mobius_ordinary_discontinuous H hH hd).mono
    (mobius_proper_invariant_open_subset_ordinary H hH D hD hproper hinv)

/-- A nonempty open packing of a nontrivial group cannot have translates covering the connected sphere. -/
theorem mobiusPacking_saturation_ne_univ (H : Subgroup Mobius.complexMobiusGroup) [Nontrivial H]
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hne : D.Nonempty) (hp : IsMobiusPacking H D) :
    mobiusSaturation H D ≠ Set.univ := by
  intro hcover
  have hcompl : Dᶜ = ⋃ (g : H) (_ : g ≠ 1), g.val.val '' D := by
    ext z
    constructor
    · intro hz
      have hzS : z ∈ mobiusSaturation H D := by rw [hcover]; trivial
      obtain ⟨g, hzg⟩ := Set.mem_iUnion.mp hzS
      have hg : g ≠ 1 := by
        intro he
        subst g
        apply hz
        obtain ⟨x, hx, rfl⟩ := hzg
        exact hx
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, hzg⟩⟩
    · intro hz hzD
      obtain ⟨g, hzg'⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hg, hzg⟩ := Set.mem_iUnion.mp hzg'
      exact Set.disjoint_left.mp (hp g hg) hzg hzD
  have hco : IsOpen Dᶜ := by
    rw [hcompl]
    exact isOpen_iUnion fun g => isOpen_iUnion fun _ =>
      (Mobius.mobiusBoundaryHomeomorph g.val).isOpenMap D hD
  have hc : IsClopen D := ⟨by simpa only [compl_compl] using hco.isClosed_compl, hD⟩
  have hu : D = Set.univ := IsClopen.eq_univ hc hne
  obtain ⟨g, hg⟩ := exists_ne (1 : H)
  obtain ⟨z, hz⟩ := hne
  have hgz : g.val.val z ∈ D := by rw [hu]; trivial
  exact Set.disjoint_left.mp (hp g hg) ⟨z, hz, rfl⟩ hgz

/-- on the genuine union of all translates of an open packing. -/
theorem discontinuous_on_saturation_of_open_packing (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hne : D.Nonempty) (hp : IsMobiusPacking H D) :
    IsMobiusDiscontinuousOn H (mobiusSaturation H D) := by
  let : Infinite H := nonElementary_infinite H hH
  exact discontinuous_on_proper_open_invariant_set H hH hd _ (mobiusSaturation_isOpen H hD)
    (mobiusPacking_saturation_ne_univ H D hD hne hp)
    (fun g _ hz => mobiusSaturation_invariant H D g hz)

/-- Distinct translates of a packing are disjoint in the actual sphere action. -/
theorem IsMobiusPacking.disjoint_translates {H : Subgroup Mobius.complexMobiusGroup}
    {D : Set Mobius.ExtendedComplex} (hp : IsMobiusPacking H D) (g h : H) (hgh : g ≠ h) :
    Disjoint (g.val.val '' D) (h.val.val '' D) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  have hhg : h⁻¹ * g ≠ 1 := by
    intro hh
    apply hgh
    simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using congrArg (fun k : H => h * k) hh
  have hxy : (h⁻¹ * g).val.val u = v := by
    apply h.val.val.injective
    change h.val.val (h.val.val.symm (g.val.val u)) = h.val.val v
    rw [Equiv.apply_symm_apply]
    exact he.symm
  exact Set.disjoint_left.mp (hp (h⁻¹ * g) hhg) ⟨u, hu, rfl⟩ (hxy ▸ hv)

/-- An open packing gives a genuine discontinuous action on its saturation, without prior group hypotheses. -/
theorem mobius_openPacking_saturation_discontinuous (H : Subgroup Mobius.complexMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hp : IsMobiusPacking H D) :
    IsMobiusDiscontinuousOn H (mobiusSaturation H D) := by
  classical
  intro K hK hKS
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun g : H => g.val.val '' D)
    (fun g => (Mobius.mobiusBoundaryHomeomorph g.val).isOpenMap D hD)
    hKS
  apply (((F.finite_toSet).prod (F.finite_toSet)).image
    (fun p : H × H => p.1 * p.2⁻¹)).subset
  rintro g ⟨y, ⟨x, hxK, rfl⟩, hgyK⟩
  obtain ⟨i, hxi'⟩ := Set.mem_iUnion.mp (hF hxK)
  obtain ⟨hiF, hxi⟩ := Set.mem_iUnion.mp hxi'
  obtain ⟨j, hgj'⟩ := Set.mem_iUnion.mp (hF hgyK)
  obtain ⟨hjF, hgj⟩ := Set.mem_iUnion.mp hgj'
  have hgi : g * i = j := by
    by_contra hne
    apply Set.disjoint_left.mp (DiscreteGroups.IsMobiusPacking.disjoint_translates hp (g * i) j hne) _ hgj
    obtain ⟨u, hu, hux⟩ := hxi
    exact ⟨u, hu, by change g.val.val (i.val.val u) = g.val.val x; rw [hux]⟩
  refine ⟨(j, i), ⟨hjF, hiF⟩, ?_⟩
  change j * i⁻¹ = g
  rw [← hgi, mul_assoc, mul_inv_cancel, mul_one]

end
end LowDimensionalTopology.Geometry.DiscreteGroups
