module

public import LowDimensionalTopology.Unproved.Surfaces.ClosedCurveIntersectionGeometry
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!
# Geometric intersection counts on the original free classes

All actual simple representatives in the two prescribed free classes are
allowed. Infinite point intersections retain their extended-natural value.
The natural-valued minimum uses the explicit original representative geometry.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- All actual intersection-point counts in the two exact original class fibers. -/
def geometricIntersectionCounts (a b : EssentialSimpleFreeClass X) : Set ℕ∞ :=
  {n | ∃ c d : EssentialSimpleCircle X,
    c.freeClass = a ∧ d.freeClass = b ∧
      (range c.val ∩ range d.val).encard = n}

/-- The extended infimum retains infinite intersections without a natural fallback. -/
def geometricIntersectionNumberENat (a b : EssentialSimpleFreeClass X) : ℕ∞ :=
  sInf (geometricIntersectionCounts a b)

/-- Both class fibers contain actual representatives of the original quotient. -/
theorem geometricIntersectionCounts_nonempty (a b : EssentialSimpleFreeClass X) :
    (geometricIntersectionCounts a b).Nonempty := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep a
  obtain ⟨d, rfl⟩ := Quotient.exists_rep b
  exact ⟨(range c.val ∩ range d.val).encard, c, d, rfl, rfl, rfl⟩

/-- The extended infimum is bounded by every actual representative intersection. -/
theorem geometricIntersectionNumberENat_le (a b : EssentialSimpleFreeClass X)
    (c d : EssentialSimpleCircle X) (hc : c.freeClass = a) (hd : d.freeClass = b) :
    geometricIntersectionNumberENat a b ≤ (range c.val ∩ range d.val).encard := by
  change sInf (geometricIntersectionCounts a b) ≤ _
  exact sInf_le ⟨c, d, hc, hd, rfl⟩

/-- Every lower bound on the actual class fibers bounds their extended infimum. -/
theorem le_geometricIntersectionNumberENat (a b : EssentialSimpleFreeClass X) (n : ℕ∞)
    (h : ∀ c d : EssentialSimpleCircle X,
      c.freeClass = a → d.freeClass = b → n ≤ (range c.val ∩ range d.val).encard) :
    n ≤ geometricIntersectionNumberENat a b := by
  change n ≤ sInf (geometricIntersectionCounts a b)
  apply le_sInf
  rintro m ⟨c, d, hc, hd, rfl⟩
  exact h c d hc hd

/-- Swapping the actual representative circles leaves the extended count unchanged. -/
theorem geometricIntersectionNumberENat_symm (a b : EssentialSimpleFreeClass X) :
    geometricIntersectionNumberENat a b = geometricIntersectionNumberENat b a := by
  apply le_antisymm
  · apply le_geometricIntersectionNumberENat
    intro c d hc hd
    simpa only [Set.inter_comm] using geometricIntersectionNumberENat_le a b d c hd hc
  · apply le_geometricIntersectionNumberENat
    intro c d hc hd
    simpa only [Set.inter_comm] using geometricIntersectionNumberENat_le b a d c hd hc

/-- The extended minimum is realized by actual representatives, including when infinite. -/
theorem exists_geometricIntersectionNumberENat_representatives
    (a b : EssentialSimpleFreeClass X) :
    ∃ c d : EssentialSimpleCircle X,
      c.freeClass = a ∧ d.freeClass = b ∧
        (range c.val ∩ range d.val).encard = geometricIntersectionNumberENat a b := by
  change geometricIntersectionNumberENat a b ∈ geometricIntersectionCounts a b
  exact csInf_mem (geometricIntersectionCounts_nonempty a b)

variable (R : ClosedRiemannSurface X) {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
include hGeom

include R hg hgenus hGeom in
/-- Finite actual representatives bound the extended minimum strictly below infinity. -/
theorem geometricIntersectionNumberENat_lt_top (a b : EssentialSimpleFreeClass X) :
    geometricIntersectionNumberENat a b < ⊤ := by
  obtain ⟨c, d, hc, hd, hfinite⟩ := hGeom.1 a b
  exact (geometricIntersectionNumberENat_le a b c d hc hd).trans_lt hfinite.encard_lt_top

include R hg hgenus hGeom in
/-- The original finite-pair geometry excludes an infinite intersection minimum. -/
theorem geometricIntersectionNumberENat_ne_top (a b : EssentialSimpleFreeClass X) :
    geometricIntersectionNumberENat a b ≠ ⊤ :=
  (geometricIntersectionNumberENat_lt_top R hg hgenus hGeom a b).ne

/-- The actual geometric intersection minimum, converted only after finiteness is proved. -/
def geometricIntersectionNumber (a b : EssentialSimpleFreeClass X) : ℕ :=
  ENat.lift (geometricIntersectionNumberENat a b)
    (geometricIntersectionNumberENat_lt_top R hg hgenus hGeom a b)

/-- The natural-valued number is precisely the original extended infimum. -/
theorem natCast_geometricIntersectionNumber (a b : EssentialSimpleFreeClass X) :
    (geometricIntersectionNumber R hg hgenus hGeom a b : ℕ∞) =
      geometricIntersectionNumberENat a b := by
  exact ENat.natCast_lift _ _

/-- Geometric intersection is symmetric on the same original free classes. -/
theorem geometricIntersectionNumber_symm (a b : EssentialSimpleFreeClass X) :
    geometricIntersectionNumber R hg hgenus hGeom a b =
      geometricIntersectionNumber R hg hgenus hGeom b a := by
  apply ENat.natCast_inj.mp
  calc
    (geometricIntersectionNumber R hg hgenus hGeom a b : ℕ∞) =
        geometricIntersectionNumberENat a b :=
      natCast_geometricIntersectionNumber R hg hgenus hGeom a b
    _ = geometricIntersectionNumberENat b a := geometricIntersectionNumberENat_symm a b
    _ = (geometricIntersectionNumber R hg hgenus hGeom b a : ℕ∞) :=
      (natCast_geometricIntersectionNumber R hg hgenus hGeom b a).symm

/-- Disjoint actual same-class representatives give the geometric zero diagonal. -/
theorem geometricIntersectionNumber_self (a : EssentialSimpleFreeClass X) :
    geometricIntersectionNumber R hg hgenus hGeom a a = 0 := by
  obtain ⟨c, d, hc, hd, hdisjoint⟩ := hGeom.2.1 a
  have hzero : geometricIntersectionNumberENat a a = 0 := by
    apply le_antisymm
    · calc
        geometricIntersectionNumberENat a a ≤ (range c.val ∩ range d.val).encard :=
          geometricIntersectionNumberENat_le a a c d hc hd
        _ = 0 := by
          rw [Set.disjoint_iff_inter_eq_empty.mp hdisjoint, Set.encard_empty]
    · exact bot_le
  exact ENat.natCast_inj.mp
    ((natCast_geometricIntersectionNumber R hg hgenus hGeom a a).trans hzero)

/-- Every finitely intersecting actual pair bounds the natural geometric minimum. -/
theorem geometricIntersectionNumber_le (a b : EssentialSimpleFreeClass X)
    (c d : EssentialSimpleCircle X) (hc : c.freeClass = a) (hd : d.freeClass = b)
    (hfinite : (range c.val ∩ range d.val).Finite) :
    geometricIntersectionNumber R hg hgenus hGeom a b ≤ (range c.val ∩ range d.val).ncard := by
  apply ENat.natCast_le_natCast.mp
  calc
    (geometricIntersectionNumber R hg hgenus hGeom a b : ℕ∞) =
        geometricIntersectionNumberENat a b :=
      natCast_geometricIntersectionNumber R hg hgenus hGeom a b
    _ ≤ (range c.val ∩ range d.val).encard := geometricIntersectionNumberENat_le a b c d hc hd
    _ = ((range c.val ∩ range d.val).ncard : ℕ∞) := hfinite.cast_ncard_eq.symm

/-- The finite natural minimum is attained in the exact original class fibers. -/
theorem exists_geometricIntersectionNumber_minimizers (a b : EssentialSimpleFreeClass X) :
    ∃ c d : EssentialSimpleCircle X,
      c.freeClass = a ∧ d.freeClass = b ∧
        (range c.val ∩ range d.val).Finite ∧
          (range c.val ∩ range d.val).ncard = geometricIntersectionNumber R hg hgenus hGeom a b := by
  obtain ⟨c, d, hc, hd, hcount⟩ := exists_geometricIntersectionNumberENat_representatives a b
  have hfinite : (range c.val ∩ range d.val).Finite :=
    Set.encard_lt_top_iff.mp
      (lt_of_eq_of_lt hcount (geometricIntersectionNumberENat_lt_top R hg hgenus hGeom a b))
  refine ⟨c, d, hc, hd, hfinite, ?_⟩
  apply ENat.natCast_inj.mp
  exact hfinite.cast_ncard_eq.trans
    (hcount.trans (natCast_geometricIntersectionNumber R hg hgenus hGeom a b).symm)

/-- The original unavoidable dual meets the actual minimizing representatives positively. -/
theorem exists_geometricIntersectionNumber_pos (a : EssentialSimpleFreeClass X) :
    ∃ b : EssentialSimpleFreeClass X, 0 < geometricIntersectionNumber R hg hgenus hGeom a b := by
  obtain ⟨b, hb⟩ := hGeom.2.2 a
  obtain ⟨c, d, hc, hd, hfinite, hminimum⟩ :=
    exists_geometricIntersectionNumber_minimizers R hg hgenus hGeom a b
  refine ⟨b, ?_⟩
  rw [← hminimum]
  exact (Set.ncard_pos hfinite).mpr (hb c d hc hd)

end LowDimensionalTopology.Geometry.Surfaces
