/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicInvariants
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex

/-- One genuine representative of each pair of a fixed-point-free involution. -/
abbrev InvolutionPositive {α:Type} [LinearOrder α] (p:α→α) : Type:={a:α // a<p a}

/-- Every member of a paired finite boundary is exactly one signed occurrence of its actual unoriented edge pair. -/
def freeInvolutionDartEquiv {α:Type} [LinearOrder α] (p:α→α)
    (hinv:Function.Involutive p) (hfree:∀a,p a≠a) : α≃SignedDart (InvolutionPositive p) where
  toFun a:=if h:a<p a then .pos ⟨a,h⟩ else .neg ⟨p a,by
    rw [hinv a]
    exact lt_of_le_of_ne (le_of_not_gt h) (hfree a)⟩
  invFun d:=match d with
    | .pos a=>a.val
    | .neg a=>p a.val
  left_inv a:=by
    by_cases h:a<p a
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h,hinv a]
  right_inv d:=by
    cases d with
    | pos a=>
      simp only [dite_eq_left a.property]
    | neg a=>
      have hnot:¬p a.val<p (p a.val):=by rw [hinv a.val];exact not_lt_of_gt a.property
      simp only [dite_eq_right hnot]
      congr 1
      exact Subtype.ext (hinv a.val)

/-- The actual pairing corresponds exactly to reversal of the signed dart. -/
theorem freeInvolutionDartEquiv_pair {α:Type} [LinearOrder α] (p:α→α)
    (hinv:Function.Involutive p) (hfree:∀a,p a≠a) (a:α) :
    freeInvolutionDartEquiv p hinv hfree (p a)=(freeInvolutionDartEquiv p hinv hfree a).flip := by
  by_cases h:a<p a
  · have hnot:¬p a<p (p a):=by rw [hinv a];exact not_lt_of_gt h
    change (if _h:p a<p (p a) then _ else _)= @SignedDart.flip (InvolutionPositive p) (if _h:a<p a then _ else _)
    simp only [dite_eq_right hnot,dite_eq_left h,SignedDart.flip]
    congr 1
    exact Subtype.ext (hinv a)
  · have hp:p a<p (p a):=by rw [hinv a];exact lt_of_le_of_ne (le_of_not_gt h) (hfree a)
    change (if _h:p a<p (p a) then _ else _)= @SignedDart.flip (InvolutionPositive p) (if _h:a<p a then _ else _)
    simp only [dite_eq_left hp,dite_eq_right h,SignedDart.flip]

/-- The stored cyclic word enumerates the actual boundary occurrences in their original finite order. -/
def freeInvolutionWord {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) : List (SignedDart (InvolutionPositive p)):=
  List.ofFn (freeInvolutionDartEquiv p hinv hfree)

@[simp] theorem freeInvolutionWord_length {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) : (freeInvolutionWord p hinv hfree).length=n:=List.length_ofFn

theorem freeInvolutionWord_nodup {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) : (freeInvolutionWord p hinv hfree).Nodup:=
  List.nodup_ofFn.mpr (freeInvolutionDartEquiv p hinv hfree).injective

theorem freeInvolutionWord_mem {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) (d:SignedDart (InvolutionPositive p)) : d∈freeInvolutionWord p hinv hfree := by
  rw [freeInvolutionWord,List.mem_ofFn]
  exact (freeInvolutionDartEquiv p hinv hfree).surjective d

/-- Each actual signed edge occurs exactly once in the stored boundary. -/
theorem freeInvolutionWord_count {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) (d:SignedDart (InvolutionPositive p)) : (freeInvolutionWord p hinv hfree).count d=1 := by
  exact List.count_eq_one_of_mem (freeInvolutionWord_nodup p hinv hfree) (freeInvolutionWord_mem p hinv hfree d)

/-- Forgetting the dart sign counts exactly the positive and negative occurrences. -/
theorem count_map_signed_edge {E:Type} [DecidableEq E] (w:List (SignedDart E)) (e:E) :
    (w.map edgeOfDart).count e=w.count (.pos e)+w.count (.neg e) := by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    cases d with
    | pos a=>
      by_cases he:a=e
      · simp [edgeOfDart,he,ih]
        omega
      · simp [edgeOfDart,he,ih]
    | neg a=>
      by_cases he:a=e
      · simp [edgeOfDart,he,ih]
        omega
      · simp [edgeOfDart,he,ih]

/-- Literal signed incidence is the difference of the genuine occurrence counts. -/
theorem wordCoefficient_eq_count_difference {E:Type} [DecidableEq E] (w:List (SignedDart E)) (e:E) :
    wordCoefficient e w=(w.count (.pos e):ℤ)-(w.count (.neg e):ℤ) := by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    cases d with
    | pos a=>
      by_cases he:a=e
      · simp [wordCoefficient_cons,dartCoefficient,he,ih]
        omega
      · simp [wordCoefficient_cons,dartCoefficient,he,ih]
    | neg a=>
      by_cases he:a=e
      · simp [wordCoefficient_cons,dartCoefficient,he,ih]
        omega
      · simp [wordCoefficient_cons,dartCoefficient,he,ih]

/-- The actual word of a free involution has no boundary edges: every edge really occurs twice. -/
theorem freeInvolutionWord_closed {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) : IsClosed (ofOneFaceWord (freeInvolutionWord p hinv hfree)) := by
  rw [oneFace_closed_iff]
  intro e
  rw [count_map_signed_edge,freeInvolutionWord_count,freeInvolutionWord_count]

/-- The actual word has a coherent one-face orientation because each edge occurs once with each sign. -/
theorem freeInvolutionWord_coherent {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) : IsCoherentlyOrientable (ofOneFaceWord (freeInvolutionWord p hinv hfree)) := by
  rw [oneFace_coherent_iff]
  intro e
  rw [wordCoefficient_eq_count_difference,freeInvolutionWord_count,freeInvolutionWord_count]
  norm_num

/-- The original-order one-face word is a genuine incidence-valid finite cyclic presentation. -/
theorem freeInvolutionWord_valid {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) (hn:0<n) : (ofOneFaceWord (freeInvolutionWord p hinv hfree)).IsSurfaceValid := by
  apply ofOneFaceWord_isSurfaceValid
  · intro he
    have hh:=congrArg List.length he
    rw [freeInvolutionWord_length,List.length_nil] at hh
    exact (Nat.ne_of_gt hn) hh
  · intro e
    right
    rw [count_map_signed_edge,freeInvolutionWord_count,freeInvolutionWord_count]

/-- The actual incidence-valid word, bundled for the verified finite cyclic normalization theorem. -/
def freeInvolutionPresentation {n:ℕ} (p:Fin n→Fin n) (hinv:Function.Involutive p)
    (hfree:∀a,p a≠a) (hn:0<n) : ValidPresentation:=
  ⟨ofOneFaceWord (freeInvolutionWord p hinv hfree),freeInvolutionWord_valid p hinv hfree hn⟩
end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
