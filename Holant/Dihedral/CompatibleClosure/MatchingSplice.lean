import Holant.Dihedral.EndpointParallelogram.Matching
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Sort

/-! Actual original-vertex incidence update when an edge of one matching is
closed and the two incident edges of the other matching are spliced. -/
namespace Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.EndpointParallelogram

variable {ι : Type*} [DecidableEq ι]

abbrev Remaining (u v : ι) := {i : ι // i ≠ u ∧ i ≠ v}

private theorem mate_injective (P : Pairing ι) : Function.Injective P.mate := P.involutive.injective

private theorem cross_reverse (P : Pairing ι) {u v : ι} (h : P.mate u ≠ v) : P.mate v ≠ u := by
  intro he
  apply h
  exact ((P.involutive v).symm.trans (congrArg P.mate he)).symm

/-- Delete a pair already matched by P. Every surviving original incidence is
unchanged. -/
def deleteMatched (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u = v) :
    Pairing (Remaining u v) where
  mate x := ⟨P.mate x.val,by
    constructor
    · intro he
      exact x.property.2 (((P.involutive x.val).symm.trans (congrArg P.mate he)).trans h)
    · intro he
      exact x.property.1 (mate_injective P (he.trans h.symm))⟩
  involutive := by intro x; apply Subtype.ext; exact P.involutive x.val
  fixed_free := by intro x he; exact P.fixed_free x.val (congrArg Subtype.val he)

/-- The two other original neighbors are distinct surviving vertices. -/
theorem neighbors_survive (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v) :
    P.mate u ≠ u ∧ P.mate u ≠ v ∧ P.mate v ≠ u ∧ P.mate v ≠ v ∧ P.mate u ≠ P.mate v :=
  ⟨P.fixed_free u,h,cross_reverse P h,P.fixed_free v,fun he => huv (mate_injective P he)⟩

def spliceMate (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v)
    (x : Remaining u v) : Remaining u v :=
  if ha : x.val = P.mate u then
    ⟨P.mate v,(neighbors_survive P u v huv h).2.2.1,(neighbors_survive P u v huv h).2.2.2.1⟩
  else if hb : x.val = P.mate v then
    ⟨P.mate u,(neighbors_survive P u v huv h).1,(neighbors_survive P u v huv h).2.1⟩
  else ⟨P.mate x.val,by
    constructor
    · intro he
      exact ha ((P.involutive x.val).symm.trans (congrArg P.mate he))
    · intro he
      exact hb ((P.involutive x.val).symm.trans (congrArg P.mate he))⟩

theorem spliceMate_val (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v)
    (x : Remaining u v) :
    (spliceMate P u v huv h x).val =
      if x.val = P.mate u then P.mate v else if x.val = P.mate v then P.mate u else P.mate x.val := by
  unfold spliceMate
  split_ifs <;> rfl

/-- This is a genuine perfect matching on exactly the undeleted original ports. -/
def spliceMatching (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v) :
    Pairing (Remaining u v) where
  mate := spliceMate P u v huv h
  involutive := by
    intro x
    apply Subtype.ext
    simp only [spliceMate_val]
    obtain ⟨hau,hav,hbu,hbv,hab⟩ := neighbors_survive P u v huv h
    by_cases ha : x.val = P.mate u
    · simp [ha,Ne.symm hab]
    by_cases hb : x.val = P.mate v
    · simp [ha,hb,hab]
    have hma : P.mate x.val ≠ P.mate u := fun he => x.property.1 (mate_injective P he)
    have hmb : P.mate x.val ≠ P.mate v := fun he => x.property.2 (mate_injective P he)
    simp only [ha,hb,hma,hmb,ite_false]
    exact P.involutive x.val
  fixed_free := by
    intro x he
    have hv := congrArg Subtype.val he
    simp only [spliceMate_val] at hv
    obtain ⟨hau,hav,hbu,hbv,hab⟩ := neighbors_survive P u v huv h
    by_cases ha : x.val = P.mate u
    · simp [ha,Ne.symm hab] at hv
    by_cases hb : x.val = P.mate v
    · simp only [hb,Ne.symm hab,ite_false,ite_true] at hv
      exact hab hv
    exact P.fixed_free x.val (by simpa [ha,hb] using hv)

/-- All other incidences are literally retained, so every alternating segment
outside the two removed vertices is unchanged. -/
theorem splice_unaffected (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v)
    (x : Remaining u v) (ha : x.val ≠ P.mate u) (hb : x.val ≠ P.mate v) :
    ((spliceMatching P u v huv h).mate x).val = P.mate x.val := by
  simp only [spliceMatching,spliceMate_val,ha,hb,ite_false]

/-- The former two incident edges become one edge between their other ends. -/
theorem splice_connects (P : Pairing ι) (u v : ι) (huv : u ≠ v) (h : P.mate u ≠ v)
    (x : Remaining u v) (hx : x.val = P.mate u) :
    ((spliceMatching P u v huv h).mate x).val = P.mate v := by
  simp only [spliceMatching,spliceMate_val,hx,ite_true]

def removedPorts (u v : ι) (huv : u ≠ v) : (Bool ⊕ Remaining u v) ≃ ι where
  toFun
    | .inl false => u
    | .inl true => v
    | .inr x => x.val
  invFun i := if hu : i = u then .inl false else if hv : i = v then .inl true else .inr ⟨i,hu,hv⟩
  left_inv := by
    rintro (b | x)
    · cases b <;> simp [huv,Ne.symm huv]
    · simp [x.property.1,x.property.2]
  right_inv := by
    intro i
    dsimp only
    split_ifs with hu hv
    · exact hu.symm
    · exact hv.symm
    · rfl

theorem exactly_two_ports_removed [Fintype ι] (u v : ι) (huv : u ≠ v) :
    Fintype.card ι = Fintype.card (Remaining u v) + 2 := by
  have hh := Fintype.card_congr (removedPorts u v huv)
  simpa [Fintype.card_sum,Nat.add_comm] using hh.symm

end Holant.Dihedral.CompatibleClosure
