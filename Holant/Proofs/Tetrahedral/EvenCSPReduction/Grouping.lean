import Holant.Proofs.Tetrahedral.EvenCSPReduction.Data
import Mathlib.Data.List.NodupEquivFin


namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw
open scoped BigOperators

theorem portList_nodup (r : Raw) : r.portList.Nodup := by
  change ((List.finRange r.factors.length).sigma
    (fun v => List.finRange (r.factors.get v).2.length)).Nodup
  exact (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

theorem occurrences_nodup (r : Raw) (i : ℕ) : (r.occurrences i).Nodup :=
  r.portList_nodup.filter _

variable {s : ℕ} {a : ℕ → ℕ}

def fibers (r : Input s a) : r.val.Ports ≃
    Σi : Fin r.val.variables,{p : r.val.Ports // (route r) p=i} where
  toFun p := ⟨(route r) p,⟨p,rfl⟩⟩
  invFun q := q.2.val
  left_inv p := rfl
  right_inv := by
    rintro ⟨i,p,hi⟩
    subst i
    rfl

def fiberMembership (r : Input s a) (i : Fin r.val.variables) :
    {p : r.val.Ports // (route r) p=i} ≃ {p : r.val.Ports // p ∈ r.val.occurrences i.val} where
  toFun p := ⟨p.val,(r.val.occurrences_mem i.val p.val).mpr (congrArg Fin.val p.property)⟩
  invFun p := ⟨p.val,Fin.ext ((r.val.occurrences_mem i.val p.val).mp p.property)⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

def fiberOrdinal (r : Input s a) (i : Fin r.val.variables) :
    {p : r.val.Ports // (route r) p=i} ≃ Fin (r.val.degree i.val) :=
  ((fiberMembership r) i).trans
    (List.Nodup.getEquiv (r.val.occurrences i.val) (r.val.occurrences_nodup i.val)).symm

/-- All original port occurrences partition into their internally computed
variable and ordered local occurrence, with multiplicity preserved. -/
def grouping (r : Input s a) : r.val.Ports ≃
    Σi : Fin r.val.variables,Fin (r.val.degree i.val) :=
  (fibers r).trans (Equiv.sigmaCongrRight ((fiberOrdinal r)))

theorem grouping_variable (r : Input s a) (p : r.val.Ports) :
    ((grouping r) p).1=(route r) p := rfl

theorem grouping_ordinal (r : Input s a) (p : r.val.Ports) :
    ((grouping r) p).2.val=(r.val.occurrences (r.val.address p)).idxOf p := rfl

theorem grouping_inverse (r : Input s a) (i : Fin r.val.variables)
    (j : Fin (r.val.degree i.val)) :
    (grouping r).symm ⟨i,j⟩=(r.val.occurrences i.val).get j := rfl

theorem degree_sum (r : Input s a) :
    (∑i : Fin r.val.variables,r.val.degree i.val)=Fintype.card r.val.Ports := by
  have h := Fintype.card_congr (grouping r)
  simpa only [Fintype.card_sigma,Fintype.card_fin] using h.symm

/-- The stable fiber word has precisely the original port value at the
computed occurrence ordinal. This is literal getter transport. -/
def fiberWord (r : Input s a) (z : r.val.Ports → Bool) (i : Fin r.val.variables) :
    Fin (r.val.degree i.val) → Bool :=
  fun j => z ((grouping r).symm ⟨i,j⟩)

theorem fiberWord_at (r : Input s a) (z : r.val.Ports → Bool) (p : r.val.Ports) :
    (fiberWord r) z ((grouping r) p).1 ((grouping r) p).2=z p := by
  exact congrArg z ((grouping r).symm_apply_apply p)

end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw
