import Holant.Complexity.UniversalPairReduction.Surgery.PromisedValidation

namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution Smoothing RawClosedNetwork
variable {s : ℕ} {arity : ℕ → ℕ}

/-- Exhaustive result of the compiler's own search on the unchanged raw input. -/
theorem selected (r : Input s arity) :
    (FixedGadgetSubstitution.occurrences s r.val=0 ∧ Smoothing.compile s r.val=⟨r.val,false⟩ ∧
      ∀row∈r.val.vertices,row.1<s) ∨
    ∃(v : Fin r.val.vertices.length) (p q : RawEndpoint),
      (r.val.vertices.get v).1=s ∧ (r.val.vertices.get v).2=[p,q] ∧
      FixedGadgetSubstitution.occurrences s r.val=1 ∧ Smoothing.compile s r.val=smoothAt r.val v.val p q := by
  let idx := r.val.vertices.findIdx (fun row => row.1 == s)
  by_cases hi : idx<r.val.vertices.length
  · let v : Fin r.val.vertices.length := ⟨idx,hi⟩
    have hl : (r.val.vertices.get v).1=s := by
      have hh := @List.findIdx_getElem RawVertex (fun row => row.1 == s) r.val.vertices hi
      simpa only [beq_iff_eq,List.get_eq_getElem] using hh
    have hlen : (r.val.vertices.get v).2.length=2 := by
      have hh := (r.property.1.1 v).2
      simpa only [hl,extendedArity,lt_self_iff_false,ite_false] using hh
    obtain ⟨p,q,hrow⟩ := List.length_eq_two.mp hlen
    have hcount : FixedGadgetSubstitution.occurrences s r.val=1 := by
      have hm : r.val.vertices.get v∈r.val.vertices.filter (fun row => row.1 == s) := by
        exact List.mem_filter.mpr ⟨List.get_mem _ _,by simpa only [beq_iff_eq] using hl⟩
      have hp := List.length_pos_of_mem hm
      have hb := r.property.2
      unfold FixedGadgetSubstitution.occurrences at hb ⊢
      omega
    right
    refine ⟨v,p,q,hl,hrow,hcount,?_⟩
    have hg : r.val.vertices[idx]?=some (r.val.vertices.get v) := List.getElem?_eq_getElem hi
    change (match (r.val.vertices[idx]?).map Prod.snd with
      | some [first,second] => smoothAt r.val idx first second
      | _ => ⟨r.val,false⟩)=_
    rw [hg]
    simp only [Option.map_some,hrow]
    rfl
  · have hlen : idx=r.val.vertices.length := Nat.le_antisymm
      (List.findIdx_le_length) (Nat.le_of_not_gt hi)
    have hn : ∀row∈r.val.vertices,(row.1 == s)=false := List.findIdx_eq_length.mp hlen
    have hf : r.val.vertices.filter (fun row => row.1 == s)=[] :=
      List.filter_eq_nil_iff.mpr (fun row hr => by simp [hn row hr])
    left
    refine ⟨by simp [FixedGadgetSubstitution.occurrences,hf],?_,?_⟩
    · simp only [Smoothing.compile,show r.val.vertices.findIdx (fun row => row.1 == s)=r.val.vertices.length from hlen,
        List.getElem?_length,Option.map_none]
    · intro row hr
      obtain ⟨u,rfl⟩ := List.mem_iff_get.mp hr
      have hu := (r.property.1.1 u).1
      have hneq := hn (r.val.vertices.get u) (List.get_mem r.val.vertices u)
      simp only [beq_eq_false_iff_ne] at hneq
      omega

end Holant.Complexity.UniversalPairReduction.Surgery
