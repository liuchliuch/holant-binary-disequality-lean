import Holant.Complexity.UniversalPairReduction.Surgery.Validation

/-! The original at-most-one promise implies all side conditions of the raw
surgery validator. No marked index, incident edge IDs or processed graph is
supplied with the input. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution Smoothing RawClosedNetwork
variable {s : ℕ} {arity : ℕ → ℕ}

 theorem erased_no_mark (r : Input s arity) (v : Fin r.val.vertices.length)
    (hv : (r.val.vertices.get v).1=s) :
    ∀row∈r.val.vertices.eraseIdx v.val,row.1≠s := by
  have hp := (List.getElem_cons_eraseIdx_perm v.isLt).filter (fun row : RawVertex => row.1 == s)
  have hl := hp.length_eq
  have hcount := r.property.2
  change (r.val.vertices.filter (fun row => row.1 == s)).length≤1 at hcount
  simp only [List.filter_cons,List.get_eq_getElem] at hl
  have hv' : r.val.vertices[v.val].1=s := hv
  rw [hv'] at hl
  simp only [beq_self_eq_true,ite_true,List.length_cons] at hl
  have hempty : (r.val.vertices.eraseIdx v.val).filter (fun row => row.1 == s)=[] :=
    List.length_eq_zero_iff.mp (by omega)
  intro row hrow he
  have hm : row∈(r.val.vertices.eraseIdx v.val).filter (fun row => row.1 == s) := by
    simp [hrow,he]
  rw [hempty] at hm
  exact List.not_mem_nil hm

 theorem erased_valid (r : Input s arity) (v : Fin r.val.vertices.length)
    (hv : (r.val.vertices.get v).1=s) :
    ∀row∈r.val.vertices.eraseIdx v.val,row.1<s ∧ row.2.length=arity row.1 := by
  intro row hrow
  have hmem : row∈r.val.vertices := (List.eraseIdx_sublist r.val.vertices v.val).subset hrow
  obtain ⟨u,hu⟩ := List.mem_iff_get.mp hmem
  have hr := r.property.1.1 u
  rw [hu] at hr
  have hn := erased_no_mark r v hv row hrow
  have hs : row.1<s := by omega
  exact ⟨hs,hr.2.trans (if_pos hs)⟩

/-- The complete literal smoothing compiler always returns a valid original-
family instance on every input accepted by the original one-pair decoder. -/
theorem compile_wellFormed (r : Input s arity) :
    (Smoothing.compile s r.val).query.WellFormed s 1 arity := by
  let v := r.val.vertices.findIdx (fun row => row.1 == s)
  by_cases hv : v<r.val.vertices.length
  · let vi : Fin r.val.vertices.length := ⟨v,hv⟩
    have hlabel : (r.val.vertices.get vi).1=s := by
      have hh := @List.findIdx_getElem RawVertex (fun row => row.1 == s) r.val.vertices hv
      simpa only [beq_iff_eq,List.get_eq_getElem] using hh
    have hlen : (r.val.vertices.get vi).2.length=2 := by
      have hh := (r.property.1.1 vi).2
      simpa only [hlabel,extendedArity,lt_self_iff_false,ite_false] using hh
    obtain ⟨p,q,hrow⟩ := List.length_eq_two.mp hlen
    have he := smoothAt_wellFormed r.val r.property.1 vi p q hrow (erased_valid r vi hlabel)
    have hg : r.val.vertices[v]?=some (r.val.vertices.get vi) := List.getElem?_eq_getElem hv
    change (match (r.val.vertices[v]?).map Prod.snd with
      | some [first,second] => smoothAt r.val v first second
      | _ => ⟨r.val,false⟩).query.WellFormed s 1 arity
    rw [hg]
    simp only [Option.map_some,hrow]
    exact he
  · have hvlen : v=r.val.vertices.length := Nat.le_antisymm
      (List.findIdx_le_length) (Nat.le_of_not_gt hv)
    have hnone : ∀row∈r.val.vertices,(row.1 == s)=false := List.findIdx_eq_length.mp hvlen
    have hr : r.val.WellFormed s 1 arity := by
      refine ⟨?_,r.property.1.2.1,r.property.1.2.2⟩
      intro u
      have hh := r.property.1.1 u
      have hn := hnone (r.val.vertices.get u) (List.get_mem _ _)
      have hs : (r.val.vertices.get u).1<s := by simp only [beq_eq_false_iff_ne] at hn; omega
      exact ⟨hs,hh.2.trans (if_pos hs)⟩
    simpa only [Smoothing.compile,show r.val.vertices.findIdx (fun row => row.1 == s)=r.val.vertices.length from hvlen,
      List.getElem?_length,Option.map_none] using hr

 def query (r : Input s arity) : {r : RawClosedNetwork // r.WellFormed s 1 arity} :=
  ⟨(Smoothing.compile s r.val).query,compile_wellFormed r⟩

end Holant.Complexity.UniversalPairReduction.Surgery
