import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeState
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeFilter
import Holant.Proofs.Hardness.ThreeModeAnnihilatorFilterSemantics

/-! Exact finite-prefix semantics of the literal collision-aware inner scan. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
namespace S
export EOBinaryConjugateProgrammeState (State initial step advance desired root)
end S
namespace A
export EOBinaryConjugateProgrammeFilter (unwanted multiplicity denominator numerator term result)
export ThreeModeAnnihilator (differenceFilter)
end A
namespace V
export ThreeModeAnnihilatorFilterSemantics (table table_length difference_table)
end V
set_option maxRecDepth 32768
set_option Elab.async false
variable {L : Type} [Field L]
local instance : DecidableEq L := Classical.decEq L

/-- A scan has one round per original root, including equal-root branches. -/
theorem scan_exact (roots remaining : List (L×L)) (moments : List L)
    (p : L×L) (pending : List (L×L)) (values : ℕ→L)
    (n : ℕ) (den count num div : L) (fuel : ℕ) :
    S.step^[remaining.length]
      (⟨roots,moments,p::pending,remaining,
        V.table ((A.unwanted (remaining.map Prod.fst) p.1).length+n) values,
        den,count,num,div,fuel⟩ : S.State L) =
      (⟨roots,moments,p::pending,[],
        V.table n (A.differenceFilter (A.unwanted (remaining.map Prod.fst) p.1) values),
        den*((A.unwanted (remaining.map Prod.fst) p.1).map (fun r=>p.1-r)).prod,
        count+(A.multiplicity (remaining.map Prod.fst) p.1 : L),num,div,fuel⟩ : S.State L) := by
  induction remaining generalizing values den count with
  | nil => simp [A.unwanted,A.multiplicity,ThreeModeAnnihilator.differenceFilter]
  | cons r rs ih =>
    simp only [A.unwanted,A.multiplicity] at ih
    by_cases he : r.1=p.1
    · simp only [List.map_cons,A.unwanted,List.filter_cons,ne_eq,he,not_true_eq_false,
        decide_false,Bool.false_eq_true,ite_false,A.multiplicity,decide_true,ite_true,
        List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [Function.iterate_succ_apply]
      have hs : S.step
          (⟨roots,moments,p::pending,r::rs,
            V.table ((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+n) values,
            den,count,num,div,fuel⟩ : S.State L) =
          (⟨roots,moments,p::pending,rs,
            V.table ((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+n) values,
            den,count+1,num,div,fuel⟩ : S.State L) := by
        simp [S.step,S.root,S.desired,EOBinaryConjugateProgrammeState.scanEqual,he]
      rw [hs,ih]
      simp [add_assoc,add_comm]
    · simp only [List.map_cons,A.unwanted,List.filter_cons,ne_eq,he,not_false_eq_true,
        decide_true,ite_true,A.multiplicity,decide_false,Bool.false_eq_true,ite_false,
        List.length_cons,List.map_cons,List.prod_cons]
      rw [Function.iterate_succ_apply]
      have hs : S.step
          (⟨roots,moments,p::pending,r::rs,
            V.table (((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+1)+n) values,
            den,count,num,div,fuel⟩ : S.State L) =
          (⟨roots,moments,p::pending,rs,
            V.table ((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+n)
              (fun k=>values (k+1)-r.1*values k),
            den*(p.1-r.1),count,num,div,fuel⟩ : S.State L) := by
        simp only [S.step,S.root,S.desired,List.getD_cons_zero,List.tail_cons,
          List.cons_ne_nil,ite_false,he,EOBinaryConjugateProgrammeState.scanDifferent]
        rw [show ((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+1)+n=
          ((List.filter (fun r=>decide (r≠p.1)) (rs.map Prod.fst)).length+n)+1 by omega,
          V.difference_table]
      rw [hs,ih]
      simp only [mul_assoc]
      rfl

omit [Field L] in
/-- The prefix has the same contents as the physical query writer's range map. -/
theorem table_eq_range (n : ℕ) (values : ℕ→L) :
    V.table n values=(List.range n).map values := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [V.table]

@[simp] theorem table_head (n : ℕ) (values : ℕ→L) (hn : 0<n) :
    (V.table n values).getD 0 0=values 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp [V.table]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
