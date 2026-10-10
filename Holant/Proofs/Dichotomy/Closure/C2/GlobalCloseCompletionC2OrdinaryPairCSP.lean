import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPair
import Holant.Proofs.Hardness.BinaryCSPProgrammeNative
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion

/-! Literal equality-pair q4 vertices implement unsigned binary CSPs through
the existing occurrence-cycle query compiler. Each structural edge is I;
declared unused variables retain exactly their computed factor two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairCSP
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace C
export EOBinaryPlaneCycles (Slot incidence shape assignments assignment_row Consistent weight value)
end C
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair)
end P
namespace R
export EOBinaryPlaneRaw (scope value query)
end R
namespace Q
export BinaryCSPProgrammeValidated (Input inputEncoding query queryComputes)
end Q
namespace N
export BinaryCSPProgrammeNative (pre preprocessing post unusedComputes)
end N
namespace U
export BinaryCSPProgrammeUnused (unused unused_eq)
end U
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def network {n : ℕ} (M : Signature K 4) (next : Equiv.Perm (C.Slot n)) : Network K 0 where
  shape := C.shape next
  vertex _ := M
  edge _ := Signature.equality

theorem edge_product {n : ℕ} (a b : C.Slot n→Bool) :
    (∏e,Signature.equality (K:=K) (a e) (b e))=if b=a then 1 else 0 := by
  classical
  by_cases h : b=a
  · rw [if_pos h,h]
    apply Finset.prod_eq_one
    intro e _
    cases a e <;> rfl
  · rw [if_neg h]
    obtain ⟨e,he⟩ : ∃e,b e≠a e := by simpa only [funext_iff,not_forall] using h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    cases ha : a e <;> cases hb : b e <;> simp_all [Signature.equality]

theorem ordinary_sum {n : ℕ} (M : Signature K 4) (next : Equiv.Perm (C.Slot n)) :
    (network M next).denote Fin.elim0=∑a : C.Slot n→Bool,∏v : Fin n,
      M ![a (C.incidence v 0),a (next (C.incidence v 0)),a (C.incidence v 1),a (next (C.incidence v 1))] := by
  classical
  unfold Network.denote
  change (∑z : (C.Slot n×Bool)→Bool,
    (∏v : Fin n,M ((C.shape next).assignment Fin.elim0 z v))*
      ∏e : C.Slot n,Signature.equality (z (e,false)) (z (e,true)))=_
  rw [←(C.assignments n).symm.sum_comp,Fintype.sum_prod_type]
  simp only [C.assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  rw [C.assignment_row]
  rfl

theorem denote_pair {n : ℕ} (f : Signature K 2) (next : Equiv.Perm (C.Slot n)) :
    (network (P.pair f) next).denote Fin.elim0=C.value f next := by
  classical
  rw [ordinary_sum]
  unfold C.value
  apply Finset.sum_congr rfl
  intro a _
  simp only [P.pair,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  by_cases h : C.Consistent next a
  · rw [if_pos h]
    unfold C.weight
    apply Finset.prod_congr rfl
    intro v _
    rw [if_pos ⟨h _,h _⟩]
    rfl
  · rw [if_neg h]
    obtain ⟨e,he⟩ : ∃e,a (next e)≠a e := by simpa only [C.Consistent,not_forall] using h
    let p : Fin n×Fin 2 := finProdFinEquiv.symm e
    have hp : C.incidence p.1 p.2=e := finProdFinEquiv.apply_symm_apply e
    apply Finset.prod_eq_zero (Finset.mem_univ p.1)
    apply if_neg
    intro hpair
    have hi : p.2=0 ∨ p.2=1 := by omega
    rcases hi with hi|hi
    · exact he (hp ▸ (hi ▸ hpair.1))
    · exact he (hp ▸ (hi ▸ hpair.2))

theorem query_denote {n : ℕ} (M : Signature K 4) (next : Equiv.Perm (C.Slot n)) :
    ((EOBinaryPlaneRecords.query next).val.realize (EOBinaryPlaneRecords.query next).property
      (fun _=>M) (fun _=>Signature.equality)).denote Fin.elim0=(network M next).denote Fin.elim0 :=
  (EOBinaryPlaneRecords.labels next).denote_serialize (fun _=>M) (fun _=>Signature.equality)

theorem raw_value (f : Signature K 2) (r : BinaryCSPProgrammeCore.Raw) (hr : r.WellFormed) :
    R.value f r=(2:K)^EOBinaryPlaneRawValue.unused r hr*
      ((R.query r hr).val.realize (R.query r hr).property (fun _=>P.pair f)
        (fun _=>Signature.equality)).denote Fin.elim0 := by
  rw [EOBinaryPlaneRaw.value_scope f r hr,GeneralCSPUnused.scan_cycle_value]
  rw [R.query,query_denote,denote_pair]
  rfl

variable [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree) (M : Signature K 4) (f : Signature K 2)
def tables := QuaternaryOrdinaryCompanion.tables (a:=fun _=>4) F (fun _ : Fin 1=>M)
def targetValue : O.TargetInput→K := (tables F M).evaluate F

theorem target_semantics (q : O.TargetInput) : targetValue F M q=
    (q.val.realize q.property (fun _=>M) (fun _=>Signature.equality)).denote Fin.elim0 := by
  simp only [targetValue,ExactSignatureTables.evaluate_eq_decoded,tables,
    QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]

theorem query_value (hm : M=P.pair f) (r : Q.Input) :
    R.value f r.val=targetValue F M (Q.query r)*(2:K)^U.unused r.val := by
  rw [raw_value _ r.val r.property,target_semantics,hm,U.unused_eq]
  exact mul_comm _ _

def controlled (hm : M=P.pair f) : LengthControlledOracleReduction
    Q.inputEncoding F.encoding O.targetEncoding F.encoding (fun r=>R.value f r.val) (targetValue F M) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch N.pre (N.post F)
    ((tables F M).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [query_value F M f hm r]
  simpa only [N.preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,targetValue] using
    reduction.reduction.correct oracle ho r


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairCSP
end
