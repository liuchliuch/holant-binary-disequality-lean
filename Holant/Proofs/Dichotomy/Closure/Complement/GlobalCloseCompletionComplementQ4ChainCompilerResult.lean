import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerRecovery
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryOrder
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NodeValues
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Batch

/-! The exact executable batch result equals the retained-table target Holant
value, in both separated-mode and support-projector interpolation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerResult
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerSemantics (Source slot)
end C
namespace L
export GlobalCloseCompletionComplementQ4ChainCompilerRecoveryNetwork (answer value)
end L
namespace R
export GlobalCloseCompletionComplementQ4ChainCompilerRecovery (separated support zero_samples)
export GlobalCloseCompletionComplementQ4ChainCompilerRecoveryOrder (reverse)
end R
namespace B
export GlobalCloseCompletionComplementQ4Batch (result resultState initial prepare answered preprocessing context roots target
  sampleCount queries finish oldTables)
end B
namespace I
export GlobalCloseCompletionComplementQ4IterationMachine (fold_value values_reverse)
end I
namespace D
export GlobalCloseCompletionComplementQ4Differences (samples processList factor)
end D
namespace V
export GlobalCloseCompletionComplementQ4NodeValues (projector_roots support_roots)
export GlobalCloseCompletionComplementQ4DifferenceRecovery (roots_length)
end V
namespace U
export GlobalCloseCompletionComplementQ4SupportBasis (filled support)
export GlobalCloseCompletionComplementQ4SupportRecovery (roots_length)
end U
namespace P
export GlobalCloseCompletionComplementQ4Basis (basis)
export GlobalCloseCompletionComplementQ4Series (ofSpectrum)
export GlobalCloseCompletionComplementQ4Nodes (Separated)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H 4) (q : C.Source H N)

theorem evaluate_base (x : ExactSignatureTables.Input s 1 a) :
    (NativeAntiTargetSource.base H F).evaluate F x=
      (x.val.realize x.property H (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  congr 2 <;> funext i x <;> simp [NativeAntiTargetSource.base]

theorem samples_range (f : ℕ→K) (start n : ℕ) :
    D.samples f start n=(List.range n).map (fun k=>f (start+k)) := by
  induction n generalizing start with
  | zero=>rfl
  | succ n ih=>simp only [D.samples,List.range_succ_eq_map,List.map_cons,List.map_map,
      ih,Nat.add_zero,Function.comp_def,Nat.add_succ,Nat.succ_add]

theorem answers_list (v : Fin 4→K) (mode : Bool) (j : Fin 4) :
    ((B.queries H N v mode j q).map ((B.oldTables F H).evaluate F))=
      D.samples (L.answer H N q) 0 (B.sampleCount H N v mode j q) := by
  rw [samples_range]
  simp only [B.queries,List.map_map,Nat.zero_add]
  apply List.map_congr_left
  intro k _
  exact evaluate_base F H _

theorem head_getD (xs : List K) : xs.getD 0 0=xs.headD 0 := by cases xs <;> rfl

theorem result_false (v : Fin 4→K) (j : Fin 4) :
    B.result F H N v false j q=
      (D.processList (B.roots H N v false j q)
        (D.samples (L.answer H N q) 0 (B.sampleCount H N v false j q))).headD 0 /
        (v j^(occurrences s q.val)*D.factor (B.roots H N v false j q) (v j^(occurrences s q.val))) := by
  simp only [B.result,B.resultState,B.initial,B.answered,B.preprocessing,OracleBatch.answers,
    B.prepare,B.context,B.target,B.finish,Bool.false_eq_true,ite_false,I.fold_value,I.values_reverse,R.reverse]
  rw [answers_list,head_getD]

theorem result_true (v : Fin 4→K) (j : Fin 4) :
    B.result F H N v true j q=
      -(D.processList (B.roots H N v true j q)
        (0::D.samples (L.answer H N q) 0 (B.sampleCount H N v true j q))).headD 0 /
        D.factor (B.roots H N v true j q) 0 := by
  simp only [B.result,B.resultState,B.initial,B.answered,B.preprocessing,OracleBatch.answers,
    B.prepare,B.context,B.target,B.finish,ite_true,I.fold_value,I.values_reverse,R.reverse,one_mul]
  rw [answers_list,head_getD]

theorem separated (v : Fin 4→K) (form : N.network.denote=P.ofSpectrum v)
    (j : Fin 4) (guard : P.Separated v j) :
    B.result F H N v false j q=L.value H N q (P.basis j) := by
  rw [result_false]
  simp only [B.sampleCount,B.roots,V.projector_roots,V.roots_length,Bool.false_eq_true,ite_false]
  exact R.separated H N q v form j guard

theorem support (v : Fin 4→K) (form : N.network.denote=P.ofSpectrum v) (j : Fin 4) :
    B.result F H N (U.filled v) true j q=L.value H N q (P.ofSpectrum (U.support v)) := by
  rw [result_true]
  simp only [B.sampleCount,B.roots,V.support_roots,U.roots_length,ite_true,Nat.add_zero]
  rw [←R.zero_samples]
  exact R.support H N q v form

theorem base_value (f : Signature K 4) :
    (NativeAntiTargetSource.base (C.slot H N f) F).evaluate F q=L.value H N q f :=
  evaluate_base F (C.slot H N f) q

theorem separated_evaluate (v : Fin 4→K) (form : N.network.denote=P.ofSpectrum v)
    (j : Fin 4) (guard : P.Separated v j) :
    (NativeAntiTargetSource.base (C.slot H N (P.basis j)) F).evaluate F q=B.result F H N v false j q := by
  rw [base_value,separated F H N q v form j guard]

theorem support_evaluate (v : Fin 4→K) (form : N.network.denote=P.ofSpectrum v) (j : Fin 4) :
    (NativeAntiTargetSource.base (C.slot H N (P.ofSpectrum (U.support v))) F).evaluate F q=
      B.result F H N (U.filled v) true j q := by
  rw [base_value,support F H N q v form j]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerResult
end
