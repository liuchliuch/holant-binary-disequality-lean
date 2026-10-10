import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryNetwork

/-! Shrinking-list recovery from actual original-H oracle queries. No caller
supplies a spectral expansion, graph interpretation, or query identity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecovery
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerSemantics (Source sample)
end C
namespace L
export GlobalCloseCompletionComplementQ4ChainCompilerRecoveryNetwork
  (original marked lifted value answer marked_count network_value right_value power_answer)
end L
namespace B
export GlobalCloseCompletionComplementQ4Basis (basis)
end B
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum)
end S
namespace P
export GlobalCloseCompletionComplementQ4DifferenceRecovery (roots roots_length recover)
export GlobalCloseCompletionComplementQ4Nodes (Separated)
end P
namespace U
export GlobalCloseCompletionComplementQ4SupportBasis (filled masked support filled_nonzero positive zero)
export GlobalCloseCompletionComplementQ4SupportRecovery (roots roots_length recover)
end U
namespace R
export GlobalCloseCompletionComplementQ4NetworkRecovery (network)
end R
namespace D
export GlobalCloseCompletionComplementQ4Differences (processList samples factor)
export GlobalCloseCompletionComplementQ4ZeroExtrapolation (zeroed)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : NativeAntiTargetSource.Output H 4)
variable (q : C.Source H N) (v : Fin 4→K) (form : N.network.denote=S.ofSpectrum v)

include form in
theorem separated (j : Fin 4) (guard : P.Separated v j) :
    (D.processList (P.roots v j (occurrences s q.val))
      (D.samples (L.answer H N q) 0 ((occurrences s q.val+1)^4+1))).headD 0 /
      (v j^(occurrences s q.val)*D.factor (P.roots v j (occurrences s q.val)) (v j^(occurrences s q.val)))=
      L.value H N q (B.basis j) := by
  have result:=P.recover (L.original H N q) (L.marked H N q) (L.lifted H N q B.basis) v j guard Fin.elim0
  simp_rw [L.power_answer H N q v form] at result
  rw [L.right_value] at result
  erw [L.marked_count H N q,P.roots_length] at result
  exact result

include form in
theorem support_power (k : ℕ) :
    (R.network (L.original H N q) (L.marked H N q) (L.lifted H N q (U.masked v))
      (fun i=>(U.filled v i)^(k+1))).denote Fin.elim0=L.answer H N q k := by
  rw [L.network_value H N q (S.ofSpectrum (fun i=>v i^(k+1))) (U.masked v) _ (U.positive v k)]
  exact (C.sample H N v form (q,k)).symm

def zeroAnswers (k : ℕ) : K:=if k=0 then 0 else L.answer H N q (k-1)

theorem positive_samples (start n : ℕ) :
    D.samples (zeroAnswers H N q) (start+1) n=D.samples (L.answer H N q) start n := by
  induction n generalizing start with
  | zero=>rfl
  | succ n ih=>simp only [D.samples,zeroAnswers,Nat.add_one_ne_zero,ite_false,Nat.add_one_sub_one,ih]

theorem zero_samples (n : ℕ) :
    D.samples (zeroAnswers H N q) 0 (n+1)=0::D.samples (L.answer H N q) 0 n := by
  rw [D.samples,positive_samples]
  rfl

include form in
theorem zeroed_answers :
    D.zeroed (fun k=>(R.network (L.original H N q) (L.marked H N q)
      (L.lifted H N q (U.masked v)) (fun i=>(U.filled v i)^k)).denote Fin.elim0)=zeroAnswers H N q := by
  funext k
  cases k with
  | zero=>simp [D.zeroed,zeroAnswers]
  | succ k=>simpa only [D.zeroed,zeroAnswers,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one] using
      support_power H N q v form k

include form in
/-- Exponent zero uses one arithmetic leading zero and D positive physical
samples. Every retained old signature remains in its original ordered slot. -/
theorem support :
    -(D.processList (U.roots (U.filled v) (occurrences s q.val))
      (D.samples (zeroAnswers H N q) 0 ((occurrences s q.val+1)^4+1))).headD 0 /
      D.factor (U.roots (U.filled v) (occurrences s q.val)) 0=
      L.value H N q (S.ofSpectrum (U.support v)) := by
  have result:=U.recover (L.original H N q) (L.marked H N q) (L.lifted H N q (U.masked v))
    (U.filled v) (U.filled_nonzero v) Fin.elim0
  rw [zeroed_answers H N q v form] at result
  erw [L.marked_count H N q,U.roots_length] at result
  refine result.trans ?_
  apply L.network_value H N q (S.ofSpectrum (U.support v)) (U.masked v) (fun _=>1)
  intro x
  simpa using U.zero v x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecovery
end
