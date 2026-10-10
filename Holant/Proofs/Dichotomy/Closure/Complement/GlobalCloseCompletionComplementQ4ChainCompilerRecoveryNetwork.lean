import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerSemantics
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4SupportBasis
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4SupportRecovery

/-! The marked vertices are selected from the original literal label stream.
Dependent port transports preserve each Bell component and the full old table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryNetwork
open Holant Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.BinaryInterpolation
open scoped BigOperators
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerSemantics (Source arity slot slot_new actual sample query)
end C
namespace R
export GlobalCloseCompletionComplementQ4NetworkRecovery (network)
end R
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum)
end S
namespace B
export GlobalCloseCompletionComplementQ4Basis (basis linear)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : NativeAntiTargetSource.Output H 4)
variable (q : C.Source H N)
abbrev original:=q.val.realize q.property (C.actual H N) (fun _ : Fin 1=>Signature.disequality)
abbrev marked:=RawPolynomial.marked q.val s
abbrev lifted (B : Fin 4→Signature K 4) (j : Fin 4) (p : Fin (original H N q).shape.vertices):=
  C.slot H N (B j) (q.val.signatureLabel q.property p)
def value (f : Signature K 4):=(q.val.realize q.property (C.slot H N f) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0

theorem marked_count : Fintype.card (marked H N q)=FixedGadgetSubstitution.occurrences s q.val := by
  rw [Fintype.card_coe,RawPolynomial.marked_card]

theorem cast_linear {m : ℕ} (h : 4=m) (f : Signature K 4) (B : Fin 4→Signature K 4)
    (u : Fin 4→K) (form : ∀x,f x=∑j,u j*B j x) (x : Fin m→Bool) :
    OriginalTables.castSignature h f x=∑j,u j*OriginalTables.castSignature h (B j) x := by
  subst m
  exact form x

theorem slot_linear (f : Signature K 4) (B : Fin 4→Signature K 4) (u : Fin 4→K)
    (form : ∀x,f x=∑j,u j*B j x) (i : Fin (s+1)) (hi : i.val=s) (x) :
    C.slot H N f i x=∑j,u j*C.slot H N (B j) i x := by
  have ie : i=(⟨s,Nat.lt_succ_self s⟩ : Fin (s+1)):=Fin.ext hi
  subst i
  simp only [C.slot,dif_pos rfl]
  exact cast_linear _ f B u form x

theorem network_value (f : Signature K 4) (B : Fin 4→Signature K 4) (u : Fin 4→K)
    (form : ∀x,f x=∑j,u j*B j x) :
    (R.network (original H N q) (marked H N q) (lifted H N q B) u).denote Fin.elim0=value H N q f := by
  apply congrFun (Network.denote_congr (q.val.shape q.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro p x
    change (if p∈marked H N q then ∑j,u j*C.slot H N (B j) (q.val.signatureLabel q.property p) x
      else C.actual H N (q.val.signatureLabel q.property p) x)=C.slot H N f (q.val.signatureLabel q.property p) x
    by_cases hp : (q.val.vertices.get p).1=s
    · have member : p∈marked H N q:=by
        simp only [marked,RawPolynomial.marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact hp
      rw [if_pos member]
      exact (slot_linear H N f B u form (q.val.signatureLabel q.property p) hp x).symm
    · have member : p∉marked H N q:=by
        simp only [marked,RawPolynomial.marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact hp
      rw [if_neg member]
      simp only [C.slot,RawClosedNetwork.signatureLabel,dif_neg hp]
  · intros;rfl

theorem right_value (f : Signature K 4) :
    (rightNetwork (original H N q) (marked H N q)
      (fun p=>C.slot H N f (q.val.signatureLabel q.property p))).denote Fin.elim0=value H N q f := by
  apply congrFun (Network.denote_congr (q.val.shape q.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro p x
    change (if p∈marked H N q then C.slot H N f (q.val.signatureLabel q.property p) x
      else C.actual H N (q.val.signatureLabel q.property p) x)=C.slot H N f (q.val.signatureLabel q.property p) x
    by_cases hp : (q.val.vertices.get p).1=s
    · have member : p∈marked H N q:=by
        simp only [marked,RawPolynomial.marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact hp
      rw [if_pos member]
    · have member : p∉marked H N q:=by
        simp only [marked,RawPolynomial.marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact hp
      rw [if_neg member]
      simp only [C.slot,RawClosedNetwork.signatureLabel,dif_neg hp]
  · intros;rfl

def answer (k : ℕ):=((C.query H N (q,k)).val.realize (C.query H N (q,k)).property
  H (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0

theorem power_answer (v : Fin 4→K) (form : N.network.denote=S.ofSpectrum v) (k : ℕ) :
    (R.network (original H N q) (marked H N q) (lifted H N q B.basis)
      (fun i=>v i^(k+1))).denote Fin.elim0=answer H N q k := by
  rw [network_value H N q (S.ofSpectrum (fun i=>v i^(k+1))) B.basis _ (B.linear _)]
  exact (C.sample H N v form (q,k)).symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryNetwork
end
