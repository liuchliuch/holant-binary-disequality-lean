import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeGraphOperations

/-! Four physical copies of a native graph have signed incidence four in
every logical column. Compression therefore supplies its literal fourth
power on paired outputs, even when that fourth power is non-Product. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductFourth
open Holant
open scoped BigOperators
namespace T
export GlobalCloseCompletionComplementQ4Templates (tensor)
export Holant.Complexity.BinaryInterpolation.Chains (tensor_denote)
end T
namespace S
def signedWord {n m : ℕ} (base : Fin n→Bool) (p : Fin n→Bool⊕Fin m)
    (z : Fin m→Bool) : Fin n→Bool:=fun i=>base i ^^ Sum.elim id z (p i)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {n : ℕ}

def ports : Fin ((n+n)+(n+n))→Bool⊕Fin n:=
  Fin.addCases (Fin.addCases Sum.inr Sum.inr) (Fin.addCases Sum.inr Sum.inr)
def word (z : Fin n→Bool) : Fin ((n+n)+(n+n))→Bool:=
  Fin.addCases (Fin.addCases z z) (Fin.addCases z z)

private theorem addCases_addNat {α : Type*} (u v : Fin n→α) (j : Fin n) :
    Fin.addCases u v (j.addNat n)=v j := by
  have e : j.addNat n=Fin.natAdd n j:=by ext;exact Nat.add_comm _ _
  rw [e,Fin.addCases_right]

theorem signed_word (z : Fin n→Bool) :
    S.signedWord (fun _=>false) ports z=word z := by
  funext i
  obtain ⟨j,rfl⟩:=(finSumFinEquiv : Fin (n+n)⊕Fin (n+n)≃Fin ((n+n)+(n+n))).surjective i
  cases j with
  | inl j=>
    obtain ⟨k,rfl⟩:=(finSumFinEquiv : Fin n⊕Fin n≃Fin (n+n)).surjective j
    cases k <;> simp [S.signedWord,ports,word,addCases_addNat]
  | inr j=>
    obtain ⟨k,rfl⟩:=(finSumFinEquiv : Fin n⊕Fin n≃Fin (n+n)).surjective j
    cases k <;> simp [S.signedWord,ports,word,addCases_addNat]

def charge {k : ℕ} (base : Fin k→Bool) (p : Fin k→Bool⊕Fin n) (j : Fin n) : ℤ:=
  ∑i,if p i=Sum.inr j then (if base i then -1 else 1) else 0

theorem column (j : Fin n) : charge (fun _=>false) ports j=4 := by
  classical
  simp only [charge,Fin.sum_univ_add,ports,Fin.addCases_left,Fin.addCases_right,
    Bool.false_eq_true,ite_false,Sum.inr.injEq]
  simp

theorem divisible (j : Fin n) : charge (fun _=>false) ports j%4=0 := by
  rw [column]
  norm_num

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H n)

def output : NativeAntiTargetSource.Output H ((n+n)+(n+n)):=
  T.tensor H (T.tensor H N N) (T.tensor H N N)

theorem value (z : Fin n→Bool) :
    (output H N).network.denote (S.signedWord (fun _=>false) ports z)=N.network.denote z^4 := by
  rw [signed_word]
  change (Holant.Complexity.BinaryInterpolation.Chains.tensor
    (Holant.Complexity.BinaryInterpolation.Chains.tensor N.network N.network)
    (Holant.Complexity.BinaryInterpolation.Chains.tensor N.network N.network)).denote (word z)=_
  simp [T.tensor_denote,Signature.tensor,Tensor.reindex,Tensor.tensor,word,addCases_addNat]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductFourth
end
