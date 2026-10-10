import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeWords
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeSigned
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeOperations

/-! Every positive signed equality of charge zero modulo four is an actual
native-X graph over the supplied Eq4 and X graphs, with exact unit weights. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSynthesis
open Holant Holant.Complexity
namespace S
export NoIPureMergeSigned (row reindex attach)
end S
namespace W
export NoIPureMergeWords (Legal legal_reduce legal_reindex order)
end W
namespace G
export NoIPureMergeOperations (connect reindex)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option Elab.async false

def balanceOrder (j : Fin 6) : Equiv.Perm (Fin 4) where
  toFun := ![![0,1,2,3],![0,2,1,3],![0,3,1,2],![1,2,0,3],![1,3,0,2],![2,3,0,1]] j
  invFun := ![![0,1,2,3],![0,2,1,3],![0,2,3,1],![2,0,1,3],![2,0,3,1],![2,3,0,1]] j
  left_inv := by fin_cases j <;> decide
  right_inv := by fin_cases j <;> decide

theorem four_classify : ∀ w : Fin 4 → Bool, W.Legal w →
    w = (fun _ => false) ∨ w = (fun _ => true) ∨
      ∃ j : Fin 6, (fun i => w (balanceOrder j i)) = ![false,false,true,true] := by
  unfold W.Legal
  decide

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (arity i.val))
variable (Q : NativeAntiTargetSource.Output H 4) (X : NativeAntiTargetSource.Output H 2)
variable (qform : Q.network.denote = Holant.EightVertex.ProductAnchor.equalityFour)
variable (xform : X.network.denote = fun x => Signature.disequality (x 0) (x 1))

theorem row_complement {n : ℕ} (w : Fin n → Bool) :
    S.row (K:=K) (fun i => !(w i)) = S.row w := by
  funext x
  simp only [S.row, Bool.not_not]
  exact add_comm _ _

theorem eq4_row : (Holant.EightVertex.ProductAnchor.equalityFour : Signature K 4) =
    S.row (fun _ => false) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour, S.row, funext_iff,
      Fin.forall_fin_succ,h0,h1,h2,h3]

include qform in
theorem balanced_value : (G.connect H Q Q).network.denote = S.row ![false,false,true,true] := by
  funext x
  rw [NoIPureMergeOperations.connect_network,
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork.connect_denote,
    qform]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork.term,
      Holant.EightVertex.ProductAnchor.equalityFour, S.row, funext_iff,
      Fin.forall_fin_succ,h0,h1,h2,h3]

theorem two_row (w : Fin 2 → Bool) (legal : W.Legal w) :
    (fun x => Signature.disequality (x 0) (x 1) : Signature K 2) = S.row w := by
  have hw : w = ![w 0,w 1] := by funext i; fin_cases i <;> rfl
  rw [hw] at legal ⊢
  cases h0 : w 0 <;> cases h1 : w 1
  all_goals
    unfold W.Legal charge weight at legal
    rw [Fin.sum_univ_two] at legal
    norm_num [h0,h1] at legal
  all_goals
    funext x
    cases hx0 : x 0 <;> cases hx1 : x 1 <;>
      simp [Signature.disequality,S.row,funext_iff,Fin.forall_fin_succ,h0,h1,hx0,hx1]

theorem reindex_value {n : ℕ} (N : NativeAntiTargetSource.Output H n) (w : Fin n → Bool)
    (form : N.network.denote = S.row w) (e : Equiv.Perm (Fin n)) :
    (G.reindex H N e).network.denote = S.row (fun i => w (e.symm i)) := by
  change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network e).denote = _
  rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,S.reindex]

include qform xform in
theorem exists_graph : ∀ n : ℕ, 0 < n → ∀ w : Fin n → Bool, W.Legal w →
    ∃ N : NativeAntiTargetSource.Output H n, N.network.denote = S.row w := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro positive w legal
    by_cases small : n ≤ 4
    · have parity : n % 2 = 0 := by
        have hh := legal
        unfold W.Legal charge at hh
        omega
      have cases : n = 2 ∨ n = 4 := by omega
      rcases cases with rfl | rfl
      · exact ⟨X,xform.trans (two_row w legal)⟩
      · rcases four_classify w legal with h | h | ⟨j,h⟩
        · subst w; exact ⟨Q,qform.trans eq4_row⟩
        · subst w
          refine ⟨Q,qform.trans ?_⟩
          rw [eq4_row, ←row_complement (fun _ : Fin 4 => false)]
          rfl
        · let B := G.connect H Q Q
          refine ⟨G.reindex H B (balanceOrder j),?_⟩
          rw [reindex_value H B _ (balanced_value H Q qform)]
          congr 1
          funext i
          simpa using (congrFun h ((balanceOrder j).symm i)).symm
    · obtain ⟨m,rfl⟩ : ∃ m, n = m+3 := ⟨n-3,by omega⟩
      obtain ⟨b,e,t,ordered⟩ := W.order (by omega) w
      have reduced : W.Legal (Fin.cons (!b) t) := W.legal_reduce t b (by
        rw [←ordered]
        exact (W.legal_reindex w e).mpr legal)
      obtain ⟨N,nform⟩ := ih (m+1) (by omega) (by omega) (Fin.cons (!b) t) reduced
      let M := NoIPureMergeAttach.output H N Q
      have mform : M.network.denote = S.row (Fin.addCases t (fun _ : Fin 3 => b)) :=
        S.attach H N Q t b nform qform
      refine ⟨G.reindex H M e,?_⟩
      rw [reindex_value H M _ mform]
      congr 1
      funext i
      simpa using (congrFun ordered (e.symm i)).symm

def produce {n : ℕ} (positive : 0 < n) (w : Fin n → Bool) (legal : W.Legal w) :
    NativeAntiTargetSource.Output H n := (exists_graph H Q X qform xform n positive w legal).choose

theorem value {n : ℕ} (positive : 0 < n) (w : Fin n → Bool) (legal : W.Legal w) :
    (produce H Q X qform xform positive w legal).network.denote = S.row w :=
  (exists_graph H Q X qform xform n positive w legal).choose_spec

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSynthesis
end
