import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationReduction

/-! Every balanced complementary row has an actual pure, two-block or dense
continuation. With exactly two live middle entries, two literal copies and
two native edges produce a dense row without any cancellation or extra gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSelect
open Holant Holant.Algebraic Holant.Complexity
namespace T
export GlobalCloseCompletionComplementQ4Templates (reindex connect connect_network)
end T
namespace S
export GlobalCloseCompletionComplementQ4Series (row connected)
end S
namespace R
export GlobalCloseCompletionComplementQ4ClassificationReduction (swap_bc swap_bd)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
local instance : CharZero K:=Algebra.charZero_of_charZero ℚ K
variable (H : (i : Fin s)→Signature K (arity i.val))

structure Dense where
  graph : NativeAntiTargetSource.Output H 4
  a : K
  b : K
  c : K
  d : K
  first : a≠0
  second : b≠0
  third : c≠0
  fourth : d≠0
  form : graph.network.denote=S.row a b c d

structure Single where
  graph : NativeAntiTargetSource.Output H 4
  a : K
  b : K
  first : a≠0
  second : b≠0
  form : graph.network.denote=S.row a b 0 0

inductive Output : Type 1 where
  | pure (graph : NativeAntiTargetSource.Output H 4) (a : K) (nonzero : a≠0)
      (form : graph.network.denote=S.row a 0 0 0)
  | single (result : Single H)
  | dense (result : Dense H)

theorem bc_value (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
    (form : N.network.denote=S.row a b c d) :
    (T.reindex H N (Equiv.swap 1 2)).network.denote=S.row a c b d := by
  change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network (Equiv.swap 1 2)).denote=_
  rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,R.swap_bc]

theorem bd_value (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
    (form : N.network.denote=S.row a b c d) :
    (T.reindex H N (Equiv.swap 1 3)).network.denote=S.row a d c b := by
  change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network (Equiv.swap 1 3)).denote=_
  rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,R.swap_bd]

def densify (N : NativeAntiTargetSource.Output H 4) (a c d : K)
    (form : N.network.denote=S.row a 0 c d) (ha : a≠0) (hc : c≠0) (hd : d≠0) : Dense H where
  graph:=T.connect H N (T.reindex H N (Equiv.swap 1 2))
  a:=a*c
  b:=a^2
  c:=c*d
  d:=d^2
  first:=mul_ne_zero ha hc
  second:=pow_ne_zero _ ha
  third:=mul_ne_zero hc hd
  fourth:=pow_ne_zero _ hd
  form:=by
    rw [T.connect_network,S.connected _ _ _ _ _ _ _ _ _ _ form (bc_value H N a 0 c d form)]
    simp only [zero_mul,mul_zero,add_zero,zero_add,pow_two]

def produce (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
    (form : N.network.denote=S.row a b c d) (ha : a≠0) : Output H := by
  classical
  by_cases hb : b=0
  · subst b
    by_cases hc : c=0
    · subst c
      by_cases hd : d=0
      · subst d
        exact .pure N a ha form
      · exact .single ⟨T.reindex H N (Equiv.swap 1 3),a,d,ha,hd,bd_value H N a 0 0 d form⟩
    · by_cases hd : d=0
      · subst d
        exact .single ⟨T.reindex H N (Equiv.swap 1 2),a,c,ha,hc,bc_value H N a 0 c 0 form⟩
      · exact .dense (densify H N a c d form ha hc hd)
  · by_cases hc : c=0
    · subst c
      by_cases hd : d=0
      · subst d
        exact .single ⟨N,a,b,ha,hb,form⟩
      · exact .dense (densify H (T.reindex H N (Equiv.swap 1 2)) a b d
          (bc_value H N a b 0 d form) ha hb hd)
    · by_cases hd : d=0
      · subst d
        exact .dense (densify H (T.reindex H N (Equiv.swap 1 3)) a c b
          (bd_value H N a b c 0 form) ha hc hb)
      · exact .dense ⟨N,a,b,c,d,ha,hb,hc,hd,form⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSelect
end
