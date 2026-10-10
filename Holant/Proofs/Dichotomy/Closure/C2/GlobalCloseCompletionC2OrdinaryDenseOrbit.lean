import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryAttach
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets

/-! Exhaustive dense ordinary complementary q4 split using actual Z vertices
and original-port permutations. Either a real graph has the separating
square invariant, or a real graph is one of the two paired sign forms. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryDenseOrbit
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z paired_squares)
end T
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (attach attach_denote labels exact ordinary binary)
end A
namespace O
export Holant.Certificates.EqualityQuaternary.Klein.Orbit (site)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (z : Fin s) (literal : (⟨arity z.val,H z⟩ : AnySignature K)=⟨2,A.binary T.Z⟩)

def phase (N : Macro H 4) (i : Fin 4) : Macro H 4 where
  network := A.attach N.network i T.Z
  labels := A.labels H N.network N.labels z T.Z literal i
  exact := A.exact H N.network N.labels z T.Z literal i N.exact
  edges := A.ordinary N.network i T.Z N.edges

def phase02 (N : Macro H 4) : Macro H 4 := phase H z literal (phase H z literal N 0) 2

theorem phase02_normal (N : Macro H 4) (a b c d : K) (form : N.network.denote=T.normal a b c d) :
    (phase02 H z literal N).network.denote=T.normal a (-b) c (-d) := by
  change (A.attach (A.attach N.network 0 T.Z) 2 T.Z).denote=_
  rw [A.attach_denote,A.attach_denote,form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [O.site,T.Z,Function.update,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem swap_bc (a b c d : K) :
    Tensor.reindex (Equiv.swap 1 2) (T.normal a b c d)=T.normal a c b d := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem swap_bd (a b c d : K) :
    Tensor.reindex (Equiv.swap 1 3) (T.normal a b c d)=T.normal a d c b := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

def Paired : Prop := ∃N : Macro H 4,∃A C : K,A≠0 ∧ C≠0 ∧
  (N.network.denote=T.normal A A C C ∨ N.network.denote=T.normal A A C (-C))

def Separated : Prop := ∃N : Macro H 4,∃a b c d : K,a≠0 ∧ b≠0 ∧ c≠0 ∧ d≠0 ∧
  N.network.denote=T.normal a b c d ∧ (a^2-b^2)^2≠(c^2-d^2)^2

include literal in
theorem paired (N : Macro H 4) (a b c d : K) (ha : a≠0) (hc : c≠0)
    (form : N.network.denote=T.normal a b c d) (hab : a^2=b^2) (hcd : c^2=d^2) : Paired H := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hab.symm with h|h <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcd.symm with k|k
  · subst b; subst d
    exact ⟨N,a,c,ha,hc,Or.inl form⟩
  · subst b; subst d
    exact ⟨N,a,c,ha,hc,Or.inr form⟩
  · subst b; subst d
    refine ⟨phase02 H z literal N,a,c,ha,hc,Or.inr ?_⟩
    simpa using phase02_normal H z literal N a (-a) c c form
  · subst b; subst d
    refine ⟨phase02 H z literal N,a,c,ha,hc,Or.inl ?_⟩
    simpa using phase02_normal H z literal N a (-a) c (-c) form

include literal in
theorem split_dense (N : Macro H 4) (a b c d : K)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
    (form : N.network.denote=T.normal a b c d) : Separated H ∨ Paired H := by
  by_cases h0 : (a^2-b^2)^2≠(c^2-d^2)^2
  · exact Or.inl ⟨N,a,b,c,d,ha,hb,hc,hd,form,h0⟩
  by_cases h1 : (a^2-c^2)^2≠(b^2-d^2)^2
  · refine Or.inl ⟨N.reindex (Equiv.swap 1 2),a,c,b,d,ha,hc,hb,hd,?_,h1⟩
    rw [Macro.reindex_denote,form,swap_bc]
  by_cases h2 : (a^2-d^2)^2≠(b^2-c^2)^2
  · refine Or.inl ⟨N.reindex (Equiv.swap 1 3),a,d,c,b,ha,hd,hc,hb,?_,?_⟩
    · rw [Macro.reindex_denote,form,swap_bd]
    · intro eqn
      apply h2
      exact eqn.trans (by ring)
  right
  have pairs := T.paired_squares a b c d (not_not.mp h0) (not_not.mp h1) (not_not.mp h2) (by norm_num)
  rcases pairs with h|h|h
  · exact paired H z literal N a b c d ha hc form h.1 h.2
  · apply paired H z literal (N.reindex (Equiv.swap 1 2)) a c b d ha hb
      (by rw [Macro.reindex_denote,form,swap_bc]) h.1 h.2
  · apply paired H z literal (N.reindex (Equiv.swap 1 3)) a d c b ha hc
      (by rw [Macro.reindex_denote,form,swap_bd]) h.1 h.2.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryDenseOrbit
end
