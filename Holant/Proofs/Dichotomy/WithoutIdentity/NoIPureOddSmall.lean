import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddTriple
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoWords

/-! The terminal odd two-corner resources, at arity one or three, produce
an actual full unary with the same original native dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSmall
open Holant
namespace O
export NativeAntiTargetSource (Output)
end O
namespace G
export GlobalCloseCompletionComplementQ4Templates (reindex contract)
end G
namespace W
export NoIPureChargeTwoWords (row opposite reindex loop_row)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))

theorem one_full (mask : Fin 1→Bool) (a b : K) (an : a≠0) (bn : b≠0) :
    ∀x,W.row mask a b x≠0 := by
  intro x
  cases hx:x 0 <;>cases hs:mask 0 <;>
    simp [W.row,W.opposite,funext_iff,Fin.forall_fin_succ,hx,hs,an,bn]

theorem ternary (Q : O.Output H 4) (p q : K) (pn : p≠0) (qn : q≠0)
    (qform : Q.network.denote=NoIPureEqualityCap.pure p q)
    (R : O.Output H 3) (mask : Fin 3→Bool) (a b : K) (an : a≠0) (bn : b≠0)
    (form : R.network.denote=W.row mask a b) :
    ∃U : O.Output H 1,U.network.denote (fun _=>false)≠0 ∧ U.network.denote (fun _=>true)≠0 := by
  classical
  by_cases constant:∀i,mask i=mask 0
  · have equal:mask=(fun _=>mask 0):=funext constant
    cases hb:mask 0
    · have rf:R.network.denote=NoIPureOddTriple.pure a b:=by
        rw [form,equal,hb]
        rfl
      exact ⟨NoIPureOddTriple.output H R Q,NoIPureOddTriple.full H R Q a b p q an bn pn qn rf qform⟩
    · have rf:R.network.denote=NoIPureOddTriple.pure b a:=by
        rw [form,equal,hb]
        funext x
        cases h0:x 0 <;>cases h1:x 1 <;>cases h2:x 2 <;>
          simp [W.row,W.opposite,NoIPureOddTriple.pure,funext_iff,Fin.forall_fin_succ,h0,h1,h2]

      exact ⟨NoIPureOddTriple.output H R Q,NoIPureOddTriple.full H R Q b a p q bn an pn qn rf qform⟩
  · have pair:∃e : Equiv.Perm (Fin 3),mask (e 0)≠mask (e 1):=by
      by_cases first:mask 0=mask 1
      · have second:mask 0≠mask 2:=by
          intro h
          apply constant
          intro i
          fin_cases i <;>simp_all
        exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def] using second⟩
      · exact ⟨Equiv.refl _,first⟩
    obtain ⟨e,opposite⟩:=pair
    let bit:=mask (e 0)
    let tail:Fin 1→Bool:=fun _=>mask (e 2)
    have eqn:(fun i=>mask (e i))=Fin.cons bit (Fin.cons (!bit) tail):=by
      funext i
      fin_cases i
      · rfl
      · have h:mask (e 1)= !mask (e 0):=by
          cases h0:mask (e 0) <;>cases h1:mask (e 1) <;>simp_all
        exact h
      · rfl
    let U:=G.contract H (n:=1) (G.reindex H R e.symm)
    have value:U.network.denote=W.row tail a b:=by
      change ((Holant.Complexity.BinaryInterpolation.Chains.reindex R.network e.symm).contract Signature.disequality).denote=_
      rw [Network.denote_contract,Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,W.reindex,eqn]
      exact W.loop_row (by decide) bit tail a b
    refine ⟨U,?_,?_⟩ <;>rw [value]
    · exact one_full tail a b an bn _
    · exact one_full tail a b an bn _

theorem source {n : ℕ} (Q : O.Output H 4) (p q : K) (pn : p≠0) (qn : q≠0)
    (qform : Q.network.denote=NoIPureEqualityCap.pure p q)
    (R : O.Output H n) (mask : Fin n→Bool) (a b : K) (an : a≠0) (bn : b≠0)
    (form : R.network.denote=W.row mask a b) (odd : Odd n) (bound : n≤3) :
    ∃U : O.Output H 1,U.network.denote (fun _=>false)≠0 ∧ U.network.denote (fun _=>true)≠0 := by
  obtain ⟨k,hk⟩:=odd
  have size:n=1 ∨ n=3:=by omega
  rcases size with rfl|rfl
  · refine ⟨R,?_,?_⟩ <;>rw [form]
    · exact one_full mask a b an bn _
    · exact one_full mask a b an bn _
  · exact ternary H Q p q pn qn qform R mask a b an bn form

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSmall
end
