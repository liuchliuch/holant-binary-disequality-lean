import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZCore

/-! A nonzero GHZ triangle core is a genuine prime ternary tensor. Every
proper split has a singleton port; its rank-one minor identities contradict
the exact three cubic minors when the internal matrix is invertible. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZPrime
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace T
export GlobalCloseCompletionTernaryGHZCore (core core_minors)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K]

def PortRankOne (f : Signature K 3) (i : Fin 3) : Prop :=
  ∀x y,f x*f y=f (Function.update x i (y i))*f (Function.update y i (x i))

theorem left_one {f : Signature K 3} {l r : AnySignature K} (split : ProperSplit ⟨3,f⟩ l r)
    (one : l.1=1) : ∃i : Fin 3,PortRankOne f i := by
  let i : Fin 3:=split.ports (.inl ⟨0,by omega⟩)
  refine ⟨i,?_⟩
  intro x y
  have leftX (j : Fin l.1) : x (split.ports (.inl j))=x i := by
    have hj : j=⟨0,by omega⟩ := Fin.ext (by omega)
    rw [hj]
  have leftY (j : Fin l.1) : y (split.ports (.inl j))=y i := by
    have hj : j=⟨0,by omega⟩ := Fin.ext (by omega)
    rw [hj]
  have rightNe (j : Fin r.1) : split.ports (.inr j)≠i := by
    intro eqn
    have := split.ports.injective eqn
    cases this
  change f x*f y=f (Function.update x i (y i))*f (Function.update y i (x i))
  have equation:=split.equation
  change f = _ at equation
  rw [equation]
  simp only [leftX,leftY,Function.update_apply]
  have hu (j : Fin l.1) : split.ports (.inl j)=i := by
    congr 1
    apply congrArg Sum.inl
    apply Fin.ext
    omega
  simp only [hu,ite_true,rightNe,ite_false]
  ring

theorem split_port {f : Signature K 3} {l r : AnySignature K}
    (split : ProperSplit ⟨3,f⟩ l r) : ∃i,PortRankOne f i := by
  have sizes:=split.arity
  change l.1+r.1=3 at sizes
  have lp:=split.left_pos
  have rp:=split.right_pos
  have one : l.1=1 ∨ r.1=1 := by omega
  rcases one with left|right
  · simpa using left_one split left
  · let swapped : ProperSplit ⟨3,f⟩ r l := {
      left_pos:=split.right_pos
      right_pos:=split.left_pos
      ports:=(Equiv.sumComm (Fin r.1) (Fin l.1)).trans split.ports
      scale:=split.scale
      equation:=by rw [split.equation];funext x;simp only [Equiv.trans_apply,Equiv.sumComm_apply,Sum.swap,Sum.elim_inl,Sum.elim_inr];ring }
    simpa using left_one swapped right

theorem core_prime (a b c d : K) (det : a*d-b*c≠0) (nonzero : a≠0 ∨ d≠0) :
    Prime (⟨3,T.core a b c d⟩ : AnySignature K) := by
  constructor
  · intro zero
    rcases nonzero with ha|hd
    · have h:=congrFun zero ![false,false,false]
      exact pow_ne_zero 3 ha (by simpa [T.core] using h)
    · have h:=congrFun zero ![true,true,true]
      exact pow_ne_zero 3 hd (by simpa [T.core] using h)
  · rintro ⟨l,r,⟨split⟩⟩
    obtain ⟨i,rank⟩:=split_port split
    have minors : a^3*(b*c*d)=(a*b*c)^2 ∧
        (a*b*c)*d^3=(b*c*d)^2 ∧ a^3*d^3=(a*b*c)*(b*c*d) := by
      fin_cases i
      · have h0:=rank ![false,false,false] ![true,true,false]
        have h1:=rank ![false,false,true] ![true,true,true]
        have h2:=rank ![false,false,false] ![true,true,true]
        simpa [T.core,Function.update,pow_two] using And.intro h0 (And.intro h1 h2)
      · have h0:=rank ![false,false,false] ![true,true,false]
        have h1:=rank ![false,false,true] ![true,true,true]
        have h2:=rank ![false,false,false] ![true,true,true]
        simpa [T.core,Function.update,pow_two] using And.intro h0 (And.intro h1 h2)
      · have h0:=rank ![false,false,false] ![true,false,true]
        have h1:=rank ![false,true,false] ![true,true,true]
        have h2:=rank ![false,false,false] ![true,true,true]
        simpa [T.core,Function.update,pow_two] using And.intro h0 (And.intro h1 h2)
    have zeros:=T.core_minors a b c d det minors.1 minors.2.1 minors.2.2
    exact nonzero.elim (fun h=>h zeros.1) (fun h=>h zeros.2)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZPrime
end
