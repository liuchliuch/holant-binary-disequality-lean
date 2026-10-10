import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNoInteractions

/-! Exact third-order coefficient identity for every small ternary factor
tree. Its three-way polynomial is invariant under the six original-port
orders and vanishes on each actual unary-by-binary split. This determines
the triple coefficients needed by the paired-q4 UPF base case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTernarySmallCubic
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K]

def cubic (f : Signature K 3) : K :=
  f ![true,true,true]*(f ![false,false,false])^2-
    f ![true,true,false]*f ![false,false,true]*f ![false,false,false]-
    f ![true,false,true]*f ![false,true,false]*f ![false,false,false]-
    f ![false,true,true]*f ![true,false,false]*f ![false,false,false]+
    2*f ![true,false,false]*f ![false,true,false]*f ![false,false,true]

theorem product_cubic (u : Bool→K) (B : Bool→Bool→K) (c : K)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    cubic (fun x=>c*u (x i)*B (x j) (x k))=0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [cubic] <;>ring

theorem one_two_split (f : Signature K 3) (u : Signature K 1) (B : Signature K 2)
    (s : ProperSplit (⟨3,f⟩ : AnySignature K) ⟨1,u⟩ ⟨2,B⟩) : cubic f=0 := by
  let i:=s.ports (.inl 0)
  let j:=s.ports (.inr 0)
  let k:=s.ports (.inr 1)
  have ij : i≠j := by simp [i,j]
  have ik : i≠k := by simp [i,k]
  have jk : j≠k := by
    intro equal
    have h:=Sum.inr.inj (s.ports.injective equal)
    exact (by decide : (0 : Fin 2)≠1) h
  have equation : f=(fun x=>(s.scale : K)*u (fun _=>x i)*B ![x j,x k]) := by
    have eqn : f=(fun x=>(s.scale : K)*(u (fun q=>x (s.ports (.inl q)))*B (fun q=>x (s.ports (.inr q))))) := s.equation
    funext x
    have h:=congrFun eqn x
    have hu : (fun q : Fin 1=>x (s.ports (.inl q)))=(fun _=>x i) := by
      funext q
      have hq : q=0:=Fin.eq_zero q
      subst q
      rfl
    have hb : (fun q : Fin 2=>x (s.ports (.inr q)))=![x j,x k] := by
      funext q
      fin_cases q <;>rfl
    dsimp only at h
    rw [hu,hb] at h
    exact h.trans (by ring)
  rw [equation]
  exact product_cubic (fun b=>u (fun _=>b)) (fun a b=>B ![a,b]) s.scale i j k ij ik jk

theorem proper_split (f : Signature K 3) {a b : AnySignature K}
    (s : ProperSplit (⟨3,f⟩ : AnySignature K) a b) : cubic f=0 := by
  rcases a with ⟨m,A⟩
  rcases b with ⟨n,B⟩
  have hm:=s.left_pos
  have hn:=s.right_pos
  have hs:=s.arity
  change 0<m at hm
  change 0<n at hn
  change m+n=3 at hs
  have alternatives : (m=1 ∧ n=2) ∨ (m=2 ∧ n=1) := by omega
  rcases alternatives with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact one_two_split f A B s
  · exact one_two_split f B A (GlobalCloseCompletionUnaryNoInteractions.swap s)

theorem of_tree (f : Signature K 3) (t : FactorTree (⟨3,f⟩ : AnySignature K))
    (small : ∀g∈t.leaves,g.1≤2) : cubic f=0 := by
  cases t with
  | leaf f hp=>
    have h:=small ⟨3,f⟩ (by simp [FactorTree.leaves])
    change 3≤2 at h
    omega
  | split s a b=>exact proper_split f s

theorem scale (f : Signature K 3) (c : K) : cubic (fun x=>c*f x)=c^3*cubic f := by
  unfold cubic
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTernarySmallCubic
end
