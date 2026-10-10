import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroSource

/-! The opposite-pin arm needed in the prime/UPF selector. Every actual
nonzero ordinary graph whose zero entry vanishes in a nonisotropic unary
frame supplies a pure perpendicular power by actual unary caps. This applies
to original rows, pinned rows, and loop outputs before a terminal is chosen. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroOrigin
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame GeneralOddNonisotropicDescent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

theorem descend (F : SignatureFamily K) (U : Network K 1)
    (hUF : Uses U F) (hUE : Ordinary U) (n : ℕ) (N : Network K n)
    (hNF : Uses N F) (hNE : Ordinary N) (x : Fin n→Bool)
    (hx : chart U.denote N.denote x≠0)
    (zero : chart U.denote N.denote (fun _=>false)=0) :
    ∃m k : ℕ,0<m ∧ m+k=n ∧ ∃V : Network K m,
      Uses V F ∧ Ordinary V ∧ EndpointSupport (chart U.denote V.denote) ∧
      chart U.denote V.denote (fun _=>false)=0 ∧
      chart U.denote V.denote (fun _=>true)≠0 ∧
      V.shape.vertices=k*U.shape.vertices+N.shape.vertices ∧
      V.shape.edges=k*(U.shape.edges+1)+N.shape.edges := by
  classical
  induction n with
  | zero=>
    have he : x=(fun _=>false) := funext fun i=>Fin.elim0 i
    exact False.elim (hx (he ▸ zero))
  | succ n ih=>
    by_cases stop : EndpointSupport (chart U.denote N.denote)
    · have own : x≠(fun _=>false) := fun h=>hx (h ▸ zero)
      have other := (stop x hx).resolve_left own
      refine ⟨n+1,0,by omega,by omega,N,hNF,hNE,stop,zero,?_,by simp,by simp⟩
      rwa [←other]
    · obtain ⟨y,hy,hy0,hy1⟩ : ∃y,chart U.denote N.denote y≠0 ∧
          y≠(fun _=>false) ∧ y≠(fun _=>true) := by
        unfold EndpointSupport at stop
        push Not at stop
        exact stop
      obtain ⟨i,hi⟩ : ∃i,y i=false := by
        by_contra none
        push Not at none
        exact hy1 (funext fun i=>Bool.eq_true_of_not_eq_false (none i))
      let e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
      let R := reboundary N e
      let y' : Fin (n+1)→Bool := fun j=>y (e j)
      let z : Fin n→Bool := fun j=>y' j.succ
      have head : y' 0=false := by simpa [y',e] using hi
      have cons : Fin.cons false z=y' := by
        funext j
        exact Fin.cases head.symm (fun _=>rfl) j
      have back : (fun j=>y' (e j))=y := by funext j;simp [y',e]
      have live : chart U.denote (capHead U R).denote z≠0 := by
        rw [chart_capHead,cons,chart_reboundary,back]
        exact hy
      have zero' : chart U.denote (capHead U R).denote (fun _=>false)=0 := by
        rw [chart_capHead]
        have hc : Fin.cons false (fun _ : Fin n=>false)=(fun _=>false) := by
          funext j
          exact Fin.cases rfl (fun _=>rfl) j
        rw [hc,chart_reboundary]
        exact zero
      obtain ⟨m,k,hm,hkn,V,hVF,hVE,hVs,hV0,hV1,hVv,hVe⟩ :=
        ih (capHead U R) (capHead_uses F U R hUF hNF)
          (capHead_ordinary U R hUE hNE) z live zero'
      refine ⟨m,k+1,hm,by omega,V,hVF,hVE,hVs,hV0,hV1,?_,?_⟩
      · rw [hVv,capHead_vertices]
        change k*U.shape.vertices+(U.shape.vertices+N.shape.vertices)=_
        ring
      · rw [hVe,capHead_edges]
        change k*(U.shape.edges+1)+(U.shape.edges+1+N.shape.edges)=_
        ring

variable {r n : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))
variable (U : Network K 1) (UL : Labelling U.shape r 1 b)
variable (uExact : LabelledNetwork.Exact H U UL) (uEdges : Ordinary U)
variable (N : Network K n) (NL : Labelling N.shape r 1 b)
variable (nExact : LabelledNetwork.Exact H N NL) (nEdges : Ordinary N)
variable (hu : norm U.denote≠0) (nonzero : N.denote≠0)
variable (zero : chart U.denote N.denote (fun _=>false)=0)

structure Power where
  arity : ℕ
  caps : ℕ
  positive : 0<arity
  conservation : arity+caps=n
  graph : Network K arity
  labels : Labelling graph.shape r 1 b
  exact : LabelledNetwork.Exact H graph labels
  edges : Ordinary graph
  scalar : K
  nonzero : scalar≠0
  equation : graph.denote=fun x=>scalar*Signature.unaryPower
    (GlobalCloseCompletionUnaryZeroPower.opposite U.denote) arity x
  vertices : graph.shape.vertices=caps*U.shape.vertices+N.shape.vertices
  edgeCount : graph.shape.edges=caps*(U.shape.edges+1)+N.shape.edges

include uExact uEdges nExact nEdges hu nonzero zero in
theorem power_exists : Nonempty (Power H U N) := by
  classical
  obtain ⟨x,hx⟩ : ∃x,chart U.denote N.denote x≠0 := by
    by_contra none
    push Not at none
    have equal : chart U.denote N.denote=chart U.denote 0 := by
      rw [show chart U.denote (0 : Signature K n)=0 by
        simp [chart,Signature.coordinateAction_zero]]
      exact funext none
    exact nonzero (chart_injective U.denote hu equal)
  let F : SignatureFamily K := Set.range fun i : Fin r=>(⟨b i.val,H i⟩ : AnySignature K)
  obtain ⟨m,k,hm,hmk,V,hVF,hVE,hVs,hV0,hV1,hVv,hVe⟩ :=
    descend F U (fun v=>⟨UL.vertex v,uExact v⟩) uEdges n N
      (fun v=>⟨NL.vertex v,nExact v⟩) nEdges x hx zero
  let VL : Labelling V.shape r 1 b := {
    vertex v:=Classical.choose (hVF v)
    vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (hVF v))
    edge _:=0 }
  exact ⟨⟨m,k,hm,hmk,V,VL,(fun v=>Classical.choose_spec (hVF v)),hVE,
    chart U.denote V.denote (fun _=>true),hV1,
    GlobalCloseCompletionUnaryZeroPower.exact_power U.denote hu V.denote hVs hV0,hVv,hVe⟩⟩

def power : Power H U N := Classical.choice
  (power_exists H U UL uExact uEdges N NL nExact nEdges hu nonzero zero)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroOrigin
end
