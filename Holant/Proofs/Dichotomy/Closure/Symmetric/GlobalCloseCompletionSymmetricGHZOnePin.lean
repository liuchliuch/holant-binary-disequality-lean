import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZOnePinAlgebra
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapProducer

/-! A single actual pin0 is enough for the symmetric GHZ cap selector.
Its singular isotropic exception is repaired with two further physical caps. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZOnePin
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph
  (symmetric pencil pencil_det cap cap_form step walk walk_value)
end C
namespace S
export GlobalCloseCompletionSymmetricGHZCapSelection (matrix cap_matrix Semisimple regularize)
end S
namespace A
export GlobalCloseCompletionSymmetricGHZOnePinAlgebra
  (weighted_of_zero nonzero_of_singular walk_det exceptional last_det)
end A
namespace P
export GlobalCloseCompletionSymmetricGHZCapProducer (a b c d form_symmetric hyperdet_nonzero)
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
export GlobalCloseCompletionSymmetricGHZRegularCap (hyperdet)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K] {r : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin r)→Signature K (arity i.val)}

theorem step_value (B : Macro H 2) (U : Macro H 1) (x : Fin 1→Bool) :
    (C.step B U).network.denote x=U.network.denote (fun _=>false)*B.network.denote ![false,x 0]+
      U.network.denote (fun _=>true)*B.network.denote ![true,x 0] := by
  rw [C.step,Macro.contract_denote,Macro.tensor_denote]
  simp only [Signature.tensor_apply]
  have un (v : Bool) : (fun i : Fin 1=>(Fin.cons v (Fin.cons v x) : Fin 3→Bool) (Fin.castAdd 2 i))=(fun _=>v) := by
    funext i; fin_cases i; rfl
  have tr (v : Bool) : (fun i : Fin 2=>(Fin.cons v (Fin.cons v x) : Fin 3→Bool) (Fin.natAdd 1 i))=![v,x 0] := by
    funext i; fin_cases i <;> rfl
  simp only [un,tr]

theorem select (N : Macro H 3) (P0 : Macro H 1) (a b c d : K)
    (form : N.network.denote=C.symmetric a b c d) (hyper : P.hyperdet a b c d≠0)
    (pin : P0.network.denote=QuaternaryUnaryAccess.pin false) :
    (b=0 ∧ c=0 ∧ a≠0 ∧ d≠0) ∨
      ∃U : Macro H 1,Matrix.det (S.matrix (C.cap N U))≠0 ∧ S.Semisimple (S.matrix (C.cap N U)) := by
  classical
  have p0 : P0.network.denote (fun _=>false)=1 := by rw [pin];rfl
  have p1 : P0.network.denote (fun _=>true)=0 := by rw [pin];rfl
  have cap0:=C.cap_form N P0 a b c d 1 0 form p0 p1
  have d0 : Matrix.det (S.matrix (C.cap N P0))=a*c-b^2 := by
    rw [S.cap_matrix N P0 a b c d form,p0,p1,C.pencil_det]
    ring
  by_cases singular : a*c-b^2=0
  swap
  · exact Or.inr (S.regularize N P0 P0 a b c d form hyper pin (by rwa [d0]))
  by_cases bz : b=0
  · obtain ⟨cz,an,dn⟩:=A.weighted_of_zero a b c d hyper singular bz
    exact Or.inl ⟨bz,cz,an,dn⟩
  obtain ⟨an,last⟩:=A.nonzero_of_singular a b c d hyper singular bz
  let V:=C.walk (C.cap N P0) P0 1
  have value : V.network.denote=fun x=>if x 0 then b else a := by
    rw [C.walk_value (C.cap N P0) P0 (C.pencil a b c d 1 0) cap0 pin 1]
    funext x
    cases h : x 0 <;> simp [pow_one,C.pencil,h]
  have v0 : V.network.denote (fun _=>false)=a := by rw [value];rfl
  have v1 : V.network.denote (fun _=>true)=b := by rw [value];rfl
  have capV:=C.cap_form N V a b c d a b form v0 v1
  have matrixV : S.matrix (C.cap N V)=C.pencil a b c d a b := by
    rw [S.cap_matrix N V a b c d form,v0,v1]
  by_cases regular : Matrix.det (C.pencil a b c d a b)≠0
  · exact Or.inr (S.regularize N P0 V a b c d form hyper pin (by rwa [matrixV]))
  have zero : Matrix.det (C.pencil a b c d a b)=0:=not_ne_iff.mp regular
  obtain ⟨_,diagonal⟩:=A.exceptional a b c d hyper singular bz zero
  let U:=C.step (C.cap N V) V
  have u0 : U.network.denote (fun _=>false)=0 := by
    rw [step_value,v0,v1,capV,diagonal]
    simp [binarySignature]
  have u1 : U.network.denote (fun _=>true)=b*(b*d-c^2) := by
    rw [step_value,v0,v1,capV,diagonal]
    simp [binarySignature]
  apply Or.inr
  apply S.regularize N P0 U a b c d form hyper pin
  rw [S.cap_matrix N U a b c d form,u0,u1]
  exact A.last_det a b c d bz last

theorem produce (phi : K→+*AlgebraicComplex) (N : Macro H 3) (P0 : Macro H 1)
    (M : InvertibleKernel) (form : RingHomRealization.mapSignature phi N.network.denote=P.ghz M.matrix)
    (pin : P0.network.denote=QuaternaryUnaryAccess.pin false) :
    (∃a d : K,a≠0 ∧ d≠0 ∧ N.network.denote=C.symmetric a 0 0 d) ∨
      ∃U : Macro H 1,Matrix.det (S.matrix (C.cap N U))≠0 ∧ S.Semisimple (S.matrix (C.cap N U)) := by
  have shape:=P.form_symmetric phi N.network.denote M form
  rcases select N P0 (P.a N.network.denote) (P.b N.network.denote) (P.c N.network.denote) (P.d N.network.denote)
    shape (P.hyperdet_nonzero phi N.network.denote M form) pin with ⟨hb,hc,ha,hd⟩|good
  · exact Or.inl ⟨P.a N.network.denote,P.d N.network.denote,ha,hd,by simpa only [hb,hc] using shape⟩
  · exact Or.inr good


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZOnePin
end
