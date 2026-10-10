import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist

/-! The scoped factor-reconstruction step behind the pin/loop prime descent.
If every zero cap away from a fixed block retains the same factor and one
ordinary loop away from that block retains it, the whole tensor has that
factor. The proof reconstructs the missing all-one column by subtraction;
it works over the actual field without conjugation or a positivity premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPinLoopFactor
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
variable {K : Type} [Field K] {m n k : ℕ}

def block (ports : (Fin m ⊕ Fin (n+2)) ≃ Fin k) (f : Signature K k)
    (x : Fin m→Bool) (y : Fin (n+2)→Bool) : K :=
  f (fun i=>Sum.elim x y (ports.symm i))

def zeroPair : Fin (n+2)→Bool := fun i=>if i.val<2 then false else true

theorem zeroPair_ne_one : zeroPair (n:=n)≠(fun _=>true) := by
  intro h
  have h0 := congrFun h ⟨0,by omega⟩
  simp [zeroPair] at h0

/-- Only the two terms of the actual equality loop at the all-one outside
assignment are needed. The missing column is never assumed to vanish. -/
theorem reconstruct (F : (Fin m→Bool)→(Fin (n+2)→Bool)→K)
    (g : Signature K m)
    (caps : ∀y,y≠(fun _=>true)→∃c : K,∀x,F x y=g x*c)
    (loop : ∃c : K,∀x,F x zeroPair+F x (fun _=>true)=g x*c) :
    ∃h : Signature K (n+2),∀x y,F x y=g x*h y := by
  classical
  obtain ⟨c0,h0⟩ := caps zeroPair zeroPair_ne_one
  obtain ⟨cL,hL⟩ := loop
  have allColumns : ∀y,∃c : K,∀x,F x y=g x*c := by
    intro y
    by_cases hy : y=(fun _=>true)
    · subst y
      refine ⟨cL-c0,?_⟩
      intro x
      have hp := hL x
      rw [h0 x] at hp
      calc
        F x (fun _=>true)=(g x*cL)-(g x*c0) := by rw [←hp];simp
        _=g x*(cL-c0) := (mul_sub _ _ _).symm
    · exact caps y hy
  exact ⟨fun y=>Classical.choose (allColumns y),fun x y=>Classical.choose_spec (allColumns y) x⟩

/-- The abstract column identity is an exact proper tensor split on the
original ordered ports, with multiplier one. -/
theorem proper_split (ports : (Fin m ⊕ Fin (n+2)) ≃ Fin k)
    (f : Signature K k) (g : Signature K m) (positive : 0<m)
    (caps : ∀y,y≠(fun _=>true)→∃c : K,∀x,block ports f x y=g x*c)
    (loop : ∃c : K,∀x,block ports f x zeroPair+block ports f x (fun _=>true)=g x*c) :
    ∃h : Signature K (n+2),Nonempty (ProperSplit (⟨k,f⟩ : AnySignature K) ⟨m,g⟩ ⟨n+2,h⟩) := by
  obtain ⟨h,hf⟩ := reconstruct (block ports f) g caps loop
  refine ⟨h,⟨{left_pos:=positive,right_pos:=by change 0<n+2;omega,ports:=ports,scale:=1,equation:=?_}⟩⟩
  funext z
  have hz := hf (fun i=>z (ports (.inl i))) (fun i=>z (ports (.inr i)))
  have eta : (fun i=>Sum.elim (fun j=>z (ports (.inl j)))
      (fun j=>z (ports (.inr j))) (ports.symm i))=z := by
    funext i
    have hi := ports.apply_symm_apply i
    cases hs : ports.symm i with
    | inl j=>simpa [hs] using congrArg z hi
    | inr j=>simpa [hs] using congrArg z hi
  simpa only [block,eta,Units.val_one,one_mul] using hz

/-- A genuine prime must have a zero cap or an ordinary loop which loses
the selected proper factor. This is the local UPF propagation boundary. -/
theorem prime_obstruction (ports : (Fin m ⊕ Fin (n+2)) ≃ Fin k)
    (f : Signature K k) (prime : Prime (⟨k,f⟩ : AnySignature K))
    (g : Signature K m) (positive : 0<m) :
    (∃y,y≠(fun _=>true) ∧ ¬∃c : K,∀x,block ports f x y=g x*c) ∨
      ¬∃c : K,∀x,block ports f x zeroPair+block ports f x (fun _=>true)=g x*c := by
  classical
  by_cases caps : ∀y,y≠(fun _=>true)→∃c : K,∀x,block ports f x y=g x*c
  · right
    intro loop
    obtain ⟨h,split⟩ := proper_split ports f g positive caps loop
    exact prime.2 ⟨⟨m,g⟩,⟨n+2,h⟩,split⟩
  · left
    push Not at caps
    obtain ⟨y,hy,hbad⟩ := caps
    exact ⟨y,hy,by simpa only [not_exists,not_forall] using hbad⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPinLoopFactor
end
