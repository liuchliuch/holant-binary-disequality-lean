import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinPhaseActual

/-! Actual Pauli sign attachments preserve tensor primality on the original
ports. A purported split is transported back on the unique factor containing
the signed port, and finite sign sets follow by actual one-port induction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinPhasePrime
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

def single (f : Signature K n) (i : Fin n) : Signature K n :=
  fun x=>(if x i then -1 else 1)*f x

theorem restore (f : Signature K n) (i : Fin n) (x : Fin n→Bool) :
    f x=(if x i then -1 else 1)*single f i x := by
  cases h : x i <;> simp [single,h]

theorem involutive (f : Signature K n) (i : Fin n) : single (single f i) i=f := by
  funext x
  exact (restore f i x).symm

theorem single_prime (f : Signature K n) (prime : Prime (⟨n,f⟩ : AnySignature K)) (i : Fin n) :
    Prime (⟨n,single f i⟩ : AnySignature K) := by
  constructor
  · intro zero
    apply prime.1
    have h := congrArg (fun g=>single g i) zero
    rw [involutive] at h
    exact h.trans (by funext x;simp only [single,Pi.zero_apply,mul_zero])
  · rintro ⟨a,b,⟨split⟩⟩
    apply prime.2
    have port := split.ports.apply_symm_apply i
    cases h : split.ports.symm i with
    | inl j =>
      have point : split.ports (.inl j)=i := by simpa only [h] using port
      refine ⟨⟨a.1,single a.2 j⟩,b,⟨⟨split.left_pos,split.right_pos,split.ports,split.scale,?_⟩⟩⟩
      funext x
      dsimp only
      have eq : single f i x=(split.scale:K)*
          (a.2 (fun t=>x (split.ports (.inl t)))*b.2 (fun t=>x (split.ports (.inr t)))) :=
        congrFun split.equation x
      rw [restore f i x,eq]
      simp only [single,point]
      ring
    | inr j =>
      have point : split.ports (.inr j)=i := by simpa only [h] using port
      refine ⟨a,⟨b.1,single b.2 j⟩,⟨⟨split.left_pos,split.right_pos,split.ports,split.scale,?_⟩⟩⟩
      funext x
      dsimp only
      have eq : single f i x=(split.scale:K)*
          (a.2 (fun t=>x (split.ports (.inl t)))*b.2 (fun t=>x (split.ports (.inr t)))) :=
        congrFun split.equation x
      rw [restore f i x,eq]
      simp only [single,point]
      ring

theorem phase_prime (f : Signature K n) (prime : Prime (⟨n,f⟩ : AnySignature K)) (s : Finset (Fin n)) :
    Prime (⟨n,A.phase s f⟩ : AnySignature K) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have empty : A.phase (∅ : Finset (Fin n)) f=f := by funext x;simp [A.phase]
    rw [empty]
    exact prime
  | @insert i s hi ih =>
    have h := single_prime (A.phase s f) ih i
    have equal : single (A.phase s f) i=A.phase (insert i s) f := by
      funext x
      simp only [single,A.phase,Finset.prod_insert hi,mul_assoc]
    rw [equal] at h
    exact h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinPhasePrime
end
