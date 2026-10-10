import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeFiniteDeck

/-! A dense common negative complement sign supplies its own genuine native
antidiagonal sign gate. One of two literal self-caps is nonzero; attaching
that actual cap removes the sign. No supplied Z or identity is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeComplementSign
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace A
export PaperTerminalBridgeAntiGroup (Available one)
end A
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace O
export PaperTerminalBridgeOddCards (pencil actual_pencil)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def Complement (f : Signature K 4) : Prop :=
  (entries f).b=(entries f).y ∧ (entries f).c=(entries f).z ∧ (entries f).d=(entries f).w

theorem minus_available (F : SignatureFamily K) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (hc : (entries f).c≠0) (c : (entries f).c= -(entries f).z)
    (d : (entries f).d= -(entries f).w) : A.Available F (-1) := by
  let e := entries f
  have result (k : Fin 3) (p : K) (hp : p≠0)
      (value : O.pencil e k 1=(p,-p)) : A.Available F (-1) := by
    have card := O.actual_pencil F f actual even k 1 (A.one F)
    change Gadget.RealizesUpTo F .disequality (C.antiTensor (O.pencil e k 1).1 (O.pencil e k 1).2) at card
    rw [value] at card
    have ratio := PaperTerminalBridgeFiniteDeck.ratio_actual F p (-p) hp card
    simpa [hp] using ratio
  by_cases live : e.w+e.c≠0
  · apply result 0 (e.w+e.c) live
    change (e.w+1*e.c,e.z+1*e.d)=(e.w+e.c,-(e.w+e.c))
    apply Prod.ext
    · simp
    · dsimp
      change e.c= -e.z at c
      change e.d= -e.w at d
      linear_combination c+d
  · have dead : e.w+e.c=0 := not_ne_iff.mp live
    have other : e.c+e.d≠0 := by
      intro zero
      apply hc
      change e.c=0
      change e.d= -e.w at d
      linear_combination (dead+zero-d)/2
    apply result 2 (e.c+e.d) other
    change (e.c+1*e.d,e.w+1*e.z)=(e.c+e.d,-(e.c+e.d))
    apply Prod.ext
    · simp
    · dsimp
      change e.c= -e.z at c
      change e.d= -e.w at d
      linear_combination c+d

def signed (f : Signature K 4) : Signature K 4 := fun x=>(if x 0 then -1 else 1)*f x

theorem signed_actual (F : SignatureFamily K) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (phase : A.Available F (-1)) :
    Gadget.RealizesUpTo F .disequality (signed f) := by
  obtain ⟨c,hc,cap⟩ := phase
  have attached := realizes_splice F f (fun x=>c*C.antiTensor 1 (-1) x) actual cap 0
  refine ⟨c,hc,?_⟩
  convert attached using 1
  funext x
  cases hx : x 0 <;>
    simp [signed,spliceTensor,C.antiTensor,Signature.disequality,hx,Function.update_eq_self]
  all_goals rw [←hx,Function.update_eq_self] <;> ring

theorem signed_even (f : Signature K 4) (even : EvenSupport f) : EvenSupport (signed f) := by
  intro x odd
  simp [signed,even x odd]

theorem signed_dense (f : Signature K 4) (dense : StableDenseParityAlgebra.Dense f) :
    StableDenseParityAlgebra.Dense (signed f) := by
  simpa [StableDenseParityAlgebra.Dense,entries,signed] using dense

theorem signed_complement (f : Signature K 4)
    (b : (entries f).b= -(entries f).y) (c : (entries f).c= -(entries f).z)
    (d : (entries f).d= -(entries f).w) : Complement (signed f) := by
  simpa [Complement,entries,signed] using And.intro b (And.intro c d)

theorem source (F : SignatureFamily K) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (dense : StableDenseParityAlgebra.Dense f) (ε : K) (square : ε^2=1)
    (b : (entries f).b=ε*(entries f).y) (c : (entries f).c=ε*(entries f).z)
    (d : (entries f).d=ε*(entries f).w) :
    ∃g : Signature K 4,Gadget.RealizesUpTo F .disequality g ∧
      EvenSupport g ∧ StableDenseParityAlgebra.Dense g ∧ Complement g := by
  rcases sq_eq_one_iff.mp square with rfl | rfl
  · refine ⟨f,⟨1,one_ne_zero,?_⟩,even,dense,?_⟩
    · simpa using actual
    · simpa [Complement] using And.intro b (And.intro c d)
  · simp only [neg_mul,one_mul] at b c d
    have phase := minus_available F f actual even dense.2.2.1 c d
    exact ⟨signed f,signed_actual F f actual phase,signed_even f even,
      signed_dense f dense,signed_complement f b c d⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeComplementSign
end
