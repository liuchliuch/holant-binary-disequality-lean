import Holant.Certificates.MatchingContractionClosure.ProductSemantics

/-! Concrete residual port bijections. A same-edge closure deletes that edge;
a cross closure swaps the two right endpoints and then deletes one edge. -/
namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {P E : Type*} [DecidableEq P] [DecidableEq E]

abbrev Remaining (u v : P) := {i : P // i≠u ∧ i≠v}
abbrev OtherEdges (e : E) := {d : E // d≠e}

theorem remaining_edge_ne (p : (E × Bool) ≃ P) (e : E)
    (x : Remaining (p (e,false)) (p (e,true))) : (p.symm x.val).1 ≠ e := by
  intro he
  have hx : x.val=p (e,(p.symm x.val).2) := by
    calc
      x.val=p ((p.symm x.val).1,(p.symm x.val).2) := (p.apply_symm_apply _).symm
      _ = _ := by rw [he]
  cases hb : (p.symm x.val).2
  · exact x.property.1 (by simpa only [hb] using hx)
  · exact x.property.2 (by simpa only [hb] using hx)

def deletePorts (p : (E × Bool) ≃ P) (e : E) :
    (OtherEdges e × Bool) ≃ Remaining (p (e,false)) (p (e,true)) where
  toFun q := ⟨p (q.1.val,q.2),by
    constructor <;> intro he <;> exact q.1.property (congrArg Prod.fst (p.injective he))⟩
  invFun x := (⟨(p.symm x.val).1,remaining_edge_ne p e x⟩,(p.symm x.val).2)
  left_inv q := by
    rcases q with ⟨⟨d,hd⟩,b⟩
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp
  right_inv x := by
    apply Subtype.ext
    exact p.apply_symm_apply x.val

@[simp] theorem deletePorts_val (p : (E × Bool) ≃ P) (e : E) (q : OtherEdges e × Bool) :
    (deletePorts p e q).val=p (q.1.val,q.2) := rfl

def endpointSwap (p : (E × Bool) ≃ P) (e f : E) : (E × Bool) ≃ P :=
  (Equiv.swap (e,true) (f,true)).trans p

@[simp] theorem endpointSwap_false (p : (E × Bool) ≃ P) (e f d : E) :
    endpointSwap p e f (d,false)=p (d,false) := by
  simp [endpointSwap,Equiv.swap_apply_def]

@[simp] theorem endpointSwap_right (p : (E × Bool) ≃ P) (e f : E) :
    endpointSwap p e f (f,true)=p (e,true) := by
  simp [endpointSwap]

@[simp] theorem endpointSwap_left (p : (E × Bool) ≃ P) (e f : E) :
    endpointSwap p e f (e,true)=p (f,true) := by
  simp [endpointSwap]

def swappedRemaining (p : (E × Bool) ≃ P) (e f : E) :
    Remaining (endpointSwap p e f (f,false)) (endpointSwap p e f (f,true)) ≃
      Remaining (p (e,true)) (p (f,false)) :=
  Equiv.subtypeEquivRight (fun x => by rw [endpointSwap_false,endpointSwap_right]; exact and_comm)

def splicePorts (p : (E × Bool) ≃ P) (e f : E) :
    (OtherEdges f × Bool) ≃ Remaining (p (e,true)) (p (f,false)) :=
  (deletePorts (endpointSwap p e f) f).trans (swappedRemaining p e f)

theorem splicePorts_val (p : (E × Bool) ≃ P) (e f : E) (q : OtherEdges f × Bool) :
    (splicePorts p e f q).val =
      if q.1.val=e then (if q.2 then p (f,true) else p (e,false)) else p (q.1.val,q.2) := by
  change endpointSwap p e f (q.1.val,q.2)=_
  by_cases hd : q.1.val=e
  · cases hb : q.2 <;> simp [hd,hb]
  · cases hb : q.2
    · simp [hd,hb]
    · simp [endpointSwap,Equiv.swap_apply_def,hd,hb,q.1.property]

variable {K : Type*} [Field K]

def extendRemaining (u v : P) (x : Remaining u v → Bool) : P → Bool :=
  fun i => if hi : i≠u ∧ i≠v then x ⟨i,hi⟩ else false

@[simp] theorem extendRemaining_apply (u v : P) (x : Remaining u v → Bool) (i : Remaining u v) :
    extendRemaining u v x i.val=x i := by simp [extendRemaining,i.property]

/-- The actual bilinear contraction on named original ports, with precisely
the undeleted original ports as its output type. -/
def contractPair (u v : P) (C : Binary (K := K)) (F : Tensor K P) : Tensor K (Remaining u v) :=
  fun x => ∑ a : Bool, ∑ b : Bool, C a b*F (insertPair u v a b (extendRemaining u v x))

theorem contractPair_zero (u v : P) (C : Binary (K := K)) :
    contractPair u v C (0 : Tensor K P)=0 := by
  funext x
  simp [contractPair]

end
end Holant.Certificates.MatchingContractionClosure
