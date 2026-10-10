import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! Exact six-bit parity regularization for rank two. The generators are
proper coordinate faces at either pinned bit and their parameter reversals.
Only total-odd and separately-all-odd patterns remain exceptional. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoParity
open Holant
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def generator (p q : Fin 3→Bool) : Fin 4→Bool×Bool :=
  ![(p 0 ^^ p 2,q 0 ^^ q 2),(p 0 ^^ q 2,q 0 ^^ p 2),
    (p 1 ^^ p 2,q 1 ^^ q 2),(p 1 ^^ q 2,q 1 ^^ p 2)]

def repair (g h : Bool×Bool) : Bool×Bool :=
  ((h.1 && g.1) ^^ (h.2 && g.2),(h.1 && g.2) ^^ (h.2 && g.1))

def TotalOdd (p q : Fin 3→Bool) : Prop := ∀j,(p j ^^ q j)=true

def BothOdd (p q : Fin 3→Bool) : Prop := ∀j,p j=true ∧ q j=true

private theorem finite_cases : ∀p q : Fin 3→Bool,
    TotalOdd p q ∨ BothOdd p q ∨
    (∀j,p j=false ∧ q j=false) ∨
    (∃i,(generator p q i).1≠(generator p q i).2) ∨
    ((∀j,p j=q j) ∧ ∃i,generator p q i=(true,true)) := by
  unfold TotalOdd BothOdd
  decide

theorem unequal_repair (g t : Bool×Bool) (ne : g.1≠g.2) :
    repair g (if g.1 then t else (t.2,t.1))=t := by
  rcases g with ⟨a,b⟩
  rcases t with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [repair]

theorem diagonal_repair (b : Bool) : repair (true,true) (b,false)=(b,b) := by
  cases b <;> rfl

theorem exceptional_or_repair (p q : Fin 3→Bool) :
    TotalOdd p q ∨ BothOdd p q ∨
    ∃i : Fin 4,∃flags : Fin 3→Bool×Bool,∀j,repair (generator p q i) (flags j)=(p j,q j) := by
  rcases finite_cases p q with total|both|zero|⟨i,ne⟩|⟨equal,i,gi⟩
  · exact Or.inl total
  · exact Or.inr (Or.inl both)
  · right;right
    refine ⟨0,fun _=>(false,false),?_⟩
    intro j
    rw [(zero j).1,(zero j).2]
    rfl
  · right;right
    exact ⟨i,fun j=>if (generator p q i).1 then (p j,q j) else (q j,p j),
      fun j=>unequal_repair (generator p q i) (p j,q j) ne⟩
  · right;right
    refine ⟨i,fun j=>(p j,false),?_⟩
    intro j
    rw [gi,diagonal_repair,equal j]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoParity
