import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Exact modulo-four character incidences for rank-two and rank-three
support charts. The seven-column kernel has precisely the 32 affine sign
patterns; no physical gate or phase-class conclusion is assumed here. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceCore
open Holant
namespace C
def codeThree (x : Fin 2→Bool) : Fin 3→Bool := ![x 0,x 1,x 0^^x 1]
def codeSeven (x : Fin 3→Bool) : Fin 7→Bool :=
  ![x 0,x 1,x 2,x 1^^x 2,x 0^^x 2,x 0^^x 1,(x 0^^x 1)^^x 2]
end C
set_option maxHeartbeats 700000
set_option Elab.async false

@[simp] theorem four : (4 : ZMod 4)=0 := by decide
@[simp] theorem six : (6 : ZMod 4)=2 := by decide
@[simp] theorem eight : (8 : ZMod 4)=0 := by decide

def bit (b : Bool) : ZMod 4:=if b then 1 else 0
def evenBit (b : Bool) : ZMod 4:=if b then 2 else 0

theorem even_exists : ∀z : ZMod 4,2*z=0→∃b : Bool,z=evenBit b := by decide

theorem rank_two (a b c : ZMod 4) (h0 : a+c=0) (h1 : b+c=0) (h2 : a+b=0) :
    (a=0 ∧ b=0 ∧ c=0) ∨ (a=2 ∧ b=2 ∧ c=2) := by
  have h : 2*c=0 := by linear_combination (norm := (ring_nf <;> simp)) h0+h1-h2
  obtain ⟨u,hu⟩:=even_exists c h
  cases u <;> simp only [evenBit,Bool.false_eq_true,ite_false,ite_true] at hu
  · left
    refine ⟨?_,?_,hu⟩
    · linear_combination (norm := (ring_nf <;> simp)) h0-hu
    · linear_combination (norm := (ring_nf <;> simp)) h1-hu
  · right
    refine ⟨?_,?_,hu⟩
    · linear_combination (norm := (ring_nf <;> simp)) h0-hu
    · linear_combination (norm := (ring_nf <;> simp)) h1-hu

variable (c : Fin 7→ZMod 4)
variable (h0 : c 0+c 4+c 5+c 6=0) (h1 : c 1+c 3+c 5+c 6=0)
variable (h2 : c 2+c 3+c 4+c 6=0) (h3 : c 1+c 2+c 4+c 5=0)
variable (h4 : c 0+c 2+c 3+c 5=0) (h5 : c 0+c 1+c 3+c 4=0)
variable (h6 : c 0+c 1+c 2+c 6=0)

def constant : ZMod 4:= -(c 0+c 1+c 2+c 3+c 4+c 5+c 6)

include h0 h1 h2 h3 h4 h5 h6 in
theorem twice0 : 2*(c 0-constant c)=0 := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0+2*h1+2*h2+2*h3-h4-h5-h6
include h0 h1 h2 h3 h4 h5 h6 in
theorem twice1 : 2*(c 1-constant c)=0 := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0+2*h1-h2+2*h3-h4+2*h5+2*h6
include h0 h1 h2 h3 h4 h5 h6 in
theorem twice2 : 2*(c 2-constant c)=0 := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0-h1+2*h2+2*h3+2*h4-h5+2*h6

include h0 h1 h2 h3 h4 h5 h6 in
theorem relation3 : c 3=c 1+c 2-constant c := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0-h1-h2+2*h3-h4-h5+2*h6
include h0 h1 h2 h3 h4 h5 h6 in
theorem relation4 : c 4=c 0+c 2-constant c := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0-h1-h2-h3+2*h4-h5+2*h6
include h0 h1 h2 h3 h4 h5 h6 in
theorem relation5 : c 5=c 0+c 1-constant c := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0-h1-h2-h3-h4+2*h5+2*h6
include h0 h1 h2 h3 h4 h5 h6 in
theorem relation6 : c 6=c 0+c 1+c 2-2*constant c := by
  unfold constant
  linear_combination (norm := (ring_nf <;> simp)) -h0-h1-h2+2*h3+2*h4+2*h5+2*h6

include h0 h1 h2 h3 h4 h5 h6 in
theorem rank_three : ∃t : ZMod 4,∃u : Fin 3→Bool,∀j,c j=t+evenBit (C.codeSeven u j) := by
  obtain ⟨u0,hu0⟩:=even_exists _ (twice0 c h0 h1 h2 h3 h4 h5 h6)
  obtain ⟨u1,hu1⟩:=even_exists _ (twice1 c h0 h1 h2 h3 h4 h5 h6)
  obtain ⟨u2,hu2⟩:=even_exists _ (twice2 c h0 h1 h2 h3 h4 h5 h6)
  have e0 : c 0=constant c+evenBit u0 := by linear_combination (norm := (ring_nf <;> simp)) hu0
  have e1 : c 1=constant c+evenBit u1 := by linear_combination (norm := (ring_nf <;> simp)) hu1
  have e2 : c 2=constant c+evenBit u2 := by linear_combination (norm := (ring_nf <;> simp)) hu2
  refine ⟨constant c,![u0,u1,u2],?_⟩
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2
  · change c 3=constant c+evenBit (C.codeSeven ![u0,u1,u2] 3)
    rw [relation3 c h0 h1 h2 h3 h4 h5 h6,e1,e2]
    cases u1 <;> cases u2 <;> simp [C.codeSeven,evenBit] <;> ring_nf <;> simp
  · change c 4=constant c+evenBit (C.codeSeven ![u0,u1,u2] 4)
    rw [relation4 c h0 h1 h2 h3 h4 h5 h6,e0,e2]
    cases u0 <;> cases u2 <;> simp [C.codeSeven,evenBit] <;> ring_nf <;> simp
  · change c 5=constant c+evenBit (C.codeSeven ![u0,u1,u2] 5)
    rw [relation5 c h0 h1 h2 h3 h4 h5 h6,e0,e1]
    cases u0 <;> cases u1 <;> simp [C.codeSeven,evenBit] <;> ring_nf <;> simp
  · change c 6=constant c+evenBit (C.codeSeven ![u0,u1,u2] 6)
    rw [relation6 c h0 h1 h2 h3 h4 h5 h6,e0,e1,e2]
    cases u0 <;> cases u1 <;> cases u2 <;> simp [C.codeSeven,evenBit] <;> ring_nf <;> simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceCore
