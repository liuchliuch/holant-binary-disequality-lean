import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceCore

/-! Modulo-four regularization of the physical signed character incidences.
Two proper-coordinate-face substitutions suffice for every even nonconstant
kernel vector. The exceptional vectors are all-two, or all-odd after a
translation of the same supported logical cube. The finite certificates are
checked by the kernel, and no graph or phase classification is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceRegularization
open Holant
open scoped BigOperators
namespace C
export NoIPurePhaseIncidenceCore (evenBit rank_three)
end C
namespace P
def bits (i : Fin 8) : Fin 3→Bool :=
  ![![false,false,false],![true,false,false],![false,true,false],![false,false,true],
    ![false,true,true],![true,false,true],![true,true,false],![true,true,true]] i

def name (a b c : Bool) : Fin 8 :=
  if a then (if b then (if c then 7 else 6) else (if c then 5 else 1))
  else if b then (if c then 4 else 2) else if c then 3 else 0

def plus (i j : Fin 8) : Fin 8 :=
  name (bits i 0 ^^ bits j 0) (bits i 1 ^^ bits j 1) (bits i 2 ^^ bits j 2)

structure Transform where
  axis : Fin 3
  first : Fin 8
  second : Fin 8
  deriving DecidableEq, Fintype

def inputs (t : Transform) : Fin 3→Fin 8 :=
  if t.axis=0 then ![0,t.first,t.second]
  else if t.axis=1 then ![t.first,0,t.second] else ![t.first,t.second,0]

def image (t : Transform) : Fin 7→Fin 8 :=
  let a := inputs t 0
  let b := inputs t 1
  let c := inputs t 2
  ![a,b,c,plus b c,plus a c,plus a b,plus (plus a b) c]
end P
namespace A
export NoIPurePhaseIncidenceCore.C (codeSeven)
end A
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false

def pattern (t : ZMod 4) (u : Fin 3→Bool) (j : Fin 7) : ZMod 4 :=
  t+C.evenBit (A.codeSeven u j)

def contribution (c : Fin 7→ZMod 4) (q : P.Transform) (j : Fin 7) : ZMod 4 :=
  ∑k,if P.image q k=j.succ then c k else 0

def zeroSchedule (u : Fin 3→Bool) : Fin 2→P.Transform :=
  (![![⟨0,0,0⟩,⟨0,0,0⟩],![⟨0,1,2⟩,⟨0,2,5⟩],
      ![⟨1,1,2⟩,⟨1,1,4⟩],![⟨2,1,3⟩,⟨2,1,4⟩],
      ![⟨1,1,2⟩,⟨1,1,3⟩],![⟨0,1,2⟩,⟨0,2,3⟩],
      ![⟨0,1,2⟩,⟨0,4,5⟩],![⟨0,1,2⟩,⟨0,3,6⟩]] : Fin 8→Fin 2→P.Transform)
    (P.name (u 0) (u 1) (u 2))

def twoSchedule (u : Fin 3→Bool) : Fin 2→P.Transform :=
  (![![⟨0,0,0⟩,⟨0,0,0⟩],![⟨0,0,0⟩,⟨0,2,3⟩],
      ![⟨0,0,0⟩,⟨1,1,3⟩],![⟨0,0,0⟩,⟨2,1,2⟩],
      ![⟨0,0,0⟩,⟨1,1,4⟩],![⟨0,0,0⟩,⟨0,2,5⟩],
      ![⟨0,0,0⟩,⟨0,3,6⟩],![⟨0,0,0⟩,⟨0,4,5⟩]] : Fin 8→Fin 2→P.Transform)
    (P.name (u 0) (u 1) (u 2))

def Corrects (c : Fin 7→ZMod 4) (q : Fin 2→P.Transform) : Prop :=
  ∀j,c j+∑i,contribution c (q i) j=0

theorem zero_certificate (u : Fin 3→Bool) : Corrects (pattern 0 u) (zeroSchedule u) := by
  have hu : u=![u 0,u 1,u 2] := by funext i;fin_cases i <;> rfl
  rw [hu]
  unfold Corrects
  cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2 <;> decide

theorem two_certificate (u : Fin 3→Bool) (nonzero : u≠fun _=>false) :
    Corrects (pattern 2 u) (twoSchedule u) := by
  have hu : u=![u 0,u 1,u 2] := by funext i;fin_cases i <;> rfl
  rw [hu] at nonzero ⊢
  unfold Corrects
  cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2
  all_goals simp only [h0,h1,h2] at nonzero ⊢
  all_goals first
    | (exfalso;apply nonzero;funext i;fin_cases i <;> rfl)
    | decide

def translated (c : Fin 7→ZMod 4) (u : Fin 3→Bool) (j : Fin 7) : ZMod 4 :=
  if A.codeSeven u j then -(c j) else c j

theorem one_translation (u : Fin 3→Bool) : ∀j,translated (pattern 1 u) u j=1 := by
  intro j
  unfold translated pattern
  cases A.codeSeven u j <;> decide

theorem three_translation (u : Fin 3→Bool) : ∀j,translated (pattern 3 u) u j=3 := by
  intro j
  unfold translated pattern
  cases A.codeSeven u j <;> decide

/-- The normalized exceptional charge is common to all seven physical
character bundles. In the regular case the displayed two maps pin actual
information coordinates and give an exact signed-charge-zero certificate. -/
theorem cases_of_pattern (c : Fin 7→ZMod 4) (t : ZMod 4) (u : Fin 3→Bool)
    (eqn : ∀j,c j=pattern t u j) :
    (∃q : Fin 2→P.Transform,Corrects c q) ∨
    (∀j,c j=2) ∨
    (∃v : Fin 3→Bool,(∀j,translated c v j=1) ∨ (∀j,translated c v j=3)) := by
  have hc : c=pattern t u := funext eqn
  rw [hc]
  have ht : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by exact (by decide : ∀v : ZMod 4,v=0 ∨ v=1 ∨ v=2 ∨ v=3) t
  rcases ht with rfl|rfl|rfl|rfl
  · exact Or.inl ⟨zeroSchedule u,zero_certificate u⟩
  · exact Or.inr (Or.inr ⟨u,Or.inl (one_translation u)⟩)
  · by_cases hu : u=fun _=>false
    · right;left
      subst u
      intro j
      fin_cases j <;> rfl
    · exact Or.inl ⟨twoSchedule u,two_certificate u hu⟩
  · exact Or.inr (Or.inr ⟨u,Or.inr (three_translation u)⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceRegularization
