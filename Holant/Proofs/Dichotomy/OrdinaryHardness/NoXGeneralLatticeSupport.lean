import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUnsignedBinary

/-! Finite Boolean support lattices have supported extreme words. Closure
under relative complements then forces ternary-XOR closure. A missing relative
complement is exposed by a purely unsigned two-variable interval minor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLatticeSupport
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace P
export NoXGeneralUnsignedBinary (meet join)
end P
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
abbrev Word := Fin n→Bool

def Below (x y : Word (n:=n)) : Prop := ∀i,x i=true→y i=true

def intersection (a : Word (n:=n)) (ws : List (Word (n:=n))) : Word (n:=n) := fun i=>a i && ws.all (fun x=>x i)

def unionWords (a : Word (n:=n)) (ws : List (Word (n:=n))) : Word (n:=n) := fun i=>a i || ws.any (fun x=>x i)

variable (R : Word (n:=n)→Prop)
variable (hm : ∀x y,R x→R y→R (P.meet x y)) (hj : ∀x y,R x→R y→R (P.join x y))

include hm in
theorem intersection_supported (a : Word (n:=n)) (ha : R a)
    (ws : List (Word (n:=n))) (hw : ∀x∈ws,R x) : R (intersection a ws) := by
  induction ws with
  | nil=>
      have eqn : intersection a []=a := by
        funext i
        change (a i && true)=a i
        cases a i <;> rfl
      rw [eqn]
      exact ha
  | cons x xs ih=>
      have eqn : intersection a (x::xs)=P.meet x (intersection a xs) := by
        funext i
        simp only [intersection,List.all_cons,P.meet]
        cases a i <;> cases x i <;> rfl
      rw [eqn]
      exact hm _ _ (hw x (by simp)) (ih (fun y hy=>hw y (by simp [hy])))

include hj in
theorem union_supported (a : Word (n:=n)) (ha : R a)
    (ws : List (Word (n:=n))) (hw : ∀x∈ws,R x) : R (unionWords a ws) := by
  induction ws with
  | nil=>
      have eqn : unionWords a []=a := by
        funext i
        change (a i || false)=a i
        cases a i <;> rfl
      rw [eqn]
      exact ha
  | cons x xs ih=>
      have eqn : unionWords a (x::xs)=P.join x (unionWords a xs) := by
        funext i
        simp only [unionWords,List.any_cons,P.join]
        cases a i <;> cases x i <;> rfl
      rw [eqn]
      exact hj _ _ (hw x (by simp)) (ih (fun y hy=>hw y (by simp [hy])))

def lowWitness (a : Word (n:=n)) (i : Fin n) : Word (n:=n) :=
  if h : ∃x,R x ∧ x i=false then Classical.choose h else a

def highWitness (a : Word (n:=n)) (i : Fin n) : Word (n:=n) :=
  if h : ∃x,R x ∧ x i=true then Classical.choose h else a

def lower (a : Word (n:=n)) : Word (n:=n) := intersection a (List.ofFn (lowWitness R a))
def upper (a : Word (n:=n)) : Word (n:=n) := unionWords a (List.ofFn (highWitness R a))

include hm in
theorem lower_supported (a : Word (n:=n)) (ha : R a) : R (lower R a) := by
  apply intersection_supported R hm a ha
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold lowWitness
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact ha

include hj in
theorem upper_supported (a : Word (n:=n)) (ha : R a) : R (upper R a) := by
  apply union_supported R hj a ha
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold highWitness
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact ha

theorem lower_bound (a x : Word (n:=n)) (hx : R x) : Below (lower R a) x := by
  intro i hlo
  by_contra bad
  have hfalse : x i=false := Bool.eq_false_iff.mpr bad
  have exists0 : ∃w,R w ∧ w i=false := ⟨x,hx,hfalse⟩
  have wit : lowWitness R a i i=false := by
    simp only [lowWitness,dite_eq_left exists0]
    exact (Classical.choose_spec exists0).2
  have all : (List.ofFn (lowWitness R a)).all (fun w=>w i)=true := by
    change (a i && (List.ofFn (lowWitness R a)).all (fun w=>w i))=true at hlo
    cases h : (List.ofFn (lowWitness R a)).all (fun w=>w i) <;> simp_all
  have eqn:=List.all_eq_true.mp all (lowWitness R a i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  rw [wit] at eqn
  contradiction

theorem upper_bound (a x : Word (n:=n)) (hx : R x) : Below x (upper R a) := by
  intro i hxi
  have exists1 : ∃w,R w ∧ w i=true := ⟨x,hx,hxi⟩
  have wit : highWitness R a i i=true := by
    simp only [highWitness,dite_eq_left exists1]
    exact (Classical.choose_spec exists1).2
  have any : (List.ofFn (highWitness R a)).any (fun w=>w i)=true :=
    List.any_eq_true.mpr ⟨highWitness R a i,List.mem_ofFn.mpr ⟨i,rfl⟩,wit⟩
  simp only [upper,unionWords,any,Bool.or_true]

include hm hj in
theorem extrema (nonempty : ∃x,R x) : ∃lo hi,R lo ∧ R hi ∧ ∀x,R x→Below lo x ∧ Below x hi := by
  obtain ⟨a,ha⟩ := nonempty
  exact ⟨lower R a,upper R a,lower_supported R hm a ha,upper_supported R hj a ha,
    fun x hx=>⟨lower_bound R a x hx,upper_bound R a x hx⟩⟩

def relative (lo hi x : Word (n:=n)) : Word (n:=n) := fun i=>lo i || (hi i && !(x i))

def xorRel (lo hi x y : Word (n:=n)) : Word (n:=n) :=
  P.join (P.meet x (relative lo hi y)) (P.meet (relative lo hi x) y)

theorem xorRel_value (lo hi x y : Word (n:=n))
    (lx : Below lo x) (ly : Below lo y) (xh : Below x hi) (yh : Below y hi) :
    xorRel lo hi x y=(fun i=>if lo i then true else Bool.xor (x i) (y i)) := by
  funext i
  have a:=lx i
  have b:=ly i
  have c:=xh i
  have d:=yh i
  cases hlo : lo i <;> cases hhi : hi i <;> cases hx : x i <;> cases hy : y i <;>
    simp_all [xorRel,relative,P.meet,P.join]

include hm hj in
theorem ternary_of_relative (lo hi : Word (n:=n))
    (bounds : ∀x,R x→Below lo x ∧ Below x hi) (closed : ∀x,R x→R (relative lo hi x)) :
    ∀x y z,R x→R y→R z→R (tripleXor x y z) := by
  have rel (x y : Word (n:=n)) (hx : R x) (hy : R y) : R (xorRel lo hi x y) :=
    hj _ _ (hm _ _ hx (closed y hy)) (hm _ _ (closed x hx) hy)
  intro x y z hx hy hz
  have hxy:=rel x y hx hy
  have he : xorRel lo hi (xorRel lo hi x y) z=tripleXor x y z := by
    rw [xorRel_value lo hi _ z (bounds _ hxy).1 (bounds _ hz).1 (bounds _ hxy).2 (bounds _ hz).2,
      xorRel_value lo hi x y (bounds _ hx).1 (bounds _ hy).1 (bounds _ hx).2 (bounds _ hy).2]
    funext i
    have ax:=(bounds x hx).1 i
    have ay:=(bounds y hy).1 i
    have az:=(bounds z hz).1 i
    cases hlo : lo i <;> cases hxi : x i <;> cases hyi : y i <;> cases hzi : z i <;>
      simp_all [tripleXor]
  rw [←he]
  exact rel _ _ hxy hz

def chainPorts (lo mid hi : Word (n:=n)) : Fin n→Bool ⊕ Fin 2 := fun i=>
  if lo i then .inl true else if hi i then (if mid i then .inr 0 else .inr 1) else .inl false

theorem chain_values (lo mid hi : Word (n:=n)) (lm : Below lo mid) (mh : Below mid hi) :
    T.substitute (chainPorts lo mid hi) ![false,false]=lo ∧
    T.substitute (chainPorts lo mid hi) ![false,true]=relative lo hi mid ∧
    T.substitute (chainPorts lo mid hi) ![true,false]=mid ∧
    T.substitute (chainPorts lo mid hi) ![true,true]=hi := by
  have bound (i : Fin n) : (lo i=true→mid i=true) ∧ (mid i=true→hi i=true) := ⟨lm i,mh i⟩
  constructor
  · funext i;cases hl : lo i <;> cases hh : hi i <;> cases hm : mid i <;> simp [chainPorts,T.substitute,hl,hh,hm]
  constructor
  · funext i;cases hl : lo i <;> cases hh : hi i <;> cases hm : mid i <;> simp [chainPorts,T.substitute,relative,hl,hh,hm]
  constructor
  · funext i;have h:=bound i;cases hl : lo i <;> cases hh : hi i <;> cases hm : mid i <;> simp_all [chainPorts,T.substitute]
  · funext i;have h:=bound i;cases hl : lo i <;> cases hh : hi i <;> cases hm : mid i <;> simp_all [chainPorts,T.substitute]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLatticeSupport
end
