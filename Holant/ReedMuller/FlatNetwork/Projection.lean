import Holant.ReedMuller.LowArity.Basic
import Mathlib.Algebra.CharP.Two

/-! Self-dual boundary direction under an actual two-port equality constraint.
The proof is constructive over the original coordinates, including the case
where the closed pair contributes a two-element fibre. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def prepend (b : ZMod 2) (x : BinaryVector n) : BinaryVector (n+2) := Fin.cons b (Fin.cons b x)
def dropTwo (x : BinaryVector (n+2)) : BinaryVector n := fun i => x i.succ.succ
def pairWord (n : ℕ) : BinaryVector (n+2) := prepend 1 0

theorem add_self_zero (a : ZMod 2) : a+a=0 := by fin_cases a <;> decide

theorem add_eq_zero_iff (a b : ZMod 2) : a+b=0 ↔ a=b := by
  have H : ∀ a b : ZMod 2,a+b=0 ↔ a=b := by decide
  exact H a b

theorem add_eq_one_of_ne (a b : ZMod 2) (h : a≠b) : a+b=1 := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem prepend_add (a b : ZMod 2) (x y : BinaryVector n) :
    prepend (a+b) (x+y)=prepend a x+prepend b y := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  rfl

theorem prepend_smul (c a : ZMod 2) (x : BinaryVector n) :
    prepend (c*a) (c • x)=c • prepend a x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  rfl

def equalProjection (D : BinaryCode (n+2)) : BinaryCode n where
  carrier := {x | ∃ b,prepend b x∈D}
  zero_mem' := by
    have h0 : prepend (n := n) 0 0=0 := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun k => ?_) j
      rfl
    exact ⟨0,h0.symm ▸ D.zero_mem⟩
  add_mem' := by
    rintro x y ⟨a,ha⟩ ⟨b,hb⟩
    exact ⟨a+b,prepend_add a b x y ▸ D.add_mem ha hb⟩
  smul_mem' := by
    rintro c x ⟨a,ha⟩
    exact ⟨c*a,prepend_smul c a x ▸ D.smul_mem c ha⟩

 theorem dot_add_left (x y z : BinaryVector n) : dot (x+y) z=dot x z+dot y z := by
  simp [dot,add_mul,Finset.sum_add_distrib]
 theorem dot_add_right (x y z : BinaryVector n) : dot x (y+z)=dot x y+dot x z := by
  simp [dot,mul_add,Finset.sum_add_distrib]

 theorem dot_prepend (a b : ZMod 2) (x y : BinaryVector n) :
    dot (prepend a x) (prepend b y)=dot x y := by
  simp only [dot,Fin.sum_univ_succ,prepend,Fin.cons_zero,Fin.cons_succ]
  rw [←add_assoc,add_self_zero,zero_add]

 theorem dot_prepend_arbitrary (a : ZMod 2) (x : BinaryVector n) (y : BinaryVector (n+2)) :
    dot (prepend a x) y=a*(y 0+y 1)+dot x (dropTwo y) := by
  simp only [dot,Fin.sum_univ_succ,prepend,Fin.cons_zero,Fin.cons_succ,dropTwo]
  have hi : (0 : Fin (n+1)).succ=(1 : Fin (n+2)) := by ext;simp
  rw [hi]
  ring

 theorem dot_pairWord (y : BinaryVector (n+2)) : dot (pairWord n) y=y 0+y 1 := by
  rw [pairWord,dot_prepend_arbitrary]
  simp [dot]

 theorem prepend_dropTwo (x : BinaryVector (n+2)) (h : x 0=x 1) :
    prepend (x 0) (dropTwo x)=x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases h (fun k => ?_) j
  rfl

 theorem dropTwo_mem_of_equal (D : BinaryCode (n+2)) (x : BinaryVector (n+2))
    (hx : x∈D) (he : x 0=x 1) : dropTwo x∈equalProjection D := by
  refine ⟨x 0,?_⟩
  rwa [prepend_dropTwo x he]

 theorem equalProjection_selfDual (D : BinaryCode (n+2)) (hD : SelfDual D) :
    SelfDual (equalProjection D) := by
  intro x
  constructor
  · rintro ⟨a,ha⟩ y ⟨b,hb⟩
    have hh := (hD (prepend a x)).mp ha (prepend b y) hb
    simpa only [dot_prepend] using hh
  · intro hx
    by_cases hd : pairWord n∈D
    · have he (y : BinaryVector (n+2)) (hy : y∈D) : y 0=y 1 := by
        apply (add_eq_zero_iff _ _).mp
        simpa only [dot_pairWord] using (hD (pairWord n)).mp hd y hy
      refine ⟨0,(hD _).mpr ?_⟩
      intro y hy
      rw [dot_prepend_arbitrary]
      simp only [zero_mul,zero_add]
      exact hx (dropTwo y) (dropTwo_mem_of_equal D y hy (he y hy))
    · have hz : ∃ z,z∈D ∧ dot (pairWord n) z≠0 := by
        by_contra hn
        apply hd
        apply (hD _).mpr
        intro z hz
        by_contra hh
        exact hn ⟨z,hz,hh⟩
      obtain ⟨z,hz,hzn⟩ := hz
      have hzneq : z 0≠z 1 := by
        intro he
        apply hzn
        rw [dot_pairWord,he,add_self_zero]
      have hzsum := add_eq_one_of_ne _ _ hzneq
      let b := dot x (dropTwo z)
      refine ⟨b,(hD _).mpr ?_⟩
      intro y hy
      rw [dot_prepend_arbitrary]
      by_cases he : y 0=y 1
      · rw [(add_eq_zero_iff _ _).mpr he,mul_zero,zero_add]
        exact hx (dropTwo y) (dropTwo_mem_of_equal D y hy he)
      · have hysum := add_eq_one_of_ne _ _ he
        have he' : (y+z) 0=(y+z) 1 := by
          apply (add_eq_zero_iff _ _).mp
          change (y 0+z 0)+(y 1+z 1)=0
          calc
            _ = (y 0+y 1)+(z 0+z 1) := by ring
            _ = 0 := by rw [hysum,hzsum];decide
        have H := hx (dropTwo (y+z)) (dropTwo_mem_of_equal D (y+z) (D.add_mem hy hz) he')
        have hdrop : dropTwo (y+z)=dropTwo y+dropTwo z := rfl
        rw [hdrop,dot_add_right] at H
        rw [hysum,mul_one]
        change dot x (dropTwo z)+dot x (dropTwo y)=0
        rwa [add_comm]

end
end Holant.ReedMuller.FlatNetwork
