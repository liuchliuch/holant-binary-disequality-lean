import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! Actual signed port names for a rank-two original support. The three
essential variables retain the original affine relation through f itself;
no XOR signature is assumed as a available physical vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoPorts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeThree codeThree_affine)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

def port (i : Fin n) : Port 3 :=
  let a := D.encode ![false,false] i
  let b := a ^^ D.encode ![true,false] i
  let c := a ^^ D.encode ![false,true] i
  if b then (if c then .inr (2,a) else .inr (0,a))
  else if c then .inr (1,a) else .inl a

theorem word_code (z : Fin 2→Bool) : word (port D) (A.codeThree z)=D.encode z := by
  funext i
  have hh := congrFun (D.affine ![true,false] ![false,true]) i
  have hx : xor (![true,false] : Fin 2→Bool) ![false,true]=![true,true] := by decide
  have ho : origin 2=(![false,false] : Fin 2→Bool) := by funext j;fin_cases j <;> rfl
  rw [hx,ho] at hh
  change D.encode ![true,true] i=
    (D.encode ![true,false] i ^^ (D.encode ![false,true] i ^^ D.encode ![false,false] i)) at hh
  have hz : z=![z 0,z 1] := by funext j;fin_cases j <;> rfl
  rw [hz]
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    cases ha : D.encode ![false,false] i <;>
    cases hb : D.encode ![true,false] i <;>
    cases hc : D.encode ![false,true] i <;>
    simp [OrdinaryNegativeSignedPortsCore.word,port,A.codeThree,ha,hb,hc,hh]

theorem port_free (j : Fin 2) : port D (D.ports j)=.inr (Fin.castLE (by decide : 2≤3) j,false) := by
  fin_cases j <;> simp [port,D.free]

/-- Full original multiplicities and signs are retained in the literal
restriction; only the semantic class test precomposes with the support code. -/
theorem essential_nonaffine (square : Affine (fun x=>f x^2)) (nonzero : f≠0) (bad : ¬Affine f) :
    ¬Affine (fun z=>f (word (port D) z)) := by
  intro h
  apply D.nonAffine_reduced square nonzero bad
  convert h.precompose A.codeThree A.codeThree_affine using 1
  funext z
  rw [word_code]
  rfl

variable (p : Fin n→Port 3)
def active (axis : Fin 2) (j : Fin 3) : Bool := decide (j.val=axis.val ∨ j=2)

def linePort (axis : Fin 2) (target : Fin 3) (i : Fin n) : Port 3 :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>if active axis j then .inr (target,s) else .inl s

def line (axis : Fin 2) (b : Bool) : Fin 2→Bool :=
  if axis=0 then ![b,false] else ![false,b]

theorem line_word (axis : Fin 2) (target : Fin 3) (z : Fin 3→Bool) :
    word (linePort p axis target) z=word p (A.codeThree (line axis (z target))) := by
  funext i
  cases h : p i with
  | inl b=>simp [linePort,OrdinaryNegativeSignedPortsCore.word,h]
  | inr t=>
      rcases t with ⟨j,s⟩
      fin_cases axis <;> fin_cases j <;> cases s <;> cases hz : z target <;>
        simp [linePort,OrdinaryNegativeSignedPortsCore.word,active,line,A.codeThree,h,hz]

theorem original_line_word (axis : Fin 2) (target : Fin 3) (z : Fin 3→Bool) :
    word (linePort (port D) axis target) z=D.encode (line axis (z target)) := by
  rw [line_word,word_code]

def lineSize (axis : Fin 2) : ℕ :=
  ∑i,match p i with
    | .inl _=>0
    | .inr (j,_)=>if active axis j then 1 else 0

theorem line_count (axis : Fin 2) (target j : Fin 3) :
    I.bundleSize (linePort p axis target) j=if target=j then lineSize p axis else 0 := by
  unfold I.bundleSize lineSize
  split_ifs with hj
  · subst j
    apply Finset.sum_congr rfl
    intro i _
    cases h : p i with
    | inl b=>simp [linePort,h]
    | inr t=>rcases t with ⟨j,s⟩;cases ha : active axis j <;> simp [linePort,h,ha]
  · apply Finset.sum_eq_zero
    intro i _
    cases h : p i with
    | inl b=>simp [linePort,h]
    | inr t=>rcases t with ⟨j,s⟩;cases ha : active axis j <;> simp [linePort,h,ha,hj]

theorem lineSize_eq (axis : Fin 2) :
    lineSize p axis=I.bundleSize p (Fin.castLE (by decide : 2≤3) axis)+I.bundleSize p 2 := by
  unfold lineSize I.bundleSize
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl b=>simp
  | inr t=>rcases t with ⟨j,s⟩;fin_cases axis <;> fin_cases j <;> simp [active]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoPorts
end
