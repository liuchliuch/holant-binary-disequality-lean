import Holant.ReedMuller.TwoChart.AlgebraicNetwork

/-! Input-coordinate complementation absorbs the native X edges used to
insert the original signature. The complement is a translation of the actual
character-flat tensor, not a change of its boundary ordering. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open Holant.Tractable.AffinePhase
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

theorem nonzeroFlat_shiftWord (f : Signature ℂ n) (hf : NonzeroFlat f)
    (t : BinaryVector n) : NonzeroFlat (fun x => f (GenerationNetwork.shiftWord t x)) := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  refine ⟨Units.mk0 ((c:ℂ)*sign (ell (-t)))
    (mul_ne_zero c.ne_zero (sign_nonzero _)),a+t,D,ell,hD,?_⟩
  funext x
  simp only [signature,value,GenerationNetwork.vector_shiftWord,Units.val_mk0]
  have hs : vectorWord x-t-a=vectorWord x-(a+t) := by abel
  rw [hs]
  split_ifs
  · rw [map_sub,map_neg,sub_eq_add_neg,sign_add]
    ring
  · rfl

/-- Complement precisely the first n coordinates; the final m coordinates
and their order are unchanged. -/
def complementInputs (x : Word (n+m)) : Word (n+m) :=
  GenerationNetwork.shiftWord (Fin.addCases (fun _ : Fin n => 1) (fun _ : Fin m => 0)) x

@[simp] theorem complementInputs_join (x : Word n) (b : Word m) :
    complementInputs (Fin.addCases x b)=Fin.addCases (fun i => !(x i)) b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [complementInputs,GenerationNetwork.shiftWord]

@[simp] theorem complementInputs_involutive (x : Word (n+m)) :
    complementInputs (complementInputs (n:=n) (m:=m) x)=x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [complementInputs,GenerationNetwork.shiftWord]

theorem nonzeroFlat_complementInputs (f : Signature ℂ (n+m)) (hf : NonzeroFlat f) :
    NonzeroFlat (fun x => f (complementInputs (n:=n) (m:=m) x)) :=
  nonzeroFlat_shiftWord f hf _

theorem CFlat_complementInputs (f : Signature ℂ (n+m)) (hf : CFlat f) :
    CFlat (fun x => f (complementInputs (n:=n) (m:=m) x)) := by
  rcases hf with rfl|hf
  · exact Or.inl rfl
  · exact Or.inr (nonzeroFlat_complementInputs f hf)

def complementWordEquiv (n : ℕ) : Word n ≃ Word n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i;simp
  right_inv x := by funext i;simp

/-- Exact partial contraction after complementing the context's input ports.
The left vertex is the original tensor, with its original ordered ports. -/
theorem withInput_complement_denote {K : Type*} [CommSemiring K]
    (g : Signature K n) (C : Signature K (n+m)) (R : Network K (n+m))
    (s : K) (hR : ∀x,R.denote x=s*C (complementInputs (n:=n) (m:=m) x))
    (b : Word m) :
    (NetworkPlug.withInput g R).denote b=s*∑x : Word n,g x*C (Fin.addCases x b) := by
  rw [NetworkPlug.withInput_denote]
  simp only [hR,complementInputs_join]
  rw [←(complementWordEquiv n).sum_comp]
  simp only [complementWordEquiv,Equiv.coe_fn_mk,Bool.not_not]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end Holant.ReedMuller.TwoChart
