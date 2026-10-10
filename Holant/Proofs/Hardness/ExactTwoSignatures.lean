import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients

/-! Literal signatures shared by the uniform EXACT2 chain and the single-cycle
reference compiler. E is an interpolation target, not a supplied q gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoSignatures
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
variable {K : Type*} [Field K]

def q : Signature K 4 := table ⟨0,1,1,1,1,1,1,0⟩
def E : Signature K 4 := table ⟨0,0,1,0,0,1,0,0⟩
def B : Signature K 4 := table ⟨0,1,0,1,1,0,1,0⟩
def spectral (t : K) : Signature K 4 := table ⟨0,t,1,t,t,1,t,0⟩

theorem spectral_linear (t : K) : spectral t=E+t • B := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [spectral,E,B,table,Pi.add_apply,Pi.smul_apply,smul_eq_mul,h0,h1,h2,h3]

theorem E_reference (x : Fin 4 → Bool) :
    E (K:=K) x=if x 0=x 2 ∧ x 1=x 3 ∧ x 0≠x 1 then 1 else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [E,table,h0,h1,h2,h3]

theorem q_self_dual (x : Fin 4 → Bool) : q (K:=K) (fun i=>!x i)=q x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [q,table,h0,h1,h2,h3]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoSignatures
