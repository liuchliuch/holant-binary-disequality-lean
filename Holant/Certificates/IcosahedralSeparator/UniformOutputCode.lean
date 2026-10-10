import Holant.Certificates.IcosahedralSeparator.TensorCode
import Holant.Certificates.IcosahedralSeparator.UniformDeterminants

/-! Literal integral encodings of the thirty fixed-kernel outputs and their
first-two-port subsequent contractions. Each output encoding has scalar8. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def phiCode : GScalar:=greal ⟨0,1⟩
def tauCode : GScalar:=greal ⟨-1,1⟩
def uniformCode (i : Fin 30) (x : Fin 4→Bool) : GScalar:=
  gadd (gsub (gmul phiCode (regularCode (ordering i 0) x))
    (gmul tauCode (regularCode (ordering i 1) x))) (regularCode (ordering i 2) x)

def subsequentCode (a b : Bool) : GScalar:=
  if a=b then (GoldenInt.ofInt 1,if a then ⟨1,-1⟩ else ⟨-1,1⟩)
  else (GoldenInt.zero,⟨-2,1⟩)

def binaryCode (i : Fin 30) (a b : Bool) : GScalar:=
  gadd (gadd (gmul (subsequentCode false false) (uniformCode i ![false,false,a,b]))
    (gmul (subsequentCode false true) (uniformCode i ![false,true,a,b])))
    (gadd (gmul (subsequentCode true false) (uniformCode i ![true,false,a,b]))
    (gmul (subsequentCode true true) (uniformCode i ![true,true,a,b])))

def transferCode (i : Fin 30) (a b : Bool) : GScalar:=binaryCode i a (!b)

def flatCode (i : Fin 30) (k : Fin 3) (a b : Bool×Bool) : GScalar:=
  if k=0 then uniformCode i ![a.1,a.2,b.1,b.2]
  else if k=1 then uniformCode i ![a.1,b.1,a.2,b.2]
  else uniformCode i ![a.1,b.1,b.2,a.2]

def groupCode (i : Fin 60) (a b : Bool) : GScalar:=
  let v:=icosahedralRaw i
  if a=b then (v 0,if a then GoldenInt.neg (v 3) else v 3)
  else (if a then GoldenInt.neg (v 2) else v 2,v 1)

noncomputable section
@[simp] theorem gembed_phi : gembed phiCode=(goldenRatio : ℂ) := by simp [phiCode,GoldenInt.eval]
@[simp] theorem gembed_tau : gembed tauCode=(goldenReciprocal : ℂ) := by
  simp [tauCode,GoldenInt.eval,GoldenInt.reciprocal_eq]
  ring

 theorem gembed_uniformCode (i : Fin 30) (x : Fin 4→Bool) :
    gembed (uniformCode i x)=8*uniformOutput i x := by
  simp [uniformCode,gembed_regularCode,uniformOutput,Pi.smul_apply,smul_eq_mul]
  ring

 theorem gembed_subsequentCode (a b : Bool) :
    gembed (subsequentCode a b)=subsequentKernel a b := by
  cases a <;> cases b <;>
    simp [subsequentCode,gembed,subsequentKernel,Q0,Q1,Q3,Signature.equality,
      GoldenInt.eval,GoldenInt.zero,GoldenInt.ofInt,GoldenInt.reciprocal_eq]
  all_goals push_cast
  all_goals have h : (goldenRatio : ℂ)^2=goldenRatio+1 := by exact_mod_cast GoldenInt.golden_sq
  all_goals ring_nf
  all_goals try rw [h]
  all_goals ring

 def subsequentOutput (i : Fin 30) : Binary:=
  fun a b=>Signature.contract subsequentKernel (uniformOutput i) ![a,b]

 theorem gembed_binaryCode (i : Fin 30) (a b : Bool) :
    gembed (binaryCode i a b)=8*subsequentOutput i a b := by
  have hj (c d : Bool) : (![c,d,a,b] : Fin 4→Bool)=Fin.cons c (Fin.cons d ![a,b]) := by
    funext j
    fin_cases j <;> rfl
  simp only [binaryCode,gembed_add,gembed_mul,gembed_subsequentCode,gembed_uniformCode,
    subsequentOutput,Signature.contract,Fintype.sum_bool,hj]
  ring

 theorem gembed_transferCode (i : Fin 30) (a b : Bool) :
    gembed (transferCode i a b)=8*Kernel.mul (subsequentOutput i) Signature.disequality a b := by
  rw [transferCode,gembed_binaryCode]
  cases a <;> cases b <;> simp [Kernel.mul_apply,Signature.disequality]

 theorem gembed_flatCode (i : Fin 30) (k : Fin 3) (a b : Bool×Bool) :
    gembed (flatCode i k a b)=8*flatten k (uniformOutput i) a b := by
  fin_cases k <;> simp [flatCode,flatten,flatten0,flatten1,flatten2,gembed_uniformCode]

 theorem gembed_groupCode (i : Fin 60) (a b : Bool) :
    gembed (groupCode i a b)=representative .icosahedral i a b := by
  cases a <;> cases b <;>
    simp [groupCode,gembed,representative,raw,goldenMatrix,quaternion,quaternionBasis,
      Q0,Q1,Q2,Q3,Signature.equality,Fin.sum_univ_succ] <;> ring

end
end Holant.Certificates.IcosahedralSeparator
