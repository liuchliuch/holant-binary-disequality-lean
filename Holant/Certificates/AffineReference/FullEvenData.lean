import Holant.Certificates.FourthRootOdd.DenseData

/-! The complete 512 normalized even-support affine tables in intrinsic
three-bit coordinates. Finite certificates use exact Gaussian integers only. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd

abbrev EvenParameters := AState × Bool × Bool × Bool

def phaseIndex (p : AState) : Fin 64 := ⟨p.1.val*16+p.2.1.val*4+p.2.2.val,by omega⟩

def phaseBit (b : Bool) : Fin 4 := if b then 1 else 0

def evenPhase (p : EvenParameters) (x : Fin 4 → Bool) : Fin 4 :=
  p.1.1*phaseBit (x 0)+p.1.2.1*phaseBit (x 1)+p.1.2.2*phaseBit (x 2)+
    signPhase p.2.1*phaseBit (x 0)*phaseBit (x 1)+
    signPhase p.2.2.1*phaseBit (x 0)*phaseBit (x 2)+
    signPhase p.2.2.2*phaseBit (x 1)*phaseBit (x 2)

def evenTable (p : EvenParameters) : Signature Gaussian 4 := fun x =>
  if evenWord x then fourthRoot (evenPhase p x) else (0,0)

def evenLoop (p : EvenParameters) (e : Fin 6) (x : Fin 2 → Bool) : Gaussian :=
  gadd (evenTable p (insertPair e false true x)) (evenTable p (insertPair e true false x))

def evenLoopPair (p : EvenParameters) (e : Fin 6) : Gaussian × Gaussian :=
  (evenLoop p e ![false,true],evenLoop p e ![true,false])

/-- Cross the selected two native X wires exactly as in source A.2(iv). -/
def crossedTerm (p : EvenParameters) (e : Fin 3) (x : Fin 4 → Bool) (u v : Bool) : Gaussian :=
  gmul (evenTable p (insertPair (initialPair e) u v (firstHalf x)))
    (evenTable p (insertPair (initialPair e) (!v) (!u) (secondHalf x)))

def crossedTable (p : EvenParameters) (e : Fin 3) (x : Fin 4 → Bool) : Gaussian :=
  gadd (gadd (crossedTerm p e x false false) (crossedTerm p e x false true))
    (gadd (crossedTerm p e x true false) (crossedTerm p e x true true))

/-- The three induced two-block matchings, including crossed external orders. -/
def blockPair : Fin 3 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3)]
def blockComplement : Fin 3 → Fin 4 × Fin 4 := ![(2,3),(1,3),(1,2)]

def equalProductTable (c : Gaussian) (r : Fin 4) (b : Fin 3) (x : Fin 4 → Bool) : Gaussian :=
  if x (blockPair b).1=x (blockPair b).2 ∧ x (blockComplement b).1=x (blockComplement b).2 then
    gmul c (gmul (if x (blockPair b).1 then fourthRoot r else (1,0))
      (if x (blockComplement b).1 then fourthRoot r else (1,0)))
  else (0,0)

inductive EvenWitness where
  | dense (u : Fin 4) (mask : Fin 16)
  | rankOne (edge : Fin 6)
  | product (edge block : Fin 3) (phase : Fin 4)
  deriving DecidableEq, Repr

def ValidEvenWitness (p : EvenParameters) : EvenWitness → Prop
  | .dense u mask => ∀ x,evenTable p x=denseTable (1,0) u mask x
  | .rankOne e => rankOneTest (evenLoopPair p e)=true
  | .product e b r => crossedTable p e (fun _ => false)≠(0,0) ∧
      ∀ x,crossedTable p e x=equalProductTable (crossedTable p e (fun _ => false)) r b x

instance (p : EvenParameters) (w : EvenWitness) : Decidable (ValidEvenWitness p w) := by
  cases w <;> unfold ValidEvenWitness <;> infer_instance

theorem full_even_parameter_count : Fintype.card EvenParameters=512 := by
  simp [EvenParameters,AState]

end Holant.Certificates.AffineReference
