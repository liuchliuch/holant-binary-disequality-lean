import Holant.Certificates.FourthRootOdd.FamilyData

namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

def wordWeight (x : Fin 4 → Bool) : ℕ :=
  (if x 0 then 1 else 0)+(if x 1 then 1 else 0)+(if x 2 then 1 else 0)+(if x 3 then 1 else 0)
def evenWord (x : Fin 4 → Bool) : Bool := !(x 0 ^^ x 1 ^^ x 2 ^^ x 3)
def maskBit (m : Fin 16) (j : Fin 4) : Bool := decide (m.val/2^(3-j.val)%2=1)
def maskSign (m : Fin 16) (x : Fin 4 → Bool) : Bool :=
  (maskBit m 0 && x 0) ^^ (maskBit m 1 && x 1) ^^
    (maskBit m 2 && x 2) ^^ (maskBit m 3 && x 3)
def gpow (z : Gaussian) : ℕ → Gaussian
  | 0 => (1,0)
  | n+1 => gmul (gpow z n) z
def denseTable (ρ : Gaussian) (u : Fin 4) (m : Fin 16) (x : Fin 4 → Bool) : Gaussian :=
  if evenWord x then
    gmul ρ (gmul (gpow (fourthRoot u) (wordWeight x/2)) (if maskSign m x then (-1,0) else (1,0)))
  else (0,0)

abbrev FamilyWitness := (Fin 6) ⊕ (Fin 3 × Fin 4 × Fin 16)
def initialPair (e : Fin 3) : Fin 6 := ⟨e.val,Nat.lt_of_lt_of_le e.isLt (by decide)⟩
def ValidFamilyWitness (p : FamilyParameters) : FamilyWitness → Prop
  | .inl e => rankOneTest (nativePair (familyState p) e)=true
  | .inr (e,u,m) =>
    exactTwoCopy (familyState p) (initialPair e) (fun _ => false)≠(0,0) ∧
      ∀ x : Fin 4 → Bool, exactTwoCopy (familyState p) (initialPair e) x=
        denseTable (exactTwoCopy (familyState p) (initialPair e) (fun _ => false)) u m x
instance (p : FamilyParameters) (w : FamilyWitness) : Decidable (ValidFamilyWitness p w) := by
  cases w with
  | inl e => exact inferInstanceAs (Decidable (_=true))
  | inr z => rcases z with ⟨e,u,m⟩; exact inferInstanceAs (Decidable (_ ∧ _))

def signIndex (x y z : Bool) : Fin 8 :=
  if x then if y then if z then 7 else 6 else if z then 5 else 4
  else if y then if z then 3 else 2 else if z then 1 else 0

end Holant.Certificates.FourthRootOdd
