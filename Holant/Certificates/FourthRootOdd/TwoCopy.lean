import Holant.Certificates.TwelveLoops.Gaussian
import Holant.Certificates.TwelveLoops.Contraction

/-! Literal corresponding two-X-edge contraction of two copies. Output order
is the two increasing surviving ports of the first copy, then those of the
second copy. The integer-coordinate evaluator has an exact complex bridge. -/
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

def insertPair (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) : Fin 4 → Bool :=
  fun i => Fin.cons (α := fun _ : Fin 4 => Bool) u (Fin.cons v x) ((portEquiv p).symm i)

def firstHalf (x : Fin 4 → Bool) : Fin 2 → Bool := ![x 0,x 1]
def secondHalf (x : Fin 4 → Bool) : Fin 2 → Bool := ![x 2,x 3]

def twoCopy {K : Type*} [Semiring K] (f : Signature K 4) (p : Fin 6) : Signature K 4 :=
  fun x => ∑ u : Bool, ∑ v : Bool,
    f (insertPair p u v (firstHalf x)) * f (insertPair p (!u) (!v) (secondHalf x))

def twoCopyNative {K : Type*} [Semiring K] (f : Signature K 4) (p : Fin 6) : Signature K 4 :=
  fun x => ∑ u : Bool, ∑ v : Bool, ∑ r : Bool, ∑ t : Bool,
    Signature.disequality u r * Signature.disequality v t *
    f (insertPair p u v (firstHalf x)) * f (insertPair p r t (secondHalf x))

theorem twoCopyNative_eq {K : Type*} [Semiring K] (f : Signature K 4) (p : Fin 6) :
    twoCopyNative f p=twoCopy f p := by
  funext x
  simp [twoCopyNative,twoCopy,Signature.disequality]

def exactOdd (s : State) : Signature Gaussian 4 := oddTable (a s) (b s)
def complexOdd (s : State) : Signature ℂ 4 := oddTable (fun j => embed (a s j)) (fun j => embed (b s j))

theorem embed_exactOdd (s : State) (x : Fin 4 → Bool) : embed (exactOdd s x)=complexOdd s x := by
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [exactOdd,complexOdd,oddTable,h₀,h₁,h₂,h₃,embed]

def exactTerm (s : State) (p : Fin 6) (x : Fin 4 → Bool) (u v : Bool) : Gaussian :=
  gmul (exactOdd s (insertPair p u v (firstHalf x)))
    (exactOdd s (insertPair p (!u) (!v) (secondHalf x)))

def exactTwoCopy (s : State) (p : Fin 6) (x : Fin 4 → Bool) : Gaussian :=
  gadd (gadd (exactTerm s p x false false) (exactTerm s p x false true))
    (gadd (exactTerm s p x true false) (exactTerm s p x true true))

theorem embed_exactTwoCopy (s : State) (p : Fin 6) (x : Fin 4 → Bool) :
    embed (exactTwoCopy s p x)=twoCopy (complexOdd s) p x := by
  simp [exactTwoCopy,exactTerm,embed_add,embed_mul,embed_exactOdd,twoCopy,add_comm,add_left_comm,add_assoc]

end Holant.Certificates.FourthRootOdd
