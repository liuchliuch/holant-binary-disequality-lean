import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH8Table

/-! Finite Pauli matching Gram test. Positivity forces a zero diagonal to
have a zero row and forces all nonzero diagonal entries to have the same sign.
For a product of two ordered Pauli binaries this leaves a scalar identity
matrix or vanishing two-by-two minors. This integer table is kernel checked. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramCertificate
open Holant
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def pauli (k : Fin 4) (a b : Bool) : ℤ :=
  if (a^^b)=(k=1 || k=3) then (if (k=2 || k=3) && a then -1 else 1) else 0

def word (i : Fin 4) : Fin 2→Bool :=
  ![![false,false],![false,true],![true,false],![true,true]] i

def product (p : Fin 4→Fin 4) (a b : Fin 4) (x : Fin 4→Bool) : ℤ :=
  pauli a (x (p 0)) (x (p 1))*pauli b (x (p 2)) (x (p 3))

def entry (p : Fin 4→Fin 4) (a b : Fin 4) (i j : Fin 4) : ℤ :=
  product p a b (Fin.addCases (m:=2) (n:=2) (word i) (word j))

def rowCondition (p : Fin 4→Fin 4) (a b : Fin 4) : Prop :=
  (∀i,entry p a b i i=0→∀j,entry p a b i j=0) ∧
    (∀i j,0≤entry p a b i i*entry p a b j j)

def conclusion (p : Fin 4→Fin 4) (a b : Fin 4) : Prop :=
  (∃s : Fin 2,∀i j,entry p a b i j=(if i=j then (if s=0 then 1 else -1) else 0)) ∨
    ∀i j k l,entry p a b i j*entry p a b k l=entry p a b i l*entry p a b k j

theorem certificate : ∀p : Fin 4→Fin 4,Function.Injective p→∀a b : Fin 4,
    rowCondition p a b→conclusion p a b := by
  unfold Function.Injective rowCondition conclusion
  decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramCertificate
