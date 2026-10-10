import Holant.Certificates.FourthRootOdd.NetworkTools
import Holant.Support
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Literal original-port wiring for the normalized equality-anchor construction
in Lemma 4.2. A word's local ports retain the order 0,1,2,3 on each supplied
vertex. The permutation only assigns those occurrences to internal ends and
ordered external ports; it does not replace or permute a vertex signature. -/
namespace Holant.EightVertex.ProductAnchor
open Holant
set_option backward.isDefEq.respectTransparency false

abbrev Word := Fin 4 → Bool

theorem weight_four (s : Word) : weight s =
    (if s 0 then 1 else 0) + (if s 1 then 1 else 0) +
      (if s 2 then 1 else 0) + (if s 3 then 1 else 0) := by
  exact Fin.sum_univ_four _

/-- Source normalized signature, with its signed complementary coefficient. -/
def normalized {K : Type*} [CommRing K] (s : Word) : Signature K 4 := fun x =>
  (if x = s then 1 else 0) + (-1 : K) ^ weight s *
    (if x = (fun i => !(s i)) then 1 else 0)

/-- The four-port equality tensor has both endpoint entries exactly one. -/
def equalityFour {K : Type*} [Zero K] [One K] : Signature K 4 := fun x =>
  if ∀ i, x i = x 0 then 1 else 0

/-- Exact raw output scalar: +1 in even weight, -1 in odd weight. -/
def outputScalar {K : Type*} [CommRing K] (s : Word) : K := (-1) ^ weight s

/-- Slots 0/1 and 2/3 are the two internal pairs; slots 4--7 are the
boundary in order. Values 0--3 belong to copy 0, values 4--7 to copy 1.
At weights 0 and 4 the table is unused, because one corolla suffices. -/
def wiringOrder (s : Word) : Fin 8 → Fin 8 :=
  match s 0, s 1, s 2, s 3 with
  | false, false, false, false => ![0,1,2,3,4,5,6,7]
  | false, false, false, true => ![3,4,5,6,0,1,2,7]
  | false, false, true, false => ![2,4,5,7,0,1,3,6]
  | false, false, true, true => ![2,4,3,5,0,1,6,7]
  | false, true, false, false => ![1,4,6,7,0,2,3,5]
  | false, true, false, true => ![1,4,3,6,0,2,5,7]
  | false, true, true, false => ![1,4,2,7,0,3,5,6]
  | false, true, true, true => ![0,5,6,7,1,2,3,4]
  | true, false, false, false => ![0,5,6,7,1,2,3,4]
  | true, false, false, true => ![0,5,3,6,1,2,4,7]
  | true, false, true, false => ![0,5,2,7,1,3,4,6]
  | true, false, true, true => ![1,4,6,7,0,2,3,5]
  | true, true, false, false => ![0,6,1,7,2,3,4,5]
  | true, true, false, true => ![2,4,5,7,0,1,3,6]
  | true, true, true, false => ![3,4,5,6,0,1,2,7]
  | true, true, true, true => ![0,1,2,3,4,5,6,7]

/-- Explicit inverse of the original-occurrence wiring table. -/
def wiringInverse (s : Word) : Fin 8 → Fin 8 :=
  match s 0, s 1, s 2, s 3 with
  | false, false, false, false => ![0,1,2,3,4,5,6,7]
  | false, false, false, true => ![4,5,6,0,1,2,3,7]
  | false, false, true, false => ![4,5,0,6,1,2,7,3]
  | false, false, true, true => ![4,5,0,2,1,3,6,7]
  | false, true, false, false => ![4,0,5,6,1,7,2,3]
  | false, true, false, true => ![4,0,5,2,1,6,3,7]
  | false, true, true, false => ![4,0,2,5,1,6,7,3]
  | false, true, true, true => ![0,4,5,6,7,1,2,3]
  | true, false, false, false => ![0,4,5,6,7,1,2,3]
  | true, false, false, true => ![0,4,5,2,6,1,3,7]
  | true, false, true, false => ![0,4,2,5,6,1,7,3]
  | true, false, true, true => ![4,0,5,6,1,7,2,3]
  | true, true, false, false => ![0,2,4,5,6,7,1,3]
  | true, true, false, true => ![4,5,0,6,1,2,7,3]
  | true, true, true, false => ![4,5,6,0,1,2,3,7]
  | true, true, true, true => ![0,1,2,3,4,5,6,7]

def wiringEquiv (s : Word) : Equiv.Perm (Fin 8) where
  toFun := wiringOrder s
  invFun := wiringInverse s
  left_inv := by
    have h : ∀ s : Word, ∀ i, wiringInverse s (wiringOrder s i) = i := by decide
    exact h s
  right_inv := by
    have h : ∀ s : Word, ∀ i, wiringOrder s (wiringInverse s i) = i := by decide
    exact h s

/-- Identify a port of either original four-port copy with its ordered slot. -/
def copyPort (v : Fin 2) (i : Fin 4) : Fin 8 :=
  Fin.cases (Fin.castAdd 4 i) (fun _ => Fin.natAdd 4 i) v

def copyPortInv (j : Fin 8) : Σ _ : Fin 2, Fin 4 :=
  ![⟨0,0⟩,⟨0,1⟩,⟨0,2⟩,⟨0,3⟩,⟨1,0⟩,⟨1,1⟩,⟨1,2⟩,⟨1,3⟩] j

/-- Two disjoint corollas, with explicit vertex indices and local port order. -/
def pairCorolla {K : Type*} (f : Signature K 4) : Network K 8 where
  shape := {
    vertices := 2
    arity := fun _ => 4
    edges := 0
    ports := {
      toFun p := .inl (copyPort p.1 p.2)
      invFun q := Sum.elim copyPortInv (fun q => Fin.elim0 q.1) q
      left_inv := by
        rintro ⟨v,i⟩
        fin_cases v <;> fin_cases i <;> rfl
      right_inv := by
        intro q
        cases q with
        | inl i => fin_cases i <;> rfl
        | inr q => exact Fin.elim0 q.1 } }
  vertex := fun _ => f
  edge := Fin.elim0

theorem pairCorolla_denote {K : Type*} [CommSemiring K] (f : Signature K 4) :
    (pairCorolla f).denote = Signature.tensor f f := by
  funext x
  dsimp [Network.denote,pairCorolla,NetworkShape.assignment]
  simp [Fin.prod_univ_succ,copyPort]
  congr 1
  congr 1
  funext i
  fin_cases i <;> rfl

end Holant.EightVertex.ProductAnchor
