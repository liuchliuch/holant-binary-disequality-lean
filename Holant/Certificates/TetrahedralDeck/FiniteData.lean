import Holant.Certificates.TwelveLoops.Data

/-! Exact finite original-port maps and Gaussian-integer contraction data.
Ancestor entries are scaled by4 solely for integral coefficient checking. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant.Certificates.TwelveLoops

abbrev Word := Fin 4 → Bool
abbrev SixWord := Fin 6 → Bool

def pairs : Fin 15 → Fin 6 × Fin 6 := ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def order : Fin 15 → Fin 6 → Fin 6 := ![![0,1,2,3,4,5],![0,2,1,3,4,5],![0,3,1,2,4,5],![0,4,1,2,3,5],![0,5,1,2,3,4],![1,2,0,3,4,5],![1,3,0,2,4,5],![1,4,0,2,3,5],![1,5,0,2,3,4],![2,3,0,1,4,5],![2,4,0,1,3,5],![2,5,0,1,3,4],![3,4,0,1,2,5],![3,5,0,1,2,4],![4,5,0,1,2,3]]
def inverse : Fin 15 → Fin 6 → Fin 6 := ![![0,1,2,3,4,5],![0,2,1,3,4,5],![0,2,3,1,4,5],![0,2,3,4,1,5],![0,2,3,4,5,1],![2,0,1,3,4,5],![2,0,3,1,4,5],![2,0,3,4,1,5],![2,0,3,4,5,1],![2,3,0,1,4,5],![2,3,0,4,1,5],![2,3,0,4,5,1],![2,3,4,0,1,5],![2,3,4,0,5,1],![2,3,4,5,0,1]]

theorem order_inverse : ∀ p : Fin 15, ∀ i : Fin 6, inverse p (order p i) = i := by decide
theorem inverse_order : ∀ p : Fin 15, ∀ i : Fin 6, order p (inverse p i) = i := by decide

def portOrder (p : Fin 15) : Equiv.Perm (Fin 6) where
  toFun := order p
  invFun := inverse p
  left_inv := order_inverse p
  right_inv := inverse_order p

def residual (p : Fin 15) (j : Fin 4) : Fin 6 := order p j.succ.succ

theorem pairs_complete : ∀ i j : Fin 6, i < j ↔ ∃ p : Fin 15, pairs p = (i,j) := by decide
theorem pair_ports : ∀ p : Fin 15, order p 0 = (pairs p).1 ∧ order p 1 = (pairs p).2 := by decide
theorem residual_sorted : ∀ p : Fin 15, StrictMono (residual p) := by decide
theorem residual_complement : ∀ p : Fin 15, ∀ i : Fin 6,
    (∃ j : Fin 4, residual p j = i) ↔ i ≠ (pairs p).1 ∧ i ≠ (pairs p).2 := by decide

def join (p : Fin 15) (a b : Bool) (x : Word) : SixWord :=
  fun i => ![a,b,x 0,x 1,x 2,x 3] (inverse p i)

def words : Fin 16 → Word := ![![false,false,false,false],![false,false,false,true],![false,false,true,false],![false,false,true,true],![false,true,false,false],![false,true,false,true],![false,true,true,false],![false,true,true,true],![true,false,false,false],![true,false,false,true],![true,false,true,false],![true,false,true,true],![true,true,false,false],![true,true,false,true],![true,true,true,false],![true,true,true,true]]
def signs : Fin 8 → Fin 3 → Bool := ![![false,false,false],![false,false,true],![false,true,false],![false,true,true],![true,false,false],![true,false,true],![true,true,false],![true,true,true]]

theorem words_surjective : Function.Surjective words := by decide
theorem signs_surjective : Function.Surjective signs := by decide

def survivor : Fin 3 → Fin 3 → Fin 4 := ![![0,1,3],![1,3,0],![3,0,1]]
def gzero : Gaussian := (0,0)
def gone : Gaussian := (1,0)
def gI : Gaussian := (0,1)
def gneg (z : Gaussian) : Gaussian := (-z.1,-z.2)
def gsum4 (f : Fin 4 → Gaussian) : Gaussian := gadd (f 0) (gadd (f 1) (gadd (f 2) (f 3)))

def gQ (k : Fin 4) (a b : Bool) : Gaussian :=
  ![(if a = b then gone else gzero),
    (if a = b then gzero else gI),
    (if a = b then gzero else if a then (-1,0) else gone),
    (if a = b then if a then (0,-1) else gI else gzero)] k

def gSigned (b : Bool) (z : Gaussian) : Gaussian := if b then gneg z else z

def gKernel (idx : Fin 12) : Bool → Bool → Gaussian :=
  Fin.addCases (motive := fun _ : Fin 12 => Bool → Bool → Gaussian) gQ (fun k a b => gadd (gQ 0 a b)
    (gadd (gSigned (signs k 0) (gQ 1 a b))
      (gadd (gSigned (signs k 1) (gQ 2 a b)) (gSigned (signs k 2) (gQ 3 a b))))) idx

def gP2 (U V : Bool → Bool → Gaussian) (x : Word) : Gaussian := gmul (U (x 0) (x 3)) (V (x 1) (x 2))
def gR (k : Fin 4) (x : Word) : Gaussian :=
  if k = 2 then gzero else gSigned (k != 0) (gP2 (gQ k) (gQ k) x)
def gDual (k : Fin 4) (a b : Bool) : Gaussian := gSigned (k == 1 || k == 3) (gQ k a b)
def gImages (s : Fin 3) : Fin 4 → Word → Gaussian :=
  ![gP2 (gQ 2) (gQ 2),gR (survivor s 0),gR (survivor s 1),gR (survivor s 2)]
def gAncestor (s : Fin 3) (x : SixWord) : Gaussian :=
  gsum4 (fun k => gmul (gDual k (x 0) (x 1)) (gImages s k (fun j => x j.succ.succ)))
def gCard (s : Fin 3) (p : Fin 15) (k : Fin 12) (x : Word) : Gaussian :=
  gadd (gmul (gKernel k false false) (gAncestor s (join p false false x)))
    (gadd (gmul (gKernel k false true) (gAncestor s (join p false true x)))
      (gadd (gmul (gKernel k true false) (gAncestor s (join p true false x)))
        (gmul (gKernel k true true) (gAncestor s (join p true true x)))))

def gMatch (r : Fin 3) (u v : Fin 12) (x : Word) : Gaussian :=
  ![gmul (gKernel u (x 0) (x 1)) (gKernel v (x 2) (x 3)),
    gmul (gKernel u (x 0) (x 2)) (gKernel v (x 1) (x 3)),
    gmul (gKernel u (x 0) (x 3)) (gKernel v (x 1) (x 2))] r

/-- Matching label, two literal group representatives, and an original-word pivot. -/
abbrev Certificate := Fin 3 × Fin 12 × Fin 12 × Fin 16

def numerator (s : Fin 3) (p : Fin 15) (k : Fin 12) (c : Certificate) : Gaussian :=
  gCard s p k (words c.2.2.2)
def denominator (c : Certificate) : Gaussian := gMatch c.1 c.2.1 c.2.2.1 (words c.2.2.2)

def Valid (s : Fin 3) (p : Fin 15) (k : Fin 12) (c : Certificate) : Prop :=
  numerator s p k c ≠ gzero ∧ denominator c ≠ gzero ∧
    ∀ j : Fin 16, gmul (denominator c) (gCard s p k (words j)) =
      gmul (numerator s p k c) (gMatch c.1 c.2.1 c.2.2.1 (words j))
instance (s : Fin 3) (p : Fin 15) (k : Fin 12) (c : Certificate) : Decidable (Valid s p k c) := by
  unfold Valid
  infer_instance

end Holant.Certificates.TetrahedralDeck
