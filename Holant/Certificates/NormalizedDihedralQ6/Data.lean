import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-! Literal six-port support data for manuscript Proposition A.9.
All ports use zero-based Lean indices; residual edge order is 34,35,36,45,46,56.
Projection is represented by setting deleted coordinates to zero, which retains
exactly the same information as restriction to the other four coordinates. -/
namespace Holant.Certificates.NormalizedDihedralQ6
abbrev Port := Fin 6
abbrev Word := Port → Bool
abbrev Support := Finset Word
abbrev Sector := Fin 6 × Bool × Bool × Bool
abbrev Pair := Port × Port

def fixedEdge : Fin 6 → Pair := ![(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def varyingEdge : Fin 6 → Pair := ![(4,5),(3,5),(3,4),(2,5),(2,4),(2,3)]

def sectorWord (ε : Bool) (d : Sector) (z w : Bool) : Word :=
  let e := fixedEdge d.1
  let f := varyingEdge d.1
  fun i => if i = 0 then z else if i = 1 then z ^^ ε
    else if i = e.1 then w else if i = e.2 then w ^^ d.2.1
    else if i = f.1 then d.2.2.2 ^^ z else d.2.2.2 ^^ z ^^ d.2.2.1

def sectorWords (ε : Bool) (d : Sector) : List Word :=
  [sectorWord ε d false false,sectorWord ε d false true,
   sectorWord ε d true false,sectorWord ε d true true]
def support (d₀ d₁ : Sector) : Support :=
  ((sectorWords false d₀)++(sectorWords true d₁)).toFinset

def standard : Sector := (0,false,false,false)
def canonicalSupport (d : Sector) : Support := support standard d

def parity (p : Pair) (x : Word) : Bool := x p.1 ^^ x p.2
def slice (S : Support) (p : Pair) (γ : Bool) : Support := S.filter (fun x => parity p x = γ)
def project (p : Pair) (x : Word) : Word := fun i => if i = p.1 ∨ i = p.2 then false else x i
def projected (S : Support) (p : Pair) (γ : Bool) : Support := (slice S p γ).image (project p)
def injectiveProjection (S : Support) (p : Pair) (γ : Bool) : Prop :=
  Set.InjOn (project p) (slice S p γ : Set Word)

/-- The manuscript's semantic matching-coset predicate, with no enumerated-atlas premise. -/
def matchingCoset (S : Support) : Prop :=
  ∃ π : Equiv.Perm Port, ∃ c : Fin 3 → Bool, ∀ x : Word,
    x ∈ S ↔ ∀ k : Fin 3, (x (π ⟨2*k.val,by omega⟩) ^^ x (π ⟨2*k.val+1,by omega⟩)) = c k

def pairs : List Pair :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

/-- Equality of image and domain cardinality is an exact finite injectivity checker. -/
theorem injectiveProjection_iff (S : Support) (p : Pair) (γ : Bool) :
    injectiveProjection S p γ ↔ (projected S p γ).card = (slice S p γ).card := by
  exact Finset.card_image_iff.symm

end Holant.Certificates.NormalizedDihedralQ6
