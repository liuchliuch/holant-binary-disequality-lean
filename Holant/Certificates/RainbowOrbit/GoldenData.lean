import Holant.Certificates.RainbowOrbit.GoldenArithmetic
import Holant.Certificates.OctahedralSeparator.GroupRepresentatives

namespace Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingProductBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def tetrahedralRaw : Fin 12 → GoldenVector :=
  ![![⟨1,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨(-1),0⟩]]

def octahedralRaw : Fin 24 → GoldenVector :=
  ![![⟨1,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨0,0⟩,⟨0,0⟩],![⟨1,0⟩,⟨0,0⟩,⟨1,0⟩,⟨0,0⟩],![⟨1,0⟩,⟨0,0⟩,⟨(-1),0⟩,⟨0,0⟩],![⟨1,0⟩,⟨0,0⟩,⟨0,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨0,0⟩,⟨0,0⟩,⟨(-1),0⟩],![⟨0,0⟩,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨0,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨1,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨(-1),0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1,0⟩,⟨1,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1,0⟩,⟨(-1),0⟩]]

def icosahedralRaw : Fin 60 → GoldenVector :=
  ![![⟨1,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1,0⟩,⟨0,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨1,0⟩,⟨(-1),0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),0⟩,⟨(-1),0⟩,⟨(-1),0⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,1⟩,⟨(-1),1⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,1⟩,⟨1,(-1)⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,(-1)⟩,⟨(-1),1⟩],![⟨0,0⟩,⟨1,0⟩,⟨0,(-1)⟩,⟨1,(-1)⟩],![⟨0,0⟩,⟨(-1),1⟩,⟨1,0⟩,⟨0,1⟩],![⟨0,0⟩,⟨1,(-1)⟩,⟨1,0⟩,⟨0,1⟩],![⟨0,0⟩,⟨(-1),1⟩,⟨1,0⟩,⟨0,(-1)⟩],![⟨0,0⟩,⟨1,(-1)⟩,⟨1,0⟩,⟨0,(-1)⟩],![⟨0,0⟩,⟨0,1⟩,⟨(-1),1⟩,⟨1,0⟩],![⟨0,0⟩,⟨0,1⟩,⟨1,(-1)⟩,⟨1,0⟩],![⟨0,0⟩,⟨0,(-1)⟩,⟨(-1),1⟩,⟨1,0⟩],![⟨0,0⟩,⟨0,(-1)⟩,⟨1,(-1)⟩,⟨1,0⟩],![⟨1,0⟩,⟨0,0⟩,⟨(-1),1⟩,⟨0,1⟩],![⟨1,0⟩,⟨0,0⟩,⟨1,(-1)⟩,⟨0,1⟩],![⟨1,0⟩,⟨0,0⟩,⟨(-1),1⟩,⟨0,(-1)⟩],![⟨1,0⟩,⟨0,0⟩,⟨1,(-1)⟩,⟨0,(-1)⟩],![⟨0,1⟩,⟨0,0⟩,⟨1,0⟩,⟨(-1),1⟩],![⟨0,1⟩,⟨0,0⟩,⟨1,0⟩,⟨1,(-1)⟩],![⟨0,(-1)⟩,⟨0,0⟩,⟨1,0⟩,⟨(-1),1⟩],![⟨0,(-1)⟩,⟨0,0⟩,⟨1,0⟩,⟨1,(-1)⟩],![⟨(-1),1⟩,⟨0,0⟩,⟨0,1⟩,⟨1,0⟩],![⟨1,(-1)⟩,⟨0,0⟩,⟨0,1⟩,⟨1,0⟩],![⟨(-1),1⟩,⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩],![⟨1,(-1)⟩,⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩],![⟨1,0⟩,⟨0,1⟩,⟨0,0⟩,⟨(-1),1⟩],![⟨1,0⟩,⟨0,1⟩,⟨0,0⟩,⟨1,(-1)⟩],![⟨1,0⟩,⟨0,(-1)⟩,⟨0,0⟩,⟨(-1),1⟩],![⟨1,0⟩,⟨0,(-1)⟩,⟨0,0⟩,⟨1,(-1)⟩],![⟨(-1),1⟩,⟨1,0⟩,⟨0,0⟩,⟨0,1⟩],![⟨1,(-1)⟩,⟨1,0⟩,⟨0,0⟩,⟨0,1⟩],![⟨(-1),1⟩,⟨1,0⟩,⟨0,0⟩,⟨0,(-1)⟩],![⟨1,(-1)⟩,⟨1,0⟩,⟨0,0⟩,⟨0,(-1)⟩],![⟨0,1⟩,⟨(-1),1⟩,⟨0,0⟩,⟨1,0⟩],![⟨0,1⟩,⟨1,(-1)⟩,⟨0,0⟩,⟨1,0⟩],![⟨0,(-1)⟩,⟨(-1),1⟩,⟨0,0⟩,⟨1,0⟩],![⟨0,(-1)⟩,⟨1,(-1)⟩,⟨0,0⟩,⟨1,0⟩],![⟨1,0⟩,⟨(-1),1⟩,⟨0,1⟩,⟨0,0⟩],![⟨1,0⟩,⟨1,(-1)⟩,⟨0,1⟩,⟨0,0⟩],![⟨1,0⟩,⟨(-1),1⟩,⟨0,(-1)⟩,⟨0,0⟩],![⟨1,0⟩,⟨1,(-1)⟩,⟨0,(-1)⟩,⟨0,0⟩],![⟨0,1⟩,⟨1,0⟩,⟨(-1),1⟩,⟨0,0⟩],![⟨0,1⟩,⟨1,0⟩,⟨1,(-1)⟩,⟨0,0⟩],![⟨0,(-1)⟩,⟨1,0⟩,⟨(-1),1⟩,⟨0,0⟩],![⟨0,(-1)⟩,⟨1,0⟩,⟨1,(-1)⟩,⟨0,0⟩],![⟨(-1),1⟩,⟨0,1⟩,⟨1,0⟩,⟨0,0⟩],![⟨1,(-1)⟩,⟨0,1⟩,⟨1,0⟩,⟨0,0⟩],![⟨(-1),1⟩,⟨0,(-1)⟩,⟨1,0⟩,⟨0,0⟩],![⟨1,(-1)⟩,⟨0,(-1)⟩,⟨1,0⟩,⟨0,0⟩]]

def evenPermutation : Fin 12 → Equiv.Perm (Fin 4) :=
  ![{toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![0,2,3,1], invFun := ![0,3,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![1,0,3,2], invFun := ![1,0,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![1,2,0,3], invFun := ![2,0,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![2,0,1,3], invFun := ![1,2,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![2,1,3,0], invFun := ![3,1,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![2,3,0,1], invFun := ![2,3,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![3,0,2,1], invFun := ![1,3,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel},{toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel}]

def goldenSign (b : Bool) : ℤ := if b then -1 else 1

def sourceGolden (ε : Fin 3 → Bool) : GoldenVector :=
  ![⟨0,0⟩,⟨goldenSign (ε 0),0⟩,⟨0,goldenSign (ε 1)⟩,
    ⟨-goldenSign (ε 2),goldenSign (ε 2)⟩]

def permutedGolden (p : Fin 12) (ε : Fin 3 → Bool) : GoldenVector :=
  fun i => sourceGolden ε ((evenPermutation p).symm i)

theorem evenPermutation_sign : ∀ p : Fin 12, Equiv.Perm.sign (evenPermutation p) = 1 := by
  decide +kernel

theorem evenPermutation_complete : ∀ π : Equiv.Perm (Fin 4),
    Equiv.Perm.sign π = 1 → ∃ p : Fin 12, π = evenPermutation p := by
  decide +kernel

theorem tetrahedralRaw_description : ∀ k : Fin 12,
    (∃ i : Fin 4, tetrahedralRaw k = fun j => if j=i then GoldenInt.ofInt 1 else GoldenInt.zero) ∨
    ∃ ε : Fin 3 → Bool, tetrahedralRaw k =
      ![GoldenInt.ofInt 1,GoldenInt.ofInt (goldenSign (ε 0)),
        GoldenInt.ofInt (goldenSign (ε 1)),GoldenInt.ofInt (goldenSign (ε 2))] := by
  decide +kernel

theorem tetrahedralRaw_covers_axes : ∀ i : Fin 4, ∃ k : Fin 12,
    tetrahedralRaw k = fun j => if j=i then GoldenInt.ofInt 1 else GoldenInt.zero := by
  decide +kernel

theorem tetrahedralRaw_covers_signs : ∀ ε : Fin 3 → Bool, ∃ k : Fin 12,
    tetrahedralRaw k = ![GoldenInt.ofInt 1,GoldenInt.ofInt (goldenSign (ε 0)),
      GoldenInt.ofInt (goldenSign (ε 1)),GoldenInt.ofInt (goldenSign (ε 2))] := by
  decide +kernel

theorem icosahedralRaw_description : ∀ k : Fin 60,
    (∃ i : Fin 12, icosahedralRaw k = tetrahedralRaw i) ∨
    ∃ p : Fin 12, ∃ ε : Fin 3 → Bool, icosahedralRaw k = permutedGolden p ε := by
  decide +kernel

theorem icosahedralRaw_covers_tetrahedral : ∀ i : Fin 12, ∃ k : Fin 60,
    icosahedralRaw k = tetrahedralRaw i := by decide +kernel

theorem icosahedralRaw_covers_golden : ∀ p : Fin 12, ∀ ε : Fin 3 → Bool,
    ∃ k : Fin 60, ∃ c : ℤ, (c=1 ∨ c = -1) ∧
      permutedGolden p ε = goldenScale c (icosahedralRaw k) := by
  intro p ε
  have h : ∀ p : Fin 12, ∀ ε : Fin 3 → Bool,
      ∃ k : Fin 60, ∃ b : Bool,
        permutedGolden p ε = goldenScale (goldenSign b) (icosahedralRaw k) := by
    decide +kernel
  obtain ⟨k,b,hk⟩ := h p ε
  refine ⟨k,goldenSign b,?_,hk⟩
  cases b <;> simp [goldenSign]

end Holant.Certificates.RainbowOrbit
