import Holant.Certificates.NormalizedDihedralQ6.CubeAction

/-! The source's sector-zero normalization, including its bijective action on
all 48 labelled sector-one choices. Fixed-edge and complementary-edge endpoint
orders are preserved explicitly; there is no quotienting of parameter choices. -/

namespace Holant.Certificates.NormalizedDihedralQ6

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normalPort (e : Fin 6) : Port → Port :=
  ![0,1,(fixedEdge e).1,(fixedEdge e).2,(varyingEdge e).1,(varyingEdge e).2]
def normalPortInv (e : Fin 6) (i : Port) : Port :=
  if i = 0 then 0 else if i = 1 then 1
  else if i = (fixedEdge e).1 then 2 else if i = (fixedEdge e).2 then 3
  else if i = (varyingEdge e).1 then 4 else 5

def normalPerm (e : Fin 6) : Equiv.Perm Port where
  toFun := normalPort e
  invFun := normalPortInv e
  left_inv i := by fin_cases e <;> fin_cases i <;> decide
  right_inv i := by fin_cases e <;> fin_cases i <;> decide

def normalFlip (d : Sector) : Word := ![false,false,d.2.1,false,d.2.2.2,d.2.2.2 ^^ d.2.2.1]

/-- The unique sorted residual pair index; both endpoint orientations are accepted. -/
def pairIndex (p : Pair) : Fin 6 :=
  if p = (2,3) ∨ p = (3,2) then 0
  else if p = (2,4) ∨ p = (4,2) then 1
  else if p = (2,5) ∨ p = (5,2) then 2
  else if p = (3,4) ∨ p = (4,3) then 3
  else if p = (3,5) ∨ p = (5,3) then 4 else 5

def normalEdge (even odd : Fin 6) : Fin 6 :=
  pairIndex ((normalPerm even).symm (fixedEdge odd).1,(normalPerm even).symm (fixedEdge odd).2)
def originalEdge (even odd : Fin 6) : Fin 6 :=
  pairIndex (normalPerm even (fixedEdge odd).1,normalPerm even (fixedEdge odd).2)

/-- Source odd-sector parameters after the literal coordinate action. -/
def normalizeOdd (d₀ d₁ : Sector) : Sector :=
  let e := normalEdge d₀.1 d₁.1
  let fixed := fixedEdge e
  let varying := varyingEdge e
  let δ := normalFlip d₀
  (e, d₁.2.1 ^^ δ fixed.1 ^^ δ fixed.2,
    d₁.2.2.1 ^^ δ varying.1 ^^ δ varying.2,
    d₁.2.2.2 ^^ (if normalPerm d₀.1 varying.1 = (varyingEdge d₁.1).2 then d₁.2.2.1 else false) ^^ δ varying.1)

/-- Explicit inverse on labelled odd-sector choices, not an existence search. -/
def denormalizeOdd (d₀ d : Sector) : Sector :=
  let e := originalEdge d₀.1 d.1
  let fixed := fixedEdge d.1
  let varying := varyingEdge d.1
  let δ := normalFlip d₀
  let b := d.2.2.1 ^^ δ varying.1 ^^ δ varying.2
  (e,d.2.1 ^^ δ fixed.1 ^^ δ fixed.2,b,
    d.2.2.2 ^^ (if normalPerm d₀.1 varying.1 = (varyingEdge e).2 then b else false) ^^ δ varying.1)

theorem denormalize_normalize (d₀ d₁ : Sector) : denormalizeOdd d₀ (normalizeOdd d₀ d₁) = d₁ := by
  rcases d₀ with ⟨e₀,a₀,b₀,o₀⟩
  rcases d₁ with ⟨e₁,a₁,b₁,o₁⟩
  fin_cases e₀ <;> fin_cases e₁ <;>
    simp [denormalizeOdd,normalizeOdd,normalEdge,originalEdge,pairIndex,normalPerm,
      normalPort,normalPortInv,normalFlip,fixedEdge,varyingEdge,
      Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

theorem normalize_denormalize (d₀ d : Sector) : normalizeOdd d₀ (denormalizeOdd d₀ d) = d := by
  rcases d₀ with ⟨e₀,a₀,b₀,o₀⟩
  rcases d with ⟨e₁,a₁,b₁,o₁⟩
  fin_cases e₀ <;> fin_cases e₁ <;>
    simp [denormalizeOdd,normalizeOdd,normalEdge,originalEdge,pairIndex,normalPerm,
      normalPort,normalPortInv,normalFlip,fixedEdge,varyingEdge,
      Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

def normalizeOddEquiv (d₀ : Sector) : Sector ≃ Sector where
  toFun := normalizeOdd d₀
  invFun := denormalizeOdd d₀
  left_inv := denormalize_normalize d₀
  right_inv := normalize_denormalize d₀

theorem normalize_self (d : Sector) : normalizeOdd d d = standard := by
  rcases d with ⟨e,a,b,o⟩
  fin_cases e <;> simp [normalizeOdd,normalEdge,pairIndex,normalPerm,normalPortInv,
    normalPort,normalFlip,fixedEdge,varyingEdge,standard,
    Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

/-- Free fixed-edge bit after a possible orientation reversal and bit flip. -/
def fixedBitShift (d₀ d₁ : Sector) : Bool :=
  let u := (fixedEdge (normalEdge d₀.1 d₁.1)).1
  (if normalPerm d₀.1 u = (fixedEdge d₁.1).2 then d₁.2.1 else false) ^^ normalFlip d₀ u

theorem sectorWord_normalize (ε : Bool) (d₀ d₁ : Sector) (z w : Bool) :
    wordEquiv (normalPerm d₀.1) (normalFlip d₀) (sectorWord ε d₁ z w) =
      sectorWord ε (normalizeOdd d₀ d₁) z (w ^^ fixedBitShift d₀ d₁) := by
  rcases d₀ with ⟨e₀,a₀,b₀,o₀⟩
  rcases d₁ with ⟨e₁,a₁,b₁,o₁⟩
  funext i
  fin_cases e₀ <;> fin_cases e₁ <;> fin_cases i <;>
    simp [wordEquiv_apply,sectorWord,normalizeOdd,fixedBitShift,normalEdge,pairIndex,
      normalPerm,normalPortInv,normalPort,normalFlip,fixedEdge,varyingEdge,
      Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

end Holant.Certificates.NormalizedDihedralQ6
